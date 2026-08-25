import Lax3Proofs.SolveAugBaseFrame
import Lax3Proofs.SolveAugOrient

set_option autoImplicit false

/-!
# F6c12-5a-iii — the symmetrization's merge, as IMP+ text

`SolveAugCompose` §5 split the augmentation's symmetrization into the
transpose-and-merge residual `AugSymCsrIn` and the landed build
`bldAdjCom` (`augSymIn_of_symCsr_build`).  This file discharges the
residual: **`AugSymCsrIn` is met by a concrete `Com` at a concrete
budget**, leaving a `GraphCsr` of `(selChain sel A.G R).toGraph` in the
fresh pair `(soO j, stO j)`.

## What the program is

Five sweeps of the carrier and its slots, of which the middle three are
the landed transpose:

* `syZeroCom` clears the counting sort's degree cells;
* `tpCom` (`SolveAugEmitCom`, discharged as `transposeIn_tpCom`) turns
  the in-neighbour CSR `(io, it)` of `D` into an out-neighbour CSR
  `(qo, qt)` — `OutCsrAt`, offsets `outOff D`;
* `syMergeCom` walks the carrier once, and for each vertex `v` stores
  the merged offset and then copies row `v` of `(io, it)` and row `v` of
  `(qo, qt)` end to end into `stO` at a running cursor.

The merged offsets are the **pointwise sum** `off i + outOff D i`
(`symOff`), which is `SolveAugBaseFrame`'s `toGraph_step_add` read at
the two input CSRs: no prefix scan is needed, and the cursor of the
single emit sweep *is* the offset, so `soO j` is filled by one store per
vertex from the cursor the sweep already carries.

## The exact-length requirement, and how it is met

`AugSymCsrIn`'s postcondition is a bare `GraphCsr`, whose `Lib.Csr`
clauses are array **equalities** (`σ.arrs o = arrOf (N+1) off`).  IMP+
`store` is `List.set`, so no run changes a length
(`graphCsr_pre_lengths`): the pass must be *handed* `soO j` at exactly
`A.N + 1` cells and `stO j` at exactly `2·arcCount D`.  The windowed `≥`
allocations the arena and the scratch descriptors supply are not enough.

That requirement is met exactly as `SolveAugBaseFrame` §3 says it can
be, and no landed residual is restated to ease it: `augStInN`'s own
`nA` cell holds `arcCount D` and the arena's `nN` holds `A.N`, so
`symCsrSizes` states both lengths in terms of `σ` alone, and
`symCsrSizes_exact` turns it into the two exact figures.  The
discharge below therefore asks its caller for `symCsrSizes` (through
the rounds' descriptor `Srd`, which is a parameter of `AugSymCsrIn`)
and for nothing else about `soO`/`stO`.

The slot count clause `ns ≤ 2·arcCount D` is met by
`symCsr_ns_le` — for a `GraphCsr` of `D.toGraph` it is an equality
(`symCsr_ns_eq`), so nothing is spent there.

## The budget

`symK N a = 90·N + 80·a + 60` at `a = arcCount D`: the zero sweep `11`
a vertex, `tpCom`'s own `41·N + 40·a + 30`, the merge sweep `35` a
vertex and `36` an arc (`18` per emitted slot, two slots per arc), plus
the fixed blocks.  `O(N + arcCount D)`, no `N²`.

Through `augSymIn_of_symCsr_build` this becomes `augSymBudget` at
`(171, 196, 84)`, against `augChainCost_le_selChainCharge`'s
coefficient bounds `sn ≤ 3·k`, `sa ≤ 5·k` at the base passes' `k = 475`
— i.e. `171 ≤ 1425` and `196 ≤ 2375`, with the whole of the slack to
spare.

## Findings

1. **The merge needs no figure cell of its own.**  Its extent is the
   cursor it ends at, so `nSy` is written from `sy.c` and never
   computed: `2·arcCount D` is a value the sweep has already produced.
   The carrier is the arena's `nN`, read by each of the three sweeps'
   scans and by nothing else, exactly as `TransposeIn` reads it (that
   pass's Finding 1).  No array length is read anywhere
   (`Imp.lean:158`).
2. **The two copies are one command.**  Row `v` of the in-CSR and row
   `v` of the transpose are copied by the *same* `syCopyCom o t st` at
   two instantiations; the specification is stated against a bare
   reading contract (offsets at `o`, targets at `t`) rather than
   against `InNCsr` or `OutCsrAt`, so neither shape enters the loop
   proof.
3. **`InNCsr` is `TrInCsr` at exact lengths.**  `tpCom`'s contract is
   stated at the windowed `TrInCsr` while the orientation region
   `augStInN` carries the exact-length `InNCsr`; `trInCsr_of_inNCsr`
   below is the bridge, and its only non-mechanical clause is `inj`,
   which is the rows' `Nodup` read as injectivity of the slot map.
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.Augmentation (Orientation)
open Lax3Proofs.Augmentation.Orientation (toGraph orients_toGraph)
open Lax3Proofs.CoverRoutine (MinDegSel selChain)
open Lax3Proofs.TgtCoupling (outNbrs mem_outNbrs)

/-! ## §0 Small helpers

The array and evaluation shapes the straight-line blocks are built
from.  `SolveAugEmitCom` §0 has the same list, `private` there. -/

private theorem sy_getD_set_self {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem sy_getD_set_of_ne {l : List ℕ} {i q c : ℕ} (h : i ≠ q) :
    (l.set i c).getD q 0 = l.getD q 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

/-- Reading below a truncation is reading the array. -/
private theorem sy_getD_take {l : List ℕ} {m i : ℕ} (h : i < m) :
    (l.take m).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

private theorem sy_getElem?_of_lt (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem sy_evB_var {B : ℕ} {y : String} {σ : Env} {c : ℕ} (hy : σ.vars y = c)
    (hc : c < B) : (Expr.var y).evalB B σ = some c := by
  rw [← hy] at hc ⊢; exact evalB_var hc

private theorem sy_evB_lit {B c : ℕ} {σ : Env} (hc : c < B) :
    (Expr.lit c).evalB B σ = some c := evalB_lit hc

private theorem sy_evB_add {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (hab : a + b < B) :
    (Expr.add e f).evalB B σ = some (a + b) := evalB_bin he hf (by simpa using hab)

private theorem sy_evB_get {B : ℕ} {a : String} {i : Expr} {σ : Env} {q c : ℕ}
    (hi : i.evalB B σ = some q) (hq : (σ.arrs a)[q]? = some c) (hc : c < B) :
    (Expr.get a i).evalB B σ = some c := evalB_get hi hq hc

private theorem sy_run_assign {B : ℕ} {x : String} {e : Expr} {σ : Env} {c K : ℕ}
    (he : e.evalB B σ = some c) (hK : 1 + e.size ≤ K) :
    Run B (.assign x e) σ (σ.setVar x c) K := (Run.assign he).mono hK

private theorem sy_run_store {B : ℕ} {a : String} {i e : Expr} {σ : Env} {q c K : ℕ}
    (hi : i.evalB B σ = some q) (he : e.evalB B σ = some c)
    (hq : q < (σ.arrs a).length) (hK : 1 + i.size + e.size ≤ K) :
    Run B (.store a i e) σ (σ.setArr a q c) K := (Run.store hi he hq).mono hK

/-- Two arrays of the same length agreeing cell by cell are equal, in
the `arrOf` spelling `Lib.Csr` states its two clauses in. -/
theorem arrOf_congr {m : ℕ} {f g : ℕ → ℕ} (h : ∀ i, i < m → f i = g i) :
    arrOf m f = arrOf m g := by
  simp only [arrOf]
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

/-- A neighbourhood is a set of vertices, so it has at most `N` of
them — the bound that makes the symmetrized slot count a word. -/
theorem ncard_neighborSet_le_card {N : ℕ} (G : SimpleGraph (Fin N)) (v : Fin N) :
    (G.neighborSet v).ncard ≤ N := by
  classical
  calc (G.neighborSet v).ncard ≤ (Set.univ : Set (Fin N)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = N := by simp [Set.ncard_univ]

/-- **Twice the arc count is at most `N²`.** Every vertex has fewer
than `N + 1` neighbours and the degree sum is `2·arcCount`
(`slotCount_toGraph_eq_two_mul_arcCount`), so the figure the merge
produces is a word as soon as `N²` is. -/
theorem two_mul_arcCount_le_sq_orient {N : ℕ} (D : Orientation N) :
    2 * arcCount D ≤ N * N := by
  classical
  rw [← slotCount_toGraph_eq_two_mul_arcCount D, slotCount]
  calc ∑ v : Fin N, (D.toGraph.neighborSet v).ncard
      ≤ ∑ _v : Fin N, N :=
        Finset.sum_le_sum fun v _ => ncard_neighborSet_le_card D.toGraph v
    _ = N * N := by simp

/-! ## §1 The two inputs, as one reading contract

The merge copies row `v` of the in-neighbour CSR and then row `v` of
the transpose, with the *same* command.  Neither `InNCsr` nor
`OutCsrAt` enters the loop proof: both are read into the bare contract
below, which is everything a copy needs — the offsets, the targets, and
that the offsets do not decrease. -/

/-- **What a row copy reads**: `o` holds the offsets up to `n`, `t` the
targets below the extent `off n`, the offsets are nondecreasing and
every target is a vertex. -/
structure SymSrc (o t : String) (n : ℕ) (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  /-- Reading an offset. -/
  offGet : ∀ i, i ≤ n → (σ.arrs o)[i]? = some (off i)
  /-- Reading a target. -/
  tgtGet : ∀ p, p < off n → (σ.arrs t)[p]? = some (tgt p)
  /-- The offsets do not decrease. -/
  mono : ∀ i, i < n → off i ≤ off (i + 1)
  /-- Every target is a vertex. -/
  tgtLt : ∀ p, p < off n → tgt p < n

namespace SymSrc

variable {o t : String} {n : ℕ} {off tgt : ℕ → ℕ} {σ : Env}

/-- The contract reads two arrays and nothing else. -/
theorem of_eq (h : SymSrc o t n off tgt σ) {σ' : Env} (ho : σ'.arrs o = σ.arrs o)
    (ht : σ'.arrs t = σ.arrs t) : SymSrc o t n off tgt σ' where
  offGet := by rw [ho]; exact h.offGet
  tgtGet := by rw [ht]; exact h.tgtGet
  mono := h.mono
  tgtLt := h.tgtLt

/-- The offsets do not decrease, over a range. -/
theorem le (h : SymSrc o t n off tgt σ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    off a ≤ off b := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            exact le_rfl
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (h.mono b (by omega))
      · obtain rfl : a = b + 1 := by omega
        exact le_rfl

end SymSrc

/-- **The in-neighbour CSR is a reading contract.** -/
theorem symSrc_of_trInCsr {o t : String} {n ns : ℕ} {D : Orientation n}
    {off tgt : ℕ → ℕ} {σ : Env} (h : TrInCsr o t D ns off tgt σ) :
    SymSrc o t n off tgt σ where
  offGet := h.offGet
  tgtGet := fun p hp => h.tgtGet p (by rw [← h.last]; exact hp)
  mono := fun i hi => by
    have := h.step ⟨i, hi⟩
    simp only at this
    omega
  tgtLt := fun p hp => h.tgtLt p (by rw [← h.last]; exact hp)

/-- **The transpose's output is a reading contract.** -/
theorem symSrc_of_outCsrAt {qo qt : String} {n : ℕ} {D : Orientation n}
    {otF : ℕ → ℕ} {σ : Env} (h : OutCsrAt qo qt D otF σ) :
    SymSrc qo qt n (outOff D) otF σ where
  offGet := h.qoGet
  tgtGet := fun p hp => h.qtGet p (by rwa [outOff_last] at hp)
  mono := fun i _ => outOff_le_succ D i
  tgtLt := fun p hp => h.qtLt p (by rwa [outOff_last] at hp)

/-! ## §2 The merged offsets

`toGraph_step_add` (`SolveAugBaseFrame` §3): the offsets of a CSR of
`D.toGraph` are the **pointwise sum** of the input CSR's and the
transpose's, so the merge needs no prefix scan — the cursor of its one
emit sweep is the offset, and one store per vertex writes it. -/

/-- The merged offset function. -/
noncomputable def symOff {N : ℕ} (off : ℕ → ℕ) (D : Orientation N) (i : ℕ) : ℕ :=
  off i + outOff D i

/-- The merged offsets are anchored. -/
theorem symOff_zero {N : ℕ} {off : ℕ → ℕ} (D : Orientation N) (h : off 0 = 0) :
    symOff off D 0 = 0 := by
  rw [symOff, h, outOff_zero]

/-- **The merged extent is twice the arc count** — the equality
`symCsr_ns_eq` asks the merge to produce, from the two inputs' own
extents. -/
theorem symOff_last {N : ℕ} {off : ℕ → ℕ} (D : Orientation N)
    (h : off N = arcCount D) : symOff off D N = 2 * arcCount D := by
  rw [symOff, h, outOff_last]; ring

/-- **The merged offsets step by the degrees of `D.toGraph`** —
`toGraph_step_add`, read at the in-CSR's own offset function and the
transpose's.  This is why one addition and one store a vertex is the
whole offset pass: row `v` of the merge is exactly `v`'s neighbourhood,
so the pointwise sum *is* the CSR's offset function.  §6's loop works
with the equivalent sum form `symOff_succ_eq`, which splits the row at
the seam the two copies meet at. -/
theorem symOff_step {N : ℕ} {off : ℕ → ℕ} {D : Orientation N}
    (hi : ∀ v : Fin N, off ((v : ℕ) + 1) = off (v : ℕ) + (D.inN v).card) (v : Fin N) :
    symOff off D ((v : ℕ) + 1)
      = symOff off D (v : ℕ) + (D.toGraph.neighborSet v).ncard :=
  toGraph_step_add D off (outOff D) hi
    (fun w => by rw [outOff_succ, outDegAt_coe]) v

/-- The merged offsets do not decrease. -/
theorem symOff_le {N : ℕ} {off : ℕ → ℕ} {D : Orientation N} {a b : ℕ}
    (hoff : ∀ i, i < N → off i ≤ off (i + 1)) (hab : a ≤ b) (hb : b ≤ N) :
    symOff off D a ≤ symOff off D b := by
  have hmono : ∀ c, c ≤ N → ∀ d, d ≤ c → off d ≤ off c := by
    intro c
    induction c with
    | zero =>
        intro _ d hd
        obtain rfl : d = 0 := by omega
        exact le_rfl
    | succ c ih =>
        intro hc d hd
        rcases Nat.lt_or_ge d (c + 1) with hlt | hge
        · exact le_trans (ih (by omega) d (by omega)) (hoff c (by omega))
        · obtain rfl : d = c + 1 := by omega
          exact le_rfl
  have h1 : off a ≤ off b := hmono b hb a hab
  have h2 : outOff D a ≤ outOff D b := outOff_mono D hab
  simp only [symOff]
  omega

/-! ## §3 The bridge: an exact-length `InNCsr` is the windowed `TrInCsr`

`tpCom`'s contract (`TransposeIn`) is stated at `TrInCsr`, whose two
length clauses are `≤`; the orientation region `augStInN` carries the
exact-length `InNCsr`.  Every other clause is the same clause, and
`inj` is the rows' `Nodup` read as injectivity of the slot map. -/

/-- **An `InNCsr` is a `TrInCsr`**, at its own offset and target
functions. -/
theorem trInCsr_of_inNCsr {o t : String} {n ns : ℕ} {D : Orientation n} {σ : Env}
    (h : InNCsr o t D ns σ) : ∃ off tgt : ℕ → ℕ, TrInCsr o t D ns off tgt σ := by
  classical
  obtain ⟨off, tgt, hc, h0, hnd, hR⟩ := h
  have hstep : ∀ v : Fin n, off ((v : ℕ) + 1) = off (v : ℕ) + (D.inN v).card := by
    intro v
    have hlen : (Csr.row off tgt (v : ℕ)).length = (D.inN v).card :=
      length_eq_card_of_rows hnd hR v
    rw [Csr.length_row, Csr.rowLen] at hlen
    have hmono : off (v : ℕ) ≤ off ((v : ℕ) + 1) := hc.off_le_succ v.isLt
    omega
  refine ⟨off, tgt, ?_⟩
  refine
    { zero := h0
      step := hstep
      last := hc.last
      offLen := le_of_eq hc.length_off.symm
      tgtLen := le_of_eq hc.length_tgt.symm
      offGet := fun i hi => by
        rw [sy_getElem?_of_lt _ _ (by rw [hc.length_off]; omega), hc.getD_off hi]
      tgtGet := fun p hp => by
        rw [sy_getElem?_of_lt _ _ (by rw [hc.length_tgt]; omega), hc.getD_tgt hp]
      tgtLt := fun p hp => hc.target hp
      sound := ?_
      complete := ?_
      inj := ?_ }
  · intro v p hp1 hp2 hlt
    obtain ⟨hu, hmem⟩ := (hR v (tgt p)).1 (mem_row_iff.2 ⟨p, hp1, hp2, rfl⟩)
    exact hmem
  · intro v u hu
    exact mem_row_iff.1 ((hR v (u : ℕ)).2 ⟨u.isLt, by simpa using hu⟩)
  · intro v p r hp1 hp2 hr1 hr2 hpr
    have hnodup : ((List.range (Csr.rowLen off (v : ℕ))).map
        (fun k => tgt (off (v : ℕ) + k))).Nodup := by
      have := hnd v
      rwa [Csr.row, arrOf] at this
    have hkey := List.inj_on_of_nodup_map hnodup
      (List.mem_range.2 (show p - off (v : ℕ) < Csr.rowLen off (v : ℕ) by
        rw [Csr.rowLen]; omega))
      (List.mem_range.2 (show r - off (v : ℕ) < Csr.rowLen off (v : ℕ) by
        rw [Csr.rowLen]; omega))
      (show tgt (off (v : ℕ) + (p - off (v : ℕ)))
          = tgt (off (v : ℕ) + (r - off (v : ℕ))) by
        rw [show off (v : ℕ) + (p - off (v : ℕ)) = p by omega,
          show off (v : ℕ) + (r - off (v : ℕ)) = r by omega]
        exact hpr)
    omega

/-! ## §4 The program

Four sweeps: clear the counting sort's cells, transpose, merge, and
record the two figures.  Nothing reads an array length — the carrier is
the arena's own `nN` cell (which is all `tpCom` needs, its Finding 1)
and the merged extent is the cursor the merge ends at (Finding 1
above). -/

/-- The merge's scratch scalars: the zeroing counter, the vertex, the
cursor, the row pointer, the row end, and the target read out. -/
def syScalars : List String := ["sy.i", "sy.v", "sy.c", "sy.j", "sy.f", "sy.w"]

/-- **The zeroing sweep**: the counting sort's degree cells, one store a
vertex.  `tpCom` asks for them zeroed on entry and nothing else in the
frame does. -/
def syZeroCom (nN dg : String) : Com :=
  .seq (.assign "sy.i" (.lit 0))
    (Csr.scan "sy.i" nN
      (.seq (.store dg (.var "sy.i") (.lit 0))
        (.assign "sy.i" (.add (.var "sy.i") (.lit 1)))))

/-- One slot of a row copy: read the target, place it at the cursor,
bump both pointers. -/
def syCopyBody (t st : String) : Com :=
  .seq (.assign "sy.w" (.get t (.var "sy.j")))
    (.seq (.store st (.var "sy.c") (.var "sy.w"))
      (.seq (.assign "sy.c" (.add (.var "sy.c") (.lit 1)))
        (.assign "sy.j" (.add (.var "sy.j") (.lit 1)))))

/-- **One row copy**: row `sy.v` of the CSR `(o, t)` laid at the cursor
`sy.c`.  The merge runs this twice a vertex — once at the in-neighbour
CSR, once at the transpose (Finding 2). -/
def syCopyCom (o t st : String) : Com :=
  .seq (.assign "sy.j" (.get o (.var "sy.v")))
    (.seq (.assign "sy.f" (.get o (.add (.var "sy.v") (.lit 1))))
      (Csr.scan "sy.j" "sy.f" (syCopyBody t st)))

/-- **One vertex's turn of the merge**: store the merged offset (which
is the cursor), then the in-arcs and then the out-arcs. -/
def syRowCom (io it qo qt so st : String) : Com :=
  .seq (.store so (.var "sy.v") (.var "sy.c"))
    (.seq (syCopyCom io it st)
      (.seq (syCopyCom qo qt st)
        (.assign "sy.v" (.add (.var "sy.v") (.lit 1)))))

/-- **The merge sweep**: one turn a vertex, then the last offset. -/
def syMergeCom (nN io it qo qt so st : String) : Com :=
  .seq (.assign "sy.v" (.lit 0))
    (.seq (.assign "sy.c" (.lit 0))
      (.seq (Csr.scan "sy.v" nN (syRowCom io it qo qt so st))
        (.store so (.var nN) (.var "sy.c"))))

/-- **The symmetrization's merge**, whole: zero, transpose, merge,
figures. -/
def symCom (nN io it qo qt dg so st nNy nSy : String) : Com :=
  .seq (syZeroCom nN dg)
    (.seq (tpCom nN io it qo qt dg)
      (.seq (syMergeCom nN io it qo qt so st)
        (.seq (.assign nNy (.var nN)) (.assign nSy (.var "sy.c")))))

/-- **The merge's budget** at `(N, a)` with `a = arcCount D`: the
zeroing sweep `11` a vertex, `tpCom`'s own `41·N + 40·a + 30`, the
merge sweep `35` a vertex and `36` an arc (`18` a slot, two slots an
arc), plus the fixed blocks. -/
def symK (N a : ℕ) : ℕ := 90 * N + 80 * a + 60

private theorem syScalars_ne {y : String} (h : y ∉ syScalars) :
    y ≠ "sy.i" ∧ y ≠ "sy.v" ∧ y ≠ "sy.c" ∧ y ≠ "sy.j" ∧ y ≠ "sy.f" ∧ y ≠ "sy.w" := by
  simp only [syScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

@[simp] theorem warrs_syCopyCom (o t st : String) : (syCopyCom o t st).warrs = [st] := by
  simp [syCopyCom, syCopyBody, Csr.scan, Com.warrs]

@[simp] theorem wvars_syCopyCom (o t st : String) :
    (syCopyCom o t st).wvars = ["sy.j", "sy.f", "sy.w", "sy.c", "sy.j"] := by
  simp [syCopyCom, syCopyBody, Csr.scan, Com.wvars]

/-! ## §5 A row copy, discharged

The specification is stated against the bare reading contract of §1 —
offsets at `o`, targets at `t` — and against the initial contents `L`
of `st`: what the copy does to `st` is to leave the cells below the
base and above the frontier alone and to fill the ones between. -/

/-- The carried state of a row copy. -/
private def SyCpInv (t st : String) (lo hi base : ℕ) (F : ℕ → ℕ) (L : List ℕ)
    (σ : Env) : Prop :=
  σ.vars "sy.f" = hi ∧ lo ≤ σ.vars "sy.j" ∧ σ.vars "sy.j" ≤ hi ∧
    σ.vars "sy.c" = base + (σ.vars "sy.j" - lo) ∧
    (∀ p, lo ≤ p → p < hi → (σ.arrs t)[p]? = some (F p)) ∧
    (σ.arrs st).length = L.length ∧
    (∀ p, p < base → (σ.arrs st).getD p 0 = L.getD p 0) ∧
    (∀ p, base + (σ.vars "sy.j" - lo) ≤ p → (σ.arrs st).getD p 0 = L.getD p 0) ∧
    (∀ k, k < σ.vars "sy.j" - lo → (σ.arrs st).getD (base + k) 0 = F (lo + k))

/-- **One slot of a row copy**, at `14`. -/
private theorem syCopy_step {B : ℕ} {t st : String} {lo hi base : ℕ} {F : ℕ → ℕ}
    {L : List ℕ} {σ : Env} (hstt : st ≠ t)
    (hhiB : hi < B) (hcB : base + (hi - lo) < B) (hfit : base + (hi - lo) ≤ L.length)
    (hFB : ∀ p, lo ≤ p → p < hi → F p < B)
    (hI : SyCpInv t st lo hi base F L σ) (hlt : σ.vars "sy.j" < hi) :
    ∃ σ' K', Run B (syCopyBody t st) σ σ' K' ∧
      SyCpInv t st lo hi base F L σ' ∧
      σ'.vars "sy.j" = σ.vars "sy.j" + 1 ∧ K' ≤ 14 := by
  obtain ⟨hf, hj1, hj2, hc, hread, hlen, hbelow, habove, hfill⟩ := hI
  obtain ⟨j, hj⟩ : ∃ j, σ.vars "sy.j" = j := ⟨_, rfl⟩
  rw [hj] at hj1 hj2 hlt hc habove hfill
  have hFjB : F j < B := hFB j hj1 hlt
  have hget : (σ.arrs t)[j]? = some (F j) := hread j hj1 hlt
  obtain ⟨c, hcv⟩ : ∃ c, c = base + (j - lo) := ⟨_, rfl⟩
  rw [← hcv] at hc
  have hclt : c < base + (hi - lo) := by omega
  -- `sy.w := t[sy.j]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "sy.w" (F j) := ⟨_, rfl⟩
  have r1 : Run B (.assign "sy.w" (.get t (.var "sy.j"))) σ σ1 3 := by
    rw [hσ1]
    exact sy_run_assign (sy_evB_get (sy_evB_var hj (by omega)) hget hFjB) (by simp)
  have h1c : σ1.vars "sy.c" = c := by rw [hσ1]; simp [hc]
  have h1w : σ1.vars "sy.w" = F j := by rw [hσ1]; simp
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  -- `st[sy.c] := sy.w`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setArr st c (F j) := ⟨_, rfl⟩
  have r2 : Run B (.store st (.var "sy.c") (.var "sy.w")) σ1 σ2 3 := by
    rw [hσ2]
    exact sy_run_store (sy_evB_var h1c (by omega)) (sy_evB_var h1w hFjB)
      (by rw [h1a]; omega) (by simp)
  have h2c : σ2.vars "sy.c" = c := by rw [hσ2]; simp [h1c]
  have h2j : σ2.vars "sy.j" = j := by rw [hσ2, hσ1]; simp [hj]
  -- `sy.c := sy.c + 1`
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setVar "sy.c" (c + 1) := ⟨_, rfl⟩
  have r3 : Run B (.assign "sy.c" (.add (.var "sy.c") (.lit 1))) σ2 σ3 4 := by
    rw [hσ3]
    exact sy_run_assign (sy_evB_add (sy_evB_var h2c (by omega)) (sy_evB_lit (by omega))
      (by omega)) (by simp)
  have h3j : σ3.vars "sy.j" = j := by rw [hσ3]; simp [h2j]
  -- `sy.j := sy.j + 1`
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setVar "sy.j" (j + 1) := ⟨_, rfl⟩
  have r4 : Run B (.assign "sy.j" (.add (.var "sy.j") (.lit 1))) σ3 σ4 4 := by
    rw [hσ4]
    exact sy_run_assign (sy_evB_add (sy_evB_var h3j (by omega)) (sy_evB_lit (by omega))
      (by omega)) (by simp)
  have hj' : σ4.vars "sy.j" = j + 1 := by rw [hσ4]; simp
  have hc' : σ4.vars "sy.c" = c + 1 := by rw [hσ4, hσ3]; simp
  have hf' : σ4.vars "sy.f" = hi := by rw [hσ4, hσ3, hσ2, hσ1]; simp [hf]
  have h4st : σ4.arrs st = (σ.arrs st).set c (F j) := by
    rw [hσ4, hσ3, hσ2, hσ1]; simp
  have h4A : ∀ b, b ≠ st → σ4.arrs b = σ.arrs b := by
    intro b hb; rw [hσ4, hσ3, hσ2, hσ1]; simp [hb]
  refine ⟨σ4, 14, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_,
    by rw [hj', hj], le_rfl⟩
  refine ⟨hf', by omega, by omega, by rw [hj', hc']; omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp1 hp2
    rw [h4A t (Ne.symm hstt)]
    exact hread p hp1 hp2
  · rw [h4st, List.length_set]; exact hlen
  · intro p hp
    rw [h4st, sy_getD_set_of_ne (by omega)]
    exact hbelow p hp
  · intro p hp
    rw [hj'] at hp
    rw [h4st, sy_getD_set_of_ne (by omega)]
    exact habove p (by omega)
  · intro k hk
    rw [hj'] at hk
    rw [h4st]
    rcases Nat.lt_or_ge k (j - lo) with hlt' | hge'
    · rw [sy_getD_set_of_ne (by omega)]
      exact hfill k hlt'
    · obtain rfl : k = j - lo := by omega
      rw [show base + (j - lo) = c by omega, sy_getD_set_self (by omega),
        show lo + (j - lo) = j by omega]

/-- **The copy's inner scan**: the whole row, at `18` a slot. -/
private theorem syCopy_scan {B : ℕ} {t st : String} {lo hi base : ℕ} {F : ℕ → ℕ}
    {L : List ℕ} (hstt : st ≠ t)
    (hhiB : hi < B) (hcB : base + (hi - lo) < B) (hfit : base + (hi - lo) ≤ L.length)
    (hFB : ∀ p, lo ≤ p → p < hi → F p < B) :
    Spec B (fun σ => SyCpInv t st lo hi base F L σ ∧ σ.vars "sy.j" = lo)
      (Csr.scan "sy.j" "sy.f" (syCopyBody t st))
      (fun _ σ' => SyCpInv t st lo hi base F L σ' ∧ σ'.vars "sy.j" = hi)
      (18 * (hi - lo) + 4) :=
  Csr.rowScan_spec B _ hi 14 "sy.j" "sy.f" (syCopyBody t st)
    (fun σ => SyCpInv t st lo hi base F L σ) hhiB
    (fun _ hI => ⟨hI.1, hI.2.2.1⟩)
    (fun _ hI hlt => syCopy_step hstt hhiB hcB hfit hFB hI hlt)
    (fun _ h => h.1) (fun _ h => by rw [h.2])

/-- **A row copy, discharged**: row `v` of `(o, t)` laid at the cursor,
at `18·(hi - lo) + 12`.  The cells of `st` below the base and at or
above the frontier are untouched; the ones between hold the row. -/
private theorem syCopy_spec {B : ℕ} {o t st : String} {v lo hi base : ℕ}
    {F : ℕ → ℕ} {L : List ℕ}
    (hstt : st ≠ t)
    (hhiB : hi < B) (hvB : v + 1 < B)
    (hcB : base + (hi - lo) < B) (hfit : base + (hi - lo) ≤ L.length)
    (hFB : ∀ p, lo ≤ p → p < hi → F p < B) :
    Spec B
      (fun σ => σ.vars "sy.v" = v ∧ σ.vars "sy.c" = base ∧
        (σ.arrs o)[v]? = some lo ∧ (σ.arrs o)[v + 1]? = some hi ∧
        lo ≤ hi ∧
        (∀ p, lo ≤ p → p < hi → (σ.arrs t)[p]? = some (F p)) ∧
        σ.arrs st = L)
      (syCopyCom o t st)
      (fun _ σ' => σ'.vars "sy.c" = base + (hi - lo) ∧
        (σ'.arrs st).length = L.length ∧
        (∀ p, p < base → (σ'.arrs st).getD p 0 = L.getD p 0) ∧
        (∀ p, base + (hi - lo) ≤ p → (σ'.arrs st).getD p 0 = L.getD p 0) ∧
        (∀ k, k < hi - lo → (σ'.arrs st).getD (base + k) 0 = F (lo + k)))
      (18 * (hi - lo) + 12) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hv, hcb, hoget, hoget1, hlohi, hread, hstL⟩ := hσ
  -- `sy.j := o[sy.v]`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "sy.j" lo := ⟨_, rfl⟩
  have r1 : Run B (.assign "sy.j" (.get o (.var "sy.v"))) σ σ1 3 := by
    rw [hσ1]
    exact sy_run_assign
      (sy_evB_get (sy_evB_var hv (by omega)) hoget (by omega)) (by simp)
  have h1v : σ1.vars "sy.v" = v := by rw [hσ1]; simp [hv]
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  -- `sy.f := o[sy.v + 1]`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "sy.f" hi := ⟨_, rfl⟩
  have r2 : Run B (.assign "sy.f" (.get o (.add (.var "sy.v") (.lit 1)))) σ1 σ2 5 := by
    rw [hσ2]
    refine sy_run_assign (sy_evB_get (sy_evB_add (sy_evB_var h1v (by omega))
      (sy_evB_lit (by omega)) (by omega)) ?_ (by omega)) (by simp)
    rw [h1a]; exact hoget1
  have h2a : σ2.arrs = σ.arrs := by rw [hσ2, hσ1]; simp
  have hI2 : SyCpInv t st lo hi base F L σ2 ∧ σ2.vars "sy.j" = lo := by
    have h2j : σ2.vars "sy.j" = lo := by rw [hσ2, hσ1]; simp
    have h2f : σ2.vars "sy.f" = hi := by rw [hσ2]; simp
    have h2c : σ2.vars "sy.c" = base := by rw [hσ2, hσ1]; simp [hcb]
    refine ⟨⟨h2f, by omega, by omega, by rw [h2c, h2j]; omega, ?_, ?_, ?_, ?_, ?_⟩, h2j⟩
    · intro p hp1 hp2; rw [h2a]; exact hread p hp1 hp2
    · rw [h2a, hstL]
    · intro p _; rw [h2a, hstL]
    · intro p _; rw [h2a, hstL]
    · intro k hk; rw [h2j] at hk; omega
  obtain ⟨σ3, hr3, hI3, hj3⟩ := (syCopy_scan hstt hhiB hcB hfit hFB).run hI2
  obtain ⟨-, -, -, hc3, -, hlen3, hbelow3, habove3, hfill3⟩ := hI3
  rw [hj3] at hc3 habove3 hfill3
  exact ⟨σ3, 3 + (5 + (18 * (hi - lo) + 4)), r1.seq (r2.seq hr3), by omega,
    hc3, hlen3, hbelow3, habove3, hfill3⟩

/-! ## §6 The merge sweep

One turn a vertex: store the merged offset — which is the cursor the
sweep already carries — then the in-arcs, then the out-arcs.  The two
copies are the same command at two instantiations (Finding 2), so this
section is bookkeeping over §5 and nothing more. -/

/-- **The merge's region discipline**: it writes `so`, `st` and (through
`tpCom`) `qo`, `qt`, `dg`; the five are apart from each other and from
the two arrays it reads. -/
structure SyNames (io it qo qt dg so st : String) : Prop where
  /-- The transpose's own discipline. -/
  tp : TpNames io it qo qt dg
  /-- The merged targets are none of the read regions. -/
  st_io : st ≠ io
  /-- The merged targets are none of the read regions. -/
  st_it : st ≠ it
  /-- The merged targets are none of the read regions. -/
  st_qo : st ≠ qo
  /-- The merged targets are none of the read regions. -/
  st_qt : st ≠ qt
  /-- The merged targets are not the counters. -/
  st_dg : st ≠ dg
  /-- The merged offsets are none of the read regions. -/
  so_io : so ≠ io
  /-- The merged offsets are none of the read regions. -/
  so_it : so ≠ it
  /-- The merged offsets are none of the read regions. -/
  so_qo : so ≠ qo
  /-- The merged offsets are none of the read regions. -/
  so_qt : so ≠ qt
  /-- The merged offsets are not the counters. -/
  so_dg : so ≠ dg
  /-- The two output regions are distinct. -/
  so_st : so ≠ st

private theorem not_mem_warrs_syCopy {o t st b : String} (h : b ≠ st) :
    b ∉ (syCopyCom o t st).warrs := by simp [h]

private theorem not_mem_wvars_syCopy {o t st y : String}
    (h1 : y ≠ "sy.j") (h2 : y ≠ "sy.f") (h3 : y ≠ "sy.w") (h4 : y ≠ "sy.c") :
    y ∉ (syCopyCom o t st).wvars := by simp [h1, h2, h3, h4]

/-- **What the merge has left in row `w`**: the in-neighbours of `w` in
the input CSR's own slot order, then its out-neighbours in the
transpose's. -/
def SymRowAt (st : String) (off tgt : ℕ → ℕ) {N : ℕ} (D : Orientation N)
    (otF : ℕ → ℕ) (w : ℕ) (σ : Env) : Prop :=
  (∀ k, k < off (w + 1) - off w →
      (σ.arrs st).getD (symOff off D w + k) 0 = tgt (off w + k)) ∧
  (∀ k, k < outOff D (w + 1) - outOff D w →
      (σ.arrs st).getD (symOff off D w + (off (w + 1) - off w) + k) 0
        = otF (outOff D w + k))

/-- A row lives below the next offset, so agreement there transports
it. -/
private theorem symRowAt_of_agree {st : String} {off tgt otF : ℕ → ℕ} {N : ℕ}
    {D : Orientation N} {w : ℕ} {σ σ' : Env} (hoff : off w ≤ off (w + 1))
    (h : SymRowAt st off tgt D otF w σ)
    (hagree : ∀ p, p < symOff off D (w + 1) →
      (σ'.arrs st).getD p 0 = (σ.arrs st).getD p 0) :
    SymRowAt st off tgt D otF w σ' := by
  have hout : outOff D w ≤ outOff D (w + 1) := outOff_le_succ D w
  have hsucc : symOff off D (w + 1)
      = symOff off D w + (off (w + 1) - off w) + (outOff D (w + 1) - outOff D w) := by
    simp only [symOff]; omega
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [hagree _ (by omega)]; exact h.1 k hk
  · rw [hagree _ (by omega)]; exact h.2 k hk

/-- The carried state of the merge sweep.

The two output allocations are asked for as `≥`, not `=`: the merge
never reads past its own extent, and an exact-length demand on `st` is
the trap `SolveCoverAllJoin` §4d pins — `2·arcCount D` moves from round
to round while an array's length cannot.  §9's `symCom_spec` recovers
the exact-length reading from this one at an exact allocation. -/
private def SyMInv (nN io it qo qt so st : String) {N : ℕ} (D : Orientation N)
    (off tgt otF : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars nN = N ∧ σ.vars "sy.v" ≤ N ∧
    σ.vars "sy.c" = symOff off D (σ.vars "sy.v") ∧
    SymSrc io it N off tgt σ ∧ SymSrc qo qt N (outOff D) otF σ ∧
    N + 1 ≤ (σ.arrs so).length ∧
    (∀ i, i < σ.vars "sy.v" → (σ.arrs so).getD i 0 = symOff off D i) ∧
    2 * arcCount D ≤ (σ.arrs st).length ∧
    (∀ w, w < σ.vars "sy.v" → SymRowAt st off tgt D otF w σ)

/-- **One vertex's turn of the merge**: `31` plus `18` a slot. -/
private theorem syRow_step {B : ℕ} {nN io it qo qt dg so st : String} {N : ℕ}
    {D : Orientation N} {off tgt otF : ℕ → ℕ} {σ : Env}
    (hnm : SyNames io it qo qt dg so st) (hnN : nN ∉ syScalars)
    (hB : N * N < B) (hNB : N < B) (hoffN : off N = arcCount D)
    (hI : SyMInv nN io it qo qt so st D off tgt otF σ) (hlt : σ.vars "sy.v" < N) :
    ∃ σ' K', Run B (syRowCom io it qo qt so st) σ σ' K' ∧
      SyMInv nN io it qo qt so st D off tgt otF σ' ∧
      σ'.vars "sy.v" = σ.vars "sy.v" + 1 ∧
      K' ≤ 31
        + 18 * (symOff off D (σ.vars "sy.v" + 1) - symOff off D (σ.vars "sy.v")) := by
  obtain ⟨hnNi, hnNv, hnNc, hnNj, hnNf, hnNw⟩ := syScalars_ne hnN
  obtain ⟨hcell, hvle, hcur, hsrc1, hsrc2, hsoLen, hsoV, hstLen, hrows⟩ := hI
  obtain ⟨v, hv⟩ : ∃ v, σ.vars "sy.v" = v := ⟨_, rfl⟩
  rw [hv] at hvle hcur hsoV hrows hlt
  -- the two rows' extents
  have h2a : 2 * arcCount D ≤ N * N := two_mul_arcCount_le_sq_orient D
  have hoffle : ∀ i, i ≤ N → off i ≤ arcCount D := by
    intro i hi; rw [← hoffN]; exact hsrc1.le hi le_rfl
  have houtle : ∀ i, i ≤ N → outOff D i ≤ arcCount D := fun i hi =>
    outOff_le_arcCount D hi
  have hd1 : off v ≤ off (v + 1) := hsrc1.mono v hlt
  have hd2 : outOff D v ≤ outOff D (v + 1) := outOff_le_succ D v
  have hbase1 : symOff off D v + (off (v + 1) - off v) = off (v + 1) + outOff D v := by
    simp only [symOff]; omega
  have hbase2 : symOff off D v + (off (v + 1) - off v) + (outOff D (v + 1) - outOff D v)
      = symOff off D (v + 1) := by simp only [symOff]; omega
  have hb1le : symOff off D v + (off (v + 1) - off v) ≤ 2 * arcCount D := by
    have := hoffle (v + 1) (by omega)
    have := houtle v (by omega)
    omega
  have hb2le : symOff off D (v + 1) ≤ 2 * arcCount D := by
    have := hoffle (v + 1) (by omega)
    have := houtle (v + 1) (by omega)
    simp only [symOff]; omega
  have hcurB : symOff off D v < B := by
    have : symOff off D v ≤ symOff off D (v + 1) :=
      symOff_le (D := D) (fun i hi => hsrc1.mono i hi) (by omega) (by omega)
    omega
  -- `so[sy.v] := sy.c`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setArr so v (symOff off D v) := ⟨_, rfl⟩
  have r1 : Run B (.store so (.var "sy.v") (.var "sy.c")) σ σ1 3 := by
    rw [hσ1]
    exact sy_run_store (sy_evB_var hv (by omega)) (sy_evB_var (hcur ▸ rfl) hcurB)
      (by omega) (by simp)
  have h1v : σ1.vars = σ.vars := by rw [hσ1]; simp
  have h1so : σ1.arrs so = (σ.arrs so).set v (symOff off D v) := by rw [hσ1]; simp
  have h1A : ∀ b, b ≠ so → σ1.arrs b = σ.arrs b := by
    intro b hb; rw [hσ1]; simp [hb]
  -- the in-arcs
  obtain ⟨σ2, hr2, hq2, hfv2, hfa2, -, -⟩ :=
    (syCopy_spec (B := B) (o := io) (t := it) (st := st) (v := v)
      (lo := off v) (hi := off (v + 1)) (base := symOff off D v) (F := tgt)
      (L := σ.arrs st) hnm.st_it
      (by have := hoffle (v + 1) (by omega); omega) (by omega)
      (by omega) (by omega)
      (fun p _ hp2 => lt_of_lt_of_le (hsrc1.tgtLt p (by
        have := hsrc1.le (show v + 1 ≤ N by omega) le_rfl; omega)) (le_of_lt hNB))).frame.run
      ⟨by rw [h1v, hv], by rw [h1v, hcur],
        by rw [h1A io (Ne.symm hnm.so_io)]; exact hsrc1.offGet v (by omega),
        by rw [h1A io (Ne.symm hnm.so_io)]; exact hsrc1.offGet (v + 1) (by omega),
        hd1,
        fun p hp1 hp2 => by
          rw [h1A it (Ne.symm hnm.so_it)]
          exact hsrc1.tgtGet p (by have := hsrc1.le (show v + 1 ≤ N by omega) le_rfl; omega),
        h1A st (Ne.symm hnm.so_st)⟩
  obtain ⟨hc2, hlen2, hbelow2, habove2, hfill2⟩ := hq2
  have h2A : ∀ b, b ≠ st → σ2.arrs b = σ1.arrs b :=
    fun b hb => hfa2 b (not_mem_warrs_syCopy hb)
  have h2v : σ2.vars "sy.v" = v := by
    rw [hfv2 _ (not_mem_wvars_syCopy (by decide) (by decide) (by decide) (by decide)),
      h1v, hv]
  have h2n : σ2.vars nN = N := by
    rw [hfv2 _ (not_mem_wvars_syCopy hnNj hnNf hnNw hnNc), h1v]; exact hcell
  -- the out-arcs
  obtain ⟨σ3, hr3, hq3, hfv3, hfa3, -, -⟩ :=
    (syCopy_spec (B := B) (o := qo) (t := qt) (st := st) (v := v)
      (lo := outOff D v) (hi := outOff D (v + 1))
      (base := symOff off D v + (off (v + 1) - off v)) (F := otF)
      (L := σ2.arrs st) hnm.st_qt
      (by have := houtle (v + 1) (by omega); omega) (by omega)
      (by omega) (by rw [hlen2]; omega)
      (fun p _ hp2 => lt_of_lt_of_le (hsrc2.tgtLt p (by
        have := houtle (v + 1) (show v + 1 ≤ N by omega)
        rw [outOff_last]; omega)) (le_of_lt hNB))).frame.run
      ⟨h2v, by rw [hc2],
        by rw [h2A qo hnm.st_qo.symm, h1A qo (Ne.symm hnm.so_qo)]
           exact hsrc2.offGet v (by omega),
        by rw [h2A qo hnm.st_qo.symm, h1A qo (Ne.symm hnm.so_qo)]
           exact hsrc2.offGet (v + 1) (by omega),
        hd2,
        fun p hp1 hp2 => by
          rw [h2A qt hnm.st_qt.symm, h1A qt (Ne.symm hnm.so_qt)]
          refine hsrc2.tgtGet p ?_
          have := houtle (v + 1) (show v + 1 ≤ N by omega)
          rw [outOff_last]; omega,
        rfl⟩
  obtain ⟨hc3, hlen3, hbelow3, habove3, hfill3⟩ := hq3
  have h3A : ∀ b, b ≠ st → σ3.arrs b = σ2.arrs b :=
    fun b hb => hfa3 b (not_mem_warrs_syCopy hb)
  have h3v : σ3.vars "sy.v" = v := by
    rw [hfv3 _ (not_mem_wvars_syCopy (by decide) (by decide) (by decide) (by decide)),
      h2v]
  have h3n : σ3.vars nN = N := by
    rw [hfv3 _ (not_mem_wvars_syCopy hnNj hnNf hnNw hnNc)]; exact h2n
  -- `sy.v := sy.v + 1`
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setVar "sy.v" (v + 1) := ⟨_, rfl⟩
  have r4 : Run B (.assign "sy.v" (.add (.var "sy.v") (.lit 1))) σ3 σ4 4 := by
    rw [hσ4]
    exact sy_run_assign (sy_evB_add (sy_evB_var h3v (by omega)) (sy_evB_lit (by omega))
      (by omega)) (by simp)
  have h4a : σ4.arrs = σ3.arrs := by rw [hσ4]; simp
  have h4v : σ4.vars "sy.v" = v + 1 := by rw [hσ4]; simp
  have h4c : σ4.vars "sy.c" = symOff off D (v + 1) := by
    rw [hσ4]; simp only [vars_setVar, if_neg (by decide : ¬ ("sy.c" = "sy.v"))]
    rw [hc3, hbase2]
  have h4n : σ4.vars nN = N := by rw [hσ4]; simp [hnNv, h3n]
  -- the arrays of the final state
  have h4B : ∀ b, b ≠ st → b ≠ so → σ4.arrs b = σ.arrs b := by
    intro b hb hbs
    rw [h4a, h3A b hb, h2A b hb, h1A b hbs]
  have h4so : σ4.arrs so = (σ.arrs so).set v (symOff off D v) := by
    rw [h4a, h3A so hnm.so_st, h2A so hnm.so_st, h1so]
  have h4stlen : 2 * arcCount D ≤ (σ4.arrs st).length := by
    rw [h4a, hlen3, hlen2]; exact hstLen
  have h4below : ∀ p, p < symOff off D v → (σ4.arrs st).getD p 0
      = (σ.arrs st).getD p 0 := by
    intro p hp
    rw [h4a, hbelow3 p (by omega), hbelow2 p hp]
  refine ⟨σ4, 3 + ((18 * (off (v + 1) - off v) + 12)
      + ((18 * (outOff D (v + 1) - outOff D v) + 12) + 4)),
    r1.seq (hr2.seq (hr3.seq r4)), ⟨h4n, by rw [h4v]; omega, by rw [h4v, h4c], ?_, ?_,
      ?_, ?_, h4stlen, ?_⟩, by rw [h4v, hv], ?_⟩
  · exact hsrc1.of_eq (h4B io (Ne.symm hnm.st_io) (Ne.symm hnm.so_io))
      (h4B it (Ne.symm hnm.st_it) (Ne.symm hnm.so_it))
  · exact hsrc2.of_eq (h4B qo (Ne.symm hnm.st_qo) (Ne.symm hnm.so_qo))
      (h4B qt (Ne.symm hnm.st_qt) (Ne.symm hnm.so_qt))
  · rw [h4so, List.length_set]; exact hsoLen
  · intro i hi
    rw [h4v] at hi
    rw [h4so]
    rcases Nat.lt_or_ge i v with hiv | hiv
    · rw [sy_getD_set_of_ne (by omega)]; exact hsoV i hiv
    · obtain rfl : i = v := by omega
      exact sy_getD_set_self (by omega)
  · intro w hw
    rw [h4v] at hw
    rcases Nat.lt_or_ge w v with hwv | hwv
    · refine symRowAt_of_agree (hsrc1.mono w (by omega)) (hrows w hwv) (fun p hp => ?_)
      refine h4below p (lt_of_lt_of_le hp ?_)
      exact symOff_le (D := D) (fun i hi => hsrc1.mono i hi) (by omega) (by omega)
    · obtain rfl : w = v := by omega
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [h4a, hbelow3 _ (by omega)]
        exact hfill2 k hk
      · rw [h4a]; exact hfill3 k hk
  · have hkey : symOff off D (v + 1) - symOff off D v
        = (off (v + 1) - off v) + (outOff D (v + 1) - outOff D v) := by
      simp only [symOff]; omega
    rw [hv, hkey]
    omega

/-- **The merge's outer scan**: `35` a vertex and `18` a slot, the two
terms of the potential. -/
private theorem syMerge_scan {B : ℕ} {nN io it qo qt dg so st : String} {N : ℕ}
    {D : Orientation N} {off tgt otF : ℕ → ℕ}
    (hnm : SyNames io it qo qt dg so st) (hnN : nN ∉ syScalars)
    (hB : N * N < B) (hNB : N < B) (hoffN : off N = arcCount D) (hoff0 : off 0 = 0) :
    Spec B (fun σ => SyMInv nN io it qo qt so st D off tgt otF σ ∧ σ.vars "sy.v" = 0)
      (Csr.scan "sy.v" nN (syRowCom io it qo qt so st))
      (fun _ σ' => SyMInv nN io it qo qt so st D off tgt otF σ' ∧ σ'.vars "sy.v" = N)
      (35 * N + 36 * arcCount D + 4) := by
  have h2a : 2 * arcCount D ≤ N * N := two_mul_arcCount_le_sq_orient D
  refine (Spec.while_potential (b := .lt (.var "sy.v") (.var nN))
    (fun σ => SyMInv nN io it qo qt so st D off tgt otF σ)
    (fun σ => 35 * (N - σ.vars "sy.v")
      + 18 * (2 * arcCount D - symOff off D (σ.vars "sy.v")))
    (fun σ hI => evalB_condLt_vars (by have := hI.2.1; omega)
      (by have := hI.1; omega)) ?_ (fun σ h => h.1) ?_).post ?_
  · intro σ hI hc
    have hlt : σ.vars "sy.v" < N := by
      have h1 := lt_of_condLt_true hc
      have h2 := hI.1
      omega
    obtain ⟨σ', K', hrun, hI', hv', hK'⟩ := syRow_step hnm hnN hB hNB hoffN hI hlt
    refine ⟨σ', K', hrun, hI', ?_⟩
    have hsrc1 := hI.2.2.2.1
    have hmono : symOff off D (σ.vars "sy.v") ≤ symOff off D (σ.vars "sy.v" + 1) :=
      symOff_le (D := D) (fun i hi => hsrc1.mono i hi) (by omega) (by omega)
    have hbnd : symOff off D (σ.vars "sy.v" + 1) ≤ 2 * arcCount D := by
      have h1 : off (σ.vars "sy.v" + 1) ≤ arcCount D := by
        rw [← hoffN]; exact hsrc1.le (by omega) le_rfl
      have h2 : outOff D (σ.vars "sy.v" + 1) ≤ arcCount D :=
        outOff_le_arcCount D (by omega)
      simp only [symOff]; omega
    simp only [size_condLt, size_var]
    rw [hv']
    omega
  · intro σ h
    have hz := h.2
    simp only [size_condLt, size_var]
    rw [hz, symOff_zero D hoff0]
    omega
  · rintro σ σ' - ⟨hI', hfalse⟩
    have h1 := le_of_condLt_false hfalse
    have h2 := hI'.1
    have h3 := hI'.2.1
    exact ⟨hI', by omega⟩

/-- **The merge sweep, discharged**: the merged offsets in `so`, the
merged rows in `st`, the extent in the cursor. -/
private theorem syMerge_spec {B : ℕ} {nN io it qo qt dg so st : String} {N : ℕ}
    {D : Orientation N} {off tgt otF : ℕ → ℕ}
    (hnm : SyNames io it qo qt dg so st) (hnN : nN ∉ syScalars)
    (hB : N * N < B) (hNB : N < B) (hoffN : off N = arcCount D) (hoff0 : off 0 = 0) :
    Spec B
      (fun σ => σ.vars nN = N ∧ SymSrc io it N off tgt σ ∧
        SymSrc qo qt N (outOff D) otF σ ∧
        N + 1 ≤ (σ.arrs so).length ∧ 2 * arcCount D ≤ (σ.arrs st).length)
      (syMergeCom nN io it qo qt so st)
      (fun _ σ' => σ'.vars "sy.c" = 2 * arcCount D ∧
        N + 1 ≤ (σ'.arrs so).length ∧
        (∀ i, i ≤ N → (σ'.arrs so).getD i 0 = symOff off D i) ∧
        2 * arcCount D ≤ (σ'.arrs st).length ∧
        (∀ w, w < N → SymRowAt st off tgt D otF w σ'))
      (35 * N + 36 * arcCount D + 11) := by
  obtain ⟨hnNi, hnNv, hnNc, hnNj, hnNf, hnNw⟩ := syScalars_ne hnN
  have h2a : 2 * arcCount D ≤ N * N := two_mul_arcCount_le_sq_orient D
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcell, hsrc1, hsrc2, hsoLen, hstLen⟩ := hσ
  -- `sy.v := 0`
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setVar "sy.v" 0 := ⟨_, rfl⟩
  have r1 : Run B (.assign "sy.v" (.lit 0)) σ σ1 2 := by
    rw [hσ1]; exact sy_run_assign (sy_evB_lit (by omega)) (by simp)
  have h1a : σ1.arrs = σ.arrs := by rw [hσ1]; simp
  -- `sy.c := 0`
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "sy.c" 0 := ⟨_, rfl⟩
  have r2 : Run B (.assign "sy.c" (.lit 0)) σ1 σ2 2 := by
    rw [hσ2]; exact sy_run_assign (sy_evB_lit (by omega)) (by simp)
  have h2a' : σ2.arrs = σ.arrs := by rw [hσ2, hσ1]; simp
  have hI2 : SyMInv nN io it qo qt so st D off tgt otF σ2 ∧ σ2.vars "sy.v" = 0 := by
    have h2v : σ2.vars "sy.v" = 0 := by rw [hσ2, hσ1]; simp
    have h2c : σ2.vars "sy.c" = 0 := by rw [hσ2]; simp
    have h2n : σ2.vars nN = N := by rw [hσ2, hσ1]; simp [hnNv, hnNc, hcell]
    refine ⟨⟨h2n, by rw [h2v]; omega, by rw [h2v, h2c, symOff_zero D hoff0], ?_, ?_,
      by rw [h2a']; exact hsoLen, ?_, by rw [h2a']; exact hstLen, ?_⟩, h2v⟩
    · exact hsrc1.of_eq (by rw [h2a']) (by rw [h2a'])
    · exact hsrc2.of_eq (by rw [h2a']) (by rw [h2a'])
    · intro i hi; rw [h2v] at hi; omega
    · intro w hw; rw [h2v] at hw; omega
  obtain ⟨σ3, hr3, hI3, hv3⟩ :=
    (syMerge_scan hnm hnN hB hNB hoffN hoff0).run hI2
  obtain ⟨h3n, -, h3c, -, -, h3soLen, h3soV, h3stLen, h3rows⟩ := hI3
  rw [hv3] at h3c h3soV h3rows
  have hlast : symOff off D N = 2 * arcCount D := symOff_last D hoffN
  -- `so[nN] := sy.c`
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setArr so N (2 * arcCount D) := ⟨_, rfl⟩
  have r4 : Run B (.store so (.var nN) (.var "sy.c")) σ3 σ4 3 := by
    rw [hσ4]
    exact sy_run_store (sy_evB_var h3n (by omega))
      (sy_evB_var (by rw [h3c, hlast]) (by omega)) (by omega) (by simp)
  have h4v : σ4.vars = σ3.vars := by rw [hσ4]; simp
  have h4so : σ4.arrs so = (σ3.arrs so).set N (2 * arcCount D) := by rw [hσ4]; simp
  have h4st : σ4.arrs st = σ3.arrs st := by rw [hσ4]; simp [Ne.symm hnm.so_st]
  refine ⟨σ4, 2 + (2 + ((35 * N + 36 * arcCount D + 4) + 3)),
    r1.seq (r2.seq (hr3.seq r4)), by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4v, h3c, hlast]
  · rw [h4so, List.length_set]; exact h3soLen
  · intro i hi
    rw [h4so]
    rcases Nat.lt_or_ge i N with hiN | hiN
    · rw [sy_getD_set_of_ne (by omega)]; exact h3soV i hiN
    · obtain rfl : i = N := by omega
      rw [sy_getD_set_self (by omega), hlast]
  · rw [h4st]; exact h3stLen
  · intro w hw
    obtain ⟨hp1, hp2⟩ := h3rows w hw
    exact ⟨fun k hk => by rw [h4st]; exact hp1 k hk,
      fun k hk => by rw [h4st]; exact hp2 k hk⟩

/-! ## §7 The zeroing sweep

`tpCom` asks for its degree cells zeroed on entry.  Nothing in the
augmentation frame supplies that, so the pass does it itself, at one
store a vertex. -/

private theorem syZero_spec {B : ℕ} {nN dg : String} {N : ℕ}
    (hnN : nN ∉ syScalars) (hNB : N < B) :
    Spec B (fun σ => σ.vars nN = N ∧ N ≤ (σ.arrs dg).length)
      (syZeroCom nN dg)
      (fun _ σ' => ∀ i, i < N → (σ'.arrs dg).getD i 0 = 0)
      (11 * N + 6) := by
  obtain ⟨hnNi, -, -, -, -, -⟩ := syScalars_ne hnN
  have hbody : Spec B
      (fun σ => (σ.vars nN = N ∧ σ.vars "sy.i" ≤ N ∧ N ≤ (σ.arrs dg).length ∧
          ∀ i, i < σ.vars "sy.i" → (σ.arrs dg).getD i 0 = 0) ∧ σ.vars "sy.i" < N)
      (.seq (.store dg (.var "sy.i") (.lit 0))
        (.assign "sy.i" (.add (.var "sy.i") (.lit 1))))
      (fun σ σ' => (σ'.vars nN = N ∧ σ'.vars "sy.i" ≤ N ∧ N ≤ (σ'.arrs dg).length ∧
          ∀ i, i < σ'.vars "sy.i" → (σ'.arrs dg).getD i 0 = 0) ∧
        σ'.vars "sy.i" = σ.vars "sy.i" + 1) 7 := by
    refine Spec.of_exists (fun σ hσ => ?_)
    obtain ⟨⟨hn, hle, hdg, hz⟩, hlt⟩ := hσ
    obtain ⟨i, hi⟩ : ∃ i, σ.vars "sy.i" = i := ⟨_, rfl⟩
    rw [hi] at hle hz hlt
    obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setArr dg i 0 := ⟨_, rfl⟩
    have r1 : Run B (.store dg (.var "sy.i") (.lit 0)) σ σ1 3 := by
      rw [hσ1]
      exact sy_run_store (sy_evB_var hi (by omega)) (sy_evB_lit (by omega))
        (by omega) (by simp)
    obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = σ1.setVar "sy.i" (i + 1) := ⟨_, rfl⟩
    have r2 : Run B (.assign "sy.i" (.add (.var "sy.i") (.lit 1))) σ1 σ2 4 := by
      rw [hσ2]
      refine sy_run_assign (sy_evB_add (sy_evB_var ?_ (by omega))
        (sy_evB_lit (by omega)) (by omega)) (by simp)
      rw [hσ1]; simp [hi]
    have h2dg : σ2.arrs dg = (σ.arrs dg).set i 0 := by rw [hσ2, hσ1]; simp
    have h2i : σ2.vars "sy.i" = i + 1 := by rw [hσ2]; simp
    refine ⟨σ2, 7, r1.seq r2, le_rfl, ⟨?_, ?_, ?_, ?_⟩, by rw [h2i, hi]⟩
    · rw [hσ2, hσ1]; simp [hnNi, hn]
    · rw [h2i]; omega
    · rw [h2dg, List.length_set]; exact hdg
    · intro q hq
      rw [h2i] at hq
      rw [h2dg]
      rcases Nat.lt_or_ge q i with hqi | hqi
      · rw [sy_getD_set_of_ne (by omega)]; exact hz q hqi
      · obtain rfl : q = i := by omega
        exact sy_getD_set_self (by omega)
  refine (Spec.forRangeZero (B := B) "sy.i" nN
    (fun σ => σ.vars nN = N ∧ σ.vars "sy.i" ≤ N ∧ N ≤ (σ.arrs dg).length ∧
      ∀ i, i < σ.vars "sy.i" → (σ.arrs dg).getD i 0 = 0)
    N 7 hNB (fun _ h => h.2.1) (fun _ h => h.1) hbody).conseq ?_ ?_ (by omega)
  · intro σ hσ
    refine ⟨by simpa [hnNi] using hσ.1, by simp, by simpa using hσ.2, ?_⟩
    intro i hi
    have h0 : (σ.setVar "sy.i" 0).vars "sy.i" = 0 := by simp
    omega
  · intro σ σ' _ hq
    exact fun i hi => hq.1.2.2.2 i (by rw [hq.2]; exact hi)


/-! ## §8 What the merge has built is a `GraphCsr` of `D.toGraph`

The two arrays are read back as `arrOf`s of their own contents — which
is where the exact lengths are spent, and the only place they are — and
the two remaining clauses are the rows'.  `asymm` is what makes a row
duplicate-free across the seam between its two halves, and `toGraph`'s
`Adjacent` is what makes its membership the symmetrized adjacency. -/

/-- Reading a vertex out of a slot: the value determines the `Fin`, so
the proof carried in the existential is never rewritten under. -/
private theorem exists_adj_of_val {N : ℕ} {G : SimpleGraph (Fin N)} {v z : Fin N}
    {u : ℕ} (hz : (z : ℕ) = u) (hadj : G.Adj v z) : ∃ hu : u < N, G.Adj v ⟨u, hu⟩ := by
  subst hz; exact ⟨z.isLt, hadj⟩

/-- **Every merged slot has an owner**: the merged offsets partition
`[0, 2·arcCount D)` into the vertices' rows. -/
private theorem symOff_owner {N : ℕ} {off : ℕ → ℕ} {D : Orientation N}
    (hoff0 : off 0 = 0) :
    ∀ m, m ≤ N → ∀ p, p < symOff off D m →
      ∃ w, w < N ∧ symOff off D w ≤ p ∧ p < symOff off D (w + 1) := by
  intro m
  induction m with
  | zero =>
      intro _ p hp
      rw [symOff_zero D hoff0] at hp
      omega
  | succ m ih =>
      intro hm p hp
      rcases Nat.lt_or_ge p (symOff off D m) with h | h
      · exact ih (by omega) p h
      · exact ⟨m, by omega, h, hp⟩

/-- The merged row's two halves, as a range split. -/
private theorem symOff_succ_eq {N : ℕ} {off : ℕ → ℕ} {D : Orientation N} {w : ℕ}
    (hd1 : off w ≤ off (w + 1)) :
    symOff off D (w + 1)
      = symOff off D w + (off (w + 1) - off w) + (outOff D (w + 1) - outOff D w) := by
  have hd2 : outOff D w ≤ outOff D (w + 1) := outOff_le_succ D w
  simp only [symOff]; omega

/-- **What a merged slot holds**: a target of the in-CSR's row, or a
target of the transpose's. -/
private theorem symRow_split {st : String} {off tgt otF : ℕ → ℕ} {N : ℕ}
    {D : Orientation N} {w p : ℕ} {σ : Env} (hd1 : off w ≤ off (w + 1))
    (hrow : SymRowAt st off tgt D otF w σ)
    (h1 : symOff off D w ≤ p) (h2 : p < symOff off D (w + 1)) :
    (∃ k, k < off (w + 1) - off w ∧ p = symOff off D w + k ∧
        (σ.arrs st).getD p 0 = tgt (off w + k)) ∨
      (∃ k, k < outOff D (w + 1) - outOff D w ∧
        p = symOff off D w + (off (w + 1) - off w) + k ∧
        (σ.arrs st).getD p 0 = otF (outOff D w + k)) := by
  have hsucc := symOff_succ_eq (D := D) hd1
  rcases Nat.lt_or_ge (p - symOff off D w) (off (w + 1) - off w) with hk | hk
  · refine Or.inl ⟨p - symOff off D w, hk, by omega, ?_⟩
    have hb := hrow.1 (p - symOff off D w) hk
    rwa [show symOff off D w + (p - symOff off D w) = p by omega] at hb
  · refine Or.inr ⟨p - symOff off D w - (off (w + 1) - off w), by omega, by omega, ?_⟩
    have hb := hrow.2 (p - symOff off D w - (off (w + 1) - off w)) (by omega)
    rwa [show symOff off D w + (off (w + 1) - off w)
      + (p - symOff off D w - (off (w + 1) - off w)) = p by omega] at hb

/-- **The merge's output is a `GraphCsr` of `D.toGraph`**, at the slot
count `2·arcCount D` — which is the only one it can have
(`symCsr_ns_eq`). -/
theorem graphCsr_of_symRows {so st io it qo qt : String} {N : ℕ}
    {D : Orientation N} {off tgt otF : ℕ → ℕ} {σ σ₀ : Env}
    (hin : TrInCsr io it D (arcCount D) off tgt σ₀)
    (hout : OutCsrAt qo qt D otF σ₀)
    (hsoLen : (σ.arrs so).length = N + 1)
    (hsoV : ∀ i, i ≤ N → (σ.arrs so).getD i 0 = symOff off D i)
    (hstLen : (σ.arrs st).length = 2 * arcCount D)
    (hrows : ∀ w, w < N → SymRowAt st off tgt D otF w σ) :
    GraphCsr so st D.toGraph (2 * arcCount D) σ := by
  classical
  have hmono : ∀ i, i < N → off i ≤ off (i + 1) := fun i hi => by
    have := hin.step ⟨i, hi⟩; simp only at this; omega
  have hoff0 : off 0 = 0 := hin.zero
  have hoffN : off N = arcCount D := hin.last
  have hlast : symOff off D N = 2 * arcCount D := symOff_last D hoffN
  have hoffle : ∀ i, i ≤ N → off i ≤ arcCount D := fun i hi => hin.off_le_ns hi
  have houtle : ∀ i, i ≤ N → outOff D i ≤ arcCount D := fun i hi =>
    outOff_le_arcCount D hi
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ, F = fun p => (σ.arrs st).getD p 0 := ⟨_, rfl⟩
  have hFval : ∀ p, F p = (σ.arrs st).getD p 0 := fun p => by rw [hF]
  -- the two arrays, read back
  have harrSo : σ.arrs so = arrOf (N + 1) (symOff off D) := by
    conv_lhs => rw [← Lax13Proofs.Codegen.arrOf_getD (σ.arrs so)]
    rw [hsoLen]
    exact arrOf_congr fun i hi => hsoV i (by omega)
  have harrSt : σ.arrs st = arrOf (2 * arcCount D) F := by
    conv_lhs => rw [← Lax13Proofs.Codegen.arrOf_getD (σ.arrs st)]
    rw [hstLen]
    exact arrOf_congr fun i _ => (hFval i).symm
  -- the two halves of a row, as slot values
  have hIn : ∀ w, w < N → ∀ k, k < off (w + 1) - off w →
      F (symOff off D w + k) = tgt (off w + k) := by
    intro w hw k hk; rw [hFval]; exact (hrows w hw).1 k hk
  have hOut : ∀ w, w < N → ∀ k, k < outOff D (w + 1) - outOff D w →
      F (symOff off D w + (off (w + 1) - off w) + k) = otF (outOff D w + k) := by
    intro w hw k hk; rw [hFval]; exact (hrows w hw).2 k hk
  have hInLt : ∀ w, w < N → ∀ k, k < off (w + 1) - off w → tgt (off w + k) < N := by
    intro w hw k hk
    refine hin.tgtLt _ ?_
    have := hoffle (w + 1) (by omega)
    omega
  have hOutLt : ∀ w, w < N → ∀ k, k < outOff D (w + 1) - outOff D w →
      otF (outOff D w + k) < N := by
    intro w hw k hk
    refine hout.qtLt _ ?_
    have := houtle (w + 1) (by omega)
    omega
  have hInMem : ∀ w, ∀ hw : w < N, ∀ k, ∀ hk : k < off (w + 1) - off w,
      (⟨tgt (off w + k), hInLt w hw k hk⟩ : Fin N) ∈ D.inN ⟨w, hw⟩ := by
    intro w hw k hk
    exact hin.sound ⟨w, hw⟩ (off w + k) (show off w ≤ off w + k by omega)
      (show off w + k < off (w + 1) by omega) _
  have hOutMem : ∀ w, ∀ hw : w < N, ∀ k, ∀ hk : k < outOff D (w + 1) - outOff D w,
      (⟨w, hw⟩ : Fin N) ∈ D.inN ⟨otF (outOff D w + k), hOutLt w hw k hk⟩ := by
    intro w hw k hk
    have := hout.sound ⟨w, hw⟩ (outOff D w + k)
      (show outOff D w ≤ outOff D w + k by omega)
      (show outOff D w + k < outOff D (w + 1) by omega) (hOutLt w hw k hk)
    rwa [mem_outNbrs] at this
  -- every slot holds a vertex
  have hFlt : ∀ p, p < 2 * arcCount D → F p < N := by
    intro p hp
    obtain ⟨w, hw, h1, h2⟩ :=
      symOff_owner (D := D) hoff0 N le_rfl p (by rw [hlast]; exact hp)
    rcases symRow_split (hmono w hw) (hrows w hw) h1 h2 with
      ⟨k, hk, hpk, hv⟩ | ⟨k, hk, hpk, hv⟩
    · rw [hFval, hv]; exact hInLt w hw k hk
    · rw [hFval, hv]; exact hOutLt w hw k hk
  refine ⟨symOff off D, F, ⟨harrSo, harrSt, fun i hi =>
    symOff_le (D := D) hmono (Nat.le_succ i) hi, hlast, hFlt⟩,
    symOff_zero D hoff0, ?_, ?_⟩
  · -- rows are duplicate free
    intro v
    have hw : (v : ℕ) < N := v.isLt
    have hd1 := hmono (v : ℕ) hw
    have hd2 := outOff_le_succ D (v : ℕ)
    have hsucc := symOff_succ_eq (D := D) hd1
    have hlen : Csr.rowLen (symOff off D) (v : ℕ)
        = (off ((v : ℕ) + 1) - off (v : ℕ))
          + (outOff D ((v : ℕ) + 1) - outOff D (v : ℕ)) := by
      simp only [Csr.rowLen]; omega
    have hb1 := hoffle ((v : ℕ) + 1) (by omega)
    have hb2 := houtle ((v : ℕ) + 1) (by omega)
    have hinj : ∀ a b, a < Csr.rowLen (symOff off D) (v : ℕ) →
        b < Csr.rowLen (symOff off D) (v : ℕ) →
        F (symOff off D (v : ℕ) + a) = F (symOff off D (v : ℕ) + b) → a = b := by
      have hmix : ∀ a b, a < off ((v : ℕ) + 1) - off (v : ℕ) →
          b < outOff D ((v : ℕ) + 1) - outOff D (v : ℕ) →
          tgt (off (v : ℕ) + a) ≠ otF (outOff D (v : ℕ) + b) := by
        intro a b ha hb hab
        have h1 := hInMem (v : ℕ) hw a ha
        have h2 := hOutMem (v : ℕ) hw b hb
        have hEq : (⟨tgt (off (v : ℕ) + a), hInLt (v : ℕ) hw a ha⟩ : Fin N)
            = ⟨otF (outOff D (v : ℕ) + b), hOutLt (v : ℕ) hw b hb⟩ := Fin.ext hab
        rw [hEq] at h1
        exact D.asymm _ _ h1 h2
      intro a b ha hb hab
      rw [hlen] at ha hb
      rcases Nat.lt_or_ge a (off ((v : ℕ) + 1) - off (v : ℕ)) with hA | hA <;>
        rcases Nat.lt_or_ge b (off ((v : ℕ) + 1) - off (v : ℕ)) with hB | hB
      · rw [hIn (v : ℕ) hw a hA, hIn (v : ℕ) hw b hB] at hab
        have := hin.inj v (off (v : ℕ) + a) (off (v : ℕ) + b) (by omega)
          (by omega) (by omega) (by omega) hab
        omega
      · rw [hIn (v : ℕ) hw a hA,
          show symOff off D (v : ℕ) + b
            = symOff off D (v : ℕ) + (off ((v : ℕ) + 1) - off (v : ℕ))
              + (b - (off ((v : ℕ) + 1) - off (v : ℕ))) by omega,
          hOut (v : ℕ) hw _ (show b - (off ((v : ℕ) + 1) - off (v : ℕ))
            < outOff D ((v : ℕ) + 1) - outOff D (v : ℕ) by omega)] at hab
        exact absurd hab (hmix a _ hA (by omega))
      · rw [hIn (v : ℕ) hw b hB,
          show symOff off D (v : ℕ) + a
            = symOff off D (v : ℕ) + (off ((v : ℕ) + 1) - off (v : ℕ))
              + (a - (off ((v : ℕ) + 1) - off (v : ℕ))) by omega,
          hOut (v : ℕ) hw _ (show a - (off ((v : ℕ) + 1) - off (v : ℕ))
            < outOff D ((v : ℕ) + 1) - outOff D (v : ℕ) by omega)] at hab
        exact absurd hab.symm (hmix b _ hB (by omega))
      · rw [show symOff off D (v : ℕ) + a
            = symOff off D (v : ℕ) + (off ((v : ℕ) + 1) - off (v : ℕ))
              + (a - (off ((v : ℕ) + 1) - off (v : ℕ))) by omega,
          hOut (v : ℕ) hw _ (show a - (off ((v : ℕ) + 1) - off (v : ℕ))
            < outOff D ((v : ℕ) + 1) - outOff D (v : ℕ) by omega),
          show symOff off D (v : ℕ) + b
            = symOff off D (v : ℕ) + (off ((v : ℕ) + 1) - off (v : ℕ))
              + (b - (off ((v : ℕ) + 1) - off (v : ℕ))) by omega,
          hOut (v : ℕ) hw _ (show b - (off ((v : ℕ) + 1) - off (v : ℕ))
            < outOff D ((v : ℕ) + 1) - outOff D (v : ℕ) by omega)] at hab
        have := hout.inj v (outOff D (v : ℕ) + (a - (off ((v : ℕ) + 1) - off (v : ℕ))))
          (outOff D (v : ℕ) + (b - (off ((v : ℕ) + 1) - off (v : ℕ))))
          (by omega) (by omega) (by omega) (by omega) hab
        omega
    rw [Csr.row, arrOf]
    exact List.Nodup.map_on (fun a ha b hb hab =>
      hinj a b (List.mem_range.1 ha) (List.mem_range.1 hb) hab) List.nodup_range
  · -- a row is the symmetrized neighbourhood
    intro v u
    have hw : (v : ℕ) < N := v.isLt
    have hd1 := hmono (v : ℕ) hw
    have hd2 := outOff_le_succ D (v : ℕ)
    have hsucc := symOff_succ_eq (D := D) hd1
    have hb1 := hoffle ((v : ℕ) + 1) (by omega)
    have hb2 := houtle ((v : ℕ) + 1) (by omega)
    rw [mem_row_iff]
    constructor
    · rintro ⟨p, hlo, hhi, rfl⟩
      rcases symRow_split hd1 (hrows (v : ℕ) hw) hlo hhi with
        ⟨k, hk, hpk, hv⟩ | ⟨k, hk, hpk, hv⟩
      · refine exists_adj_of_val
          (z := ⟨tgt (off (v : ℕ) + k), hInLt (v : ℕ) hw k hk⟩) ?_ (Or.inr ?_)
        · rw [hFval, hv]
        · exact hInMem (v : ℕ) hw k hk
      · refine exists_adj_of_val
          (z := ⟨otF (outOff D (v : ℕ) + k), hOutLt (v : ℕ) hw k hk⟩) ?_ (Or.inl ?_)
        · rw [hFval, hv]
        · exact hOutMem (v : ℕ) hw k hk
    · rintro ⟨hu, hadj⟩
      rcases hadj with hadj | hadj
      · -- `v` points at `u`: the transpose's row
        obtain ⟨q, hq1, hq2, hq3⟩ := hout.complete v ⟨u, hu⟩ (mem_outNbrs.2 hadj)
        simp only at hq1 hq2 hq3
        refine ⟨symOff off D (v : ℕ) + (off ((v : ℕ) + 1) - off (v : ℕ))
          + (q - outOff D (v : ℕ)), by omega, by omega, ?_⟩
        rw [hOut (v : ℕ) hw _ (show q - outOff D (v : ℕ)
            < outOff D ((v : ℕ) + 1) - outOff D (v : ℕ) by omega),
          show outOff D (v : ℕ) + (q - outOff D (v : ℕ)) = q by omega]
        exact hq3
      · -- `u` points at `v`: the in-CSR's row
        obtain ⟨p, hq1, hq2, hq3⟩ := hin.complete v ⟨u, hu⟩ hadj
        simp only at hq1 hq2 hq3
        refine ⟨symOff off D (v : ℕ) + (p - off (v : ℕ)), by omega, by omega, ?_⟩
        rw [hIn (v : ℕ) hw _ (show p - off (v : ℕ)
            < off ((v : ℕ) + 1) - off (v : ℕ) by omega),
          show off (v : ℕ) + (p - off (v : ℕ)) = p by omega]
        exact hq3

/-! ## §9 The pass, whole

Zero, transpose, merge, figures — at `symK N a = 90·N + 80·a + 60`,
which is `11·N + 6` for the zeroing, `tpCom`'s own `41·N + 40·a + 30`,
`35·N + 36·a + 11` for the merge and `4` for the two cells: `87·N +
76·a + 51` spent against it. -/

/-- **The carrier and the arcs together fit inside `N²`.**  A vertex
has at most `N` neighbours and an arc is two of them, so
`2·arcCount D ≤ N²`; the carrier fits alongside because `2·N ≤ N²`
above `N = 1`, and below it there are no arcs at all.  This is what
makes `tpCom`'s word obligation `N + arcCount D < B` follow from
`sq_lt_mcB` with nothing else. -/
private theorem carrier_add_arcCount_le_sq {N : ℕ} (D : Orientation N) :
    N + arcCount D ≤ N * N := by
  have h2 : 2 * arcCount D ≤ N * N := two_mul_arcCount_le_sq_orient D
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp only [Nat.zero_mul] at h2 ⊢; omega
  · rcases Nat.lt_or_ge N 2 with h | h
    · obtain rfl : N = 1 := by omega
      simp only [Nat.one_mul] at h2 ⊢; omega
    · have h3 : 2 * N ≤ N * N := Nat.mul_le_mul_right N h
      omega

@[simp] theorem warrs_syZeroCom (nN dg : String) : (syZeroCom nN dg).warrs = [dg] := by
  simp [syZeroCom, Csr.scan, Com.warrs]

private theorem not_mem_wvars_syZeroCom {nN dg y : String} (h : y ≠ "sy.i") :
    y ∉ (syZeroCom nN dg).wvars := by simp [syZeroCom, Csr.scan, Com.wvars, h]

private theorem not_mem_warrs_tpCom' {nN o t qo qt dg b : String}
    (h1 : b ≠ dg) (h2 : b ≠ qo) (h3 : b ≠ qt) :
    b ∉ (tpCom nN o t qo qt dg).warrs := by
  simp [tpCom, tpCntCom, tpOffCom, tpScatCom, tpScatOut, tpScatIn, Csr.scan,
    Com.warrs, h1, h2, h3]

private theorem not_mem_wvars_tpCom' {nN o t qo qt dg y : String}
    (h : y ∉ tpScalars) : y ∉ (tpCom nN o t qo qt dg).wvars := by
  simp only [tpScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp [tpCom, tpCntCom, tpOffCom, tpScatCom, tpScatOut, tpScatIn, Csr.scan,
    Com.wvars, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

private theorem not_mem_warrs_syMergeCom {nN io it qo qt so st b : String}
    (h1 : b ≠ so) (h2 : b ≠ st) : b ∉ (syMergeCom nN io it qo qt so st).warrs := by
  simp [syMergeCom, syRowCom, syCopyCom, syCopyBody, Csr.scan, Com.warrs, h1, h2]

private theorem not_mem_wvars_syMergeCom {nN io it qo qt so st y : String}
    (h : y ∉ syScalars) : y ∉ (syMergeCom nN io it qo qt so st).wvars := by
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := syScalars_ne h
  simp [syMergeCom, syRowCom, syCopyCom, syCopyBody, Csr.scan, Com.wvars,
    h2, h3, h4, h5, h6]

/-- **The whole merge pass, discharged at a windowed output.**  From the
in-neighbour CSR of `D`, the three scratch allocations and the two output
regions at **at least** their extents, `symCom` leaves a `GraphCsr` of
`D.toGraph` in the *truncation* of `(so, st)` to `(N + 1, 2·arcCount D)`,
and the two figures in `(nNy, nSy)`.

The window is the whole point.  `GraphCsr` pins both array lengths by
equality, `store` is `List.set`, so an exact-length output demand is a
demand on whoever allocated the arrays — and `2·arcCount D` is the
*final* orientation's arc count, which grows with every round while a
length cannot.  Asking only `2·arcCount D ≤ (σ.arrs st).length` lets the
allocation be sized once, by the carrier alone, and read at its extent;
this is exactly the move `augStInNW` already makes for the orientation
region (`SolveAugOrient` §10) and what `SolveCoverAllJoin`'s
`coverAllSym_srd_forces_constant` shows is *forced*. -/
theorem symComW_spec {B : ℕ} {nN io it qo qt dg so st nNy nSy : String} {N : ℕ}
    {D : Orientation N} {off tgt : ℕ → ℕ}
    (hnm : SyNames io it qo qt dg so st) (hnN : nN ∉ syScalars)
    (hnNtp : nN ∉ tpScalars) (hyN : nNy ∉ syScalars) (hyS : nSy ∉ syScalars)
    (hys : nSy ≠ nNy) (hB : N * N < B) :
    Spec B
      (fun σ => σ.vars nN = N ∧ TrInCsr io it D (arcCount D) off tgt σ ∧
        N + 1 ≤ (σ.arrs qo).length ∧ arcCount D ≤ (σ.arrs qt).length ∧
        N ≤ (σ.arrs dg).length ∧
        N + 1 ≤ (σ.arrs so).length ∧ 2 * arcCount D ≤ (σ.arrs st).length)
      (symCom nN io it qo qt dg so st nNy nSy)
      (fun _ σ' => GraphCsr so st D.toGraph (2 * arcCount D)
          (winA (inWs so st N (2 * arcCount D)) σ') ∧
        σ'.vars nNy = N ∧ σ'.vars nSy = 2 * arcCount D)
      (symK N (arcCount D)) := by
  obtain ⟨hnNi, hnNv, hnNc, hnNj, hnNf, hnNw⟩ := syScalars_ne hnN
  obtain ⟨-, -, hyNc, -, -, -⟩ := syScalars_ne hyN
  obtain ⟨-, -, hySc, -, -, -⟩ := syScalars_ne hyS
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcell, hin, hqoL, hqtL, hdgL, hsoL, hstL⟩ := hσ
  have hNa : N + arcCount D ≤ N * N := carrier_add_arcCount_le_sq D
  have h2sq : 2 * arcCount D ≤ N * N := two_mul_arcCount_le_sq_orient D
  have hNB : N < B := by omega
  have hoffN : off N = arcCount D := hin.last
  have hoff0 : off 0 = 0 := hin.zero
  -- the zeroing sweep
  obtain ⟨σ1, hr1, hz1, hfv1, hfa1, -, -⟩ :=
    (syZero_spec (B := B) (nN := nN) (dg := dg) (N := N) hnN hNB).frame.run ⟨hcell, hdgL⟩
  have hlen1 := run_arrs_length_eq hr1
  have h1A : ∀ b, b ≠ dg → σ1.arrs b = σ.arrs b := by
    intro b hb; exact hfa1 b (by simp [hb])
  have h1n : σ1.vars nN = N := by
    rw [hfv1 _ (not_mem_wvars_syZeroCom hnNi)]; exact hcell
  have h1in : TrInCsr io it D (arcCount D) off tgt σ1 :=
    hin.of_eq (h1A io (Ne.symm hnm.tp.dg_o)) (h1A it (Ne.symm hnm.tp.dg_t))
  -- the transpose
  obtain ⟨σ2, hr2, ⟨h2in, otF, h2out⟩, hfv2, hfa2, -, -⟩ :=
    (transposeIn_tpCom (B := B) (nN := nN) (o := io) (t := it) (qo := qo) (qt := qt)
      (dg := dg) hnm.tp hnNtp D (arcCount D) off tgt).frame.run
      ⟨h1in, h1n, by omega,
        by rw [h1A qo hnm.tp.qo_dg]; exact hqoL,
        by rw [h1A qt hnm.tp.qt_dg]; exact hqtL,
        by rw [hlen1 dg]; exact hdgL, hz1⟩
  have h2A : ∀ b, b ≠ dg → b ≠ qo → b ≠ qt → σ2.arrs b = σ1.arrs b := by
    intro b h1 h2 h3; exact hfa2 b (not_mem_warrs_tpCom' h1 h2 h3)
  have h2n : σ2.vars nN = N := by
    rw [hfv2 _ (not_mem_wvars_tpCom' hnNtp)]; exact h1n
  -- the merge sweep
  obtain ⟨σ3, hr3, ⟨h3c, h3soLen, h3soV, h3stLen, h3rows⟩, hfv3, hfa3, -, -⟩ :=
    (syMerge_spec (B := B) (nN := nN) (io := io) (it := it) (qo := qo) (qt := qt)
      (dg := dg) (so := so) (st := st) (D := D) (off := off) (tgt := tgt) (otF := otF)
      hnm hnN hB hNB hoffN hoff0).frame.run
      ⟨h2n, symSrc_of_trInCsr h2in, symSrc_of_outCsrAt h2out,
        by rw [h2A so hnm.so_dg hnm.so_qo hnm.so_qt, h1A so hnm.so_dg]
           exact hsoL,
        by rw [h2A st hnm.st_dg hnm.st_qo hnm.st_qt, h1A st hnm.st_dg]
           exact hstL⟩
  have h3n : σ3.vars nN = N := by
    rw [hfv3 _ (not_mem_wvars_syMergeCom hnN)]; exact h2n
  -- the output, read at its own extents
  have hws_o : inWs so st N (2 * arcCount D) so = some (N + 1) :=
    inWs_o so st N _
  have hws_t : inWs so st N (2 * arcCount D) st = some (2 * arcCount D) :=
    inWs_t (Ne.symm hnm.so_st) N _
  have hoffle : ∀ i, i ≤ N → off i ≤ arcCount D := fun i hi => h2in.off_le_ns hi
  have houtle : ∀ i, i ≤ N → outOff D i ≤ arcCount D := fun i hi =>
    outOff_le_arcCount D hi
  have hcsr : GraphCsr so st D.toGraph (2 * arcCount D)
      (winA (inWs so st N (2 * arcCount D)) σ3) := by
    refine graphCsr_of_symRows h2in h2out ?_ ?_ ?_ ?_
    · rw [arrs_winA_some hws_o, List.length_take]; omega
    · intro i hi
      rw [arrs_winA_some hws_o, sy_getD_take (by omega)]
      exact h3soV i hi
    · rw [arrs_winA_some hws_t, List.length_take]; omega
    · intro w hw
      have hstep : off (w + 1) = off w + (D.inN ⟨w, hw⟩).card := h2in.step ⟨w, hw⟩
      refine symRowAt_of_agree (by omega) (h3rows w hw) (fun p hp => ?_)
      have h1 := hoffle (w + 1) (by omega)
      have h2 := houtle (w + 1) (by omega)
      have hb : symOff off D (w + 1) ≤ 2 * arcCount D := by
        simp only [symOff]; omega
      rw [arrs_winA_some hws_t, sy_getD_take (by omega)]
  -- `nNy := nN`
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setVar nNy N := ⟨_, rfl⟩
  have r4 : Run B (.assign nNy (.var nN)) σ3 σ4 2 := by
    rw [hσ4]; exact sy_run_assign (sy_evB_var h3n hNB) (by simp)
  have h4c : σ4.vars "sy.c" = 2 * arcCount D := by
    rw [hσ4]; simp [Ne.symm hyNc, h3c]
  have h4a : σ4.arrs = σ3.arrs := by rw [hσ4]; simp
  -- `nSy := sy.c`
  obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = σ4.setVar nSy (2 * arcCount D) := ⟨_, rfl⟩
  have r5 : Run B (.assign nSy (.var "sy.c")) σ4 σ5 2 := by
    rw [hσ5]; exact sy_run_assign (sy_evB_var h4c (by omega)) (by simp)
  have h5a : σ5.arrs = σ3.arrs := by rw [hσ5]; simp [h4a]
  refine ⟨σ5, (11 * N + 6) + (tpK N (arcCount D)
      + ((35 * N + 36 * arcCount D + 11) + (2 + 2))),
    hr1.seq (hr2.seq (hr3.seq (r4.seq r5))), ?_, ?_, ?_, ?_⟩
  · simp only [symK, tpK]; omega
  · exact graphCsr_of_eq hcsr (by simp only [arrs_winA_some hws_o, h5a])
      (by simp only [arrs_winA_some hws_t, h5a])
  · rw [hσ5, hσ4]; simp [Ne.symm hys]
  · rw [hσ5]; simp

/-- **The same pass at an exact allocation** — the landed reading,
unchanged.  When the two output regions are handed at exactly the two
lengths `GraphCsr` pins, the truncation is the array
(`List.take_length`) and the windowed conclusion is the plain one. -/
theorem symCom_spec {B : ℕ} {nN io it qo qt dg so st nNy nSy : String} {N : ℕ}
    {D : Orientation N} {off tgt : ℕ → ℕ}
    (hnm : SyNames io it qo qt dg so st) (hnN : nN ∉ syScalars)
    (hnNtp : nN ∉ tpScalars) (hyN : nNy ∉ syScalars) (hyS : nSy ∉ syScalars)
    (hys : nSy ≠ nNy) (hB : N * N < B) :
    Spec B
      (fun σ => σ.vars nN = N ∧ TrInCsr io it D (arcCount D) off tgt σ ∧
        N + 1 ≤ (σ.arrs qo).length ∧ arcCount D ≤ (σ.arrs qt).length ∧
        N ≤ (σ.arrs dg).length ∧
        (σ.arrs so).length = N + 1 ∧ (σ.arrs st).length = 2 * arcCount D)
      (symCom nN io it qo qt dg so st nNy nSy)
      (fun _ σ' => GraphCsr so st D.toGraph (2 * arcCount D) σ' ∧
        σ'.vars nNy = N ∧ σ'.vars nSy = 2 * arcCount D)
      (symK N (arcCount D)) := by
  refine (specArrsLength
    (symComW_spec hnm hnN hnNtp hyN hyS hys hB (off := off) (tgt := tgt))).conseq
      (fun σ hσ => ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1,
        le_of_eq hσ.2.2.2.2.2.1.symm, le_of_eq hσ.2.2.2.2.2.2.symm⟩) ?_ le_rfl
  rintro σ σ' ⟨-, -, -, -, -, hsoL, hstL⟩ ⟨⟨hcsr, hnNy, hnSy⟩, hlen⟩
  have hso' : (σ'.arrs so).length = N + 1 := by rw [hlen so]; exact hsoL
  have hst' : (σ'.arrs st).length = 2 * arcCount D := by rw [hlen st]; exact hstL
  refine ⟨graphCsr_of_eq hcsr ?_ ?_, hnNy, hnSy⟩
  · rw [arrs_winA_some (inWs_o so st N (2 * arcCount D)), ← hso']
    exact List.take_length.symm
  · rw [arrs_winA_some (inWs_t (Ne.symm hnm.so_st) N (2 * arcCount D)), ← hst']
    exact List.take_length.symm

/-! ## §10 `AugSymCsrIn`, discharged

The frame plumbing is `augBaseAdjIn_bldAdjCom`'s, at the merge's own
five written regions.  Two things carry the weight:

* **the exact lengths**, which come from `Srd` through `symCsrSizes`
  and `symCsrSizes_exact` and from nowhere else — the residual is used
  exactly as `SolveAugBaseFrame` §3 says it is meetable, and is not
  restated;
* **the slot count**, which is `2·arcCount D` because a `GraphCsr` of
  `D.toGraph` has no other (`symCsr_ns_le`, an equality by
  `symCsr_ns_eq`), so the contract's `ns ≤ 2·arcCount D` costs
  nothing. -/

/-- A level's name is never one of a routine's fixed scratch names —
the `lv` mechanism's distinctness at bases of one length. -/
private theorem lv_ne_fixed {s b : String} (hlen : s.length = b.length)
    (hne : s ≠ b) (j : ℕ) : lv s j ≠ b :=
  fun h => hne (lv_inj hlen (h.trans (lv_zero b).symm)).1

theorem arenaNames_nN_notMem_syScalars (j : ℕ) : (arenaNames j).nN ∉ syScalars := by
  simp only [syScalars, arenaNames, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lv_ne_fixed (by decide) (by decide) j

theorem arenaNames_nS_notMem_syScalars (j : ℕ) : (arenaNames j).nS ∉ syScalars := by
  simp only [syScalars, arenaNames, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lv_ne_fixed (by decide) (by decide) j

theorem arenaNames_nN_notMem_tpScalars (j : ℕ) : (arenaNames j).nN ∉ tpScalars := by
  simp only [tpScalars, arenaNames, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_fixed (by decide) (by decide) j

theorem arenaNames_nS_notMem_tpScalars (j : ℕ) : (arenaNames j).nS ∉ tpScalars := by
  simp only [tpScalars, arenaNames, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact lv_ne_fixed (by decide) (by decide) j

theorem not_mem_warrs_symCom {nN io it qo qt dg so st nNy nSy b : String}
    (h1 : b ≠ qo) (h2 : b ≠ qt) (h3 : b ≠ dg) (h4 : b ≠ so) (h5 : b ≠ st) :
    b ∉ (symCom nN io it qo qt dg so st nNy nSy).warrs := by
  simp [symCom, syZeroCom, tpCom, tpCntCom, tpOffCom, tpScatCom, tpScatOut, tpScatIn,
    syMergeCom, syRowCom, syCopyCom, syCopyBody, Csr.scan, Com.warrs, h1, h2, h3, h4, h5]

theorem not_mem_wvars_symCom {nN io it qo qt dg so st nNy nSy y : String}
    (h1 : y ∉ syScalars) (h2 : y ∉ tpScalars) (h3 : y ≠ nNy) (h4 : y ≠ nSy) :
    y ∉ (symCom nN io it qo qt dg so st nNy nSy).wvars := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := syScalars_ne h1
  simp only [tpScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h2
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := h2
  simp [symCom, syZeroCom, tpCom, tpCntCom, tpOffCom, tpScatCom, tpScatOut, tpScatIn,
    syMergeCom, syRowCom, syCopyCom, syCopyBody, Csr.scan, Com.wvars,
    a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, h3, h4]

open Classical in
/-- **`AugSymCsrIn`, discharged** by `symCom` at the budget
`90·A.N + 80·arcCount D + 60`, at the canonical orientation region
`augStInN` (`SolveAugCompose` §7).

The rounds' descriptor `Srd` is asked for `symCsrSizes` — the two exact
allocations `GraphCsr` demands, stated in terms of `σ` alone
(`SolveAugBaseFrame` §3) — together with the merge's three scratch
allocations and the build's four output regions, all in the same
`σ`-only spelling.  Nothing else about `soO`/`stO` is assumed and no
landed residual is restated.

Against `augChainCost_le_selChainCharge`'s coefficient bounds, through
`augSymIn_of_symCsr_build` this is `augSymBudget` at `(171, 196, 84)`:
`sn ≤ 3·k` and `sa ≤ 5·k` hold at every `k ≥ 57`, and the base passes
already close at `k = 475`. -/
theorem augSymCsrIn_symCom (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (io it nA : ℕ → String)
    (nNy nSy soO stO qoY qtY dgY : ℕ → String)
    (aoO ajO dgO mtO : ℕ → String)
    (Srd Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnm : ∀ j, SyNames (io j) (it j) (qoY j) (qtY j) (dgY j) (soO j) (stO j))
    (hcy : ∀ j, nNy j ∉ syScalars ∧ nSy j ∉ syScalars ∧ nSy j ≠ nNy j ∧
      nNy j ≠ (arenaNames j).nN ∧ nNy j ≠ (arenaNames j).nS ∧
      nSy j ≠ (arenaNames j).nN ∧ nSy j ≠ (arenaNames j).nS)
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ qoY j ∧ b ≠ qtY j ∧ b ≠ dgY j ∧ b ≠ soO j ∧ b ≠ stO j)
    (hSrd : ∀ j σ, Srd j σ →
      symCsrSizes nA soO stO j σ ∧
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (qoY j)).length ∧
      σ.vars (nA j) ≤ (σ.arrs (qtY j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (dgY j)).length ∧
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (aoO j)).length ∧
      2 * σ.vars (nA j) ≤ (σ.arrs (ajO j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (dgO j)).length ∧
      2 * σ.vars (nA j) ≤ (σ.arrs (mtO j)).length)
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j → b ≠ stO j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ syScalars → y ∉ tpScalars → y ≠ nNy j → y ≠ nSy j →
        σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j → b ≠ stO j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ syScalars → y ∉ tpScalars → y ≠ nNy j → y ≠ nSy j →
        σ'.vars y = σ.vars y) → Ssw j σ') :
    AugSymCsrIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      nNy nSy soO stO aoO ajO dgO mtO (fun j A => augStInN io it nA j A) Srd Smp Ssw
      (fun j => symCom (arenaNames j).nN (io j) (it j) (qoY j) (qtY j) (dgY j)
        (soO j) (stO j) (nNy j) (nSy j))
      90 80 60 := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hArena, ⟨hInN, hnA⟩, hSrdσ, hcaL, hcoL, hSm, hSw⟩ := hσ
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩ := hcy j
  obtain ⟨hsz, hqoL, hqtL, hdgL, haoL, hajL, hdgOL, hmtL⟩ := hSrd j σ hSrdσ
  -- the two figures, and that they are words
  have henc : EncodesGraph x n G := hx.1
  have hnN : σ.vars (arenaNames j).nN = A.N := hArena.n_eq
  have hNn : A.N ≤ n := hArena.st.N_le_root
  have hxB : x.length + 1 < mcB q x := length_add_one_lt_mcB (three_le_length henc) hq
  have hlenx := henc.length_eq
  have hNB : A.N < mcB q x := by omega
  have hsq : n * n < mcB q x := sq_lt_mcB henc hq
  have hNsq : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
  have hBsq : A.N * A.N < mcB q x := by omega
  have h2a : 2 * arcCount (selChain (sel A.N) A.G R) ≤ A.N * A.N :=
    two_mul_arcCount_le_sq_orient _
  -- the exact lengths, from the descriptor and nothing else
  obtain ⟨hsoLen, hstLen⟩ := symCsrSizes_exact (io := io) (it := it) ⟨hInN, hnA⟩ hnN hsz
  -- the region, as the windowed CSR the transpose reads
  obtain ⟨off, tgt, hTr⟩ := trInCsr_of_inNCsr hInN
  rw [hnN] at hqoL hdgL haoL hdgOL
  rw [hnA] at hqtL hajL hmtL
  obtain ⟨σ', hrun, ⟨⟨hcsr', hnNy', hnSy'⟩, hfv, hfa, -, -⟩, hlen⟩ :=
    (specArrsLength (symCom_spec (B := mcB q x) (nN := (arenaNames j).nN)
      (io := io j) (it := it j) (qo := qoY j) (qt := qtY j) (dg := dgY j)
      (so := soO j) (st := stO j) (nNy := nNy j) (nSy := nSy j)
      (D := selChain (sel A.N) A.G R) (off := off) (tgt := tgt)
      (hnm j) (arenaNames_nN_notMem_syScalars j) (arenaNames_nN_notMem_tpScalars j)
      hy1 hy2 hy3 hBsq).frame).run
      ⟨hnN, hTr, hqoL, hqtL, hdgL, hsoLen, hstLen⟩
  -- the frame, in the shapes the transports consume
  have hfa' : ∀ b, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j → b ≠ stO j →
      σ'.arrs b = σ.arrs b :=
    fun b h1 h2 h3 h4 h5 => hfa b (not_mem_warrs_symCom h1 h2 h3 h4 h5)
  have hfv' : ∀ y, y ∉ syScalars → y ∉ tpScalars → y ≠ nNy j → y ≠ nSy j →
      σ'.vars y = σ.vars y :=
    fun y h1 h2 h3 h4 => hfv y (not_mem_wvars_symCom h1 h2 h3 h4)
  obtain ⟨ho1, ho2, ho3, ho4, ho5⟩ := harn j (arenaNames j).off (Or.inl rfl)
  obtain ⟨ht1, ht2, ht3, ht4, ht5⟩ := harn j (arenaNames j).tgt (Or.inr (Or.inl rfl))
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ :=
    harn j (arenaNames j).col (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ :=
    harn j (arenaNames j).up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨hh1, hh2, hh3, hh4, hh5⟩ :=
    harn j (arenaNames j).hist (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hvN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN :=
    hfv' _ (arenaNames_nN_notMem_syScalars j) (arenaNames_nN_notMem_tpScalars j)
      (Ne.symm hy4) (Ne.symm hy6)
  have hvS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS :=
    hfv' _ (arenaNames_nS_notMem_syScalars j) (arenaNames_nS_notMem_tpScalars j)
      (Ne.symm hy5) (Ne.symm hy7)
  refine ⟨σ', hrun.mono (by simp only [symK]; omega), ?_,
    ⟨2 * arcCount (selChain (sel A.N) A.G R), hcsr', hnNy', hnSy', hNB, by omega,
      symCsr_ns_le hcsr', ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact arenaStW_of_eq hArena hvN hvS (hfa' _ ho1 ho2 ho3 ho4 ho5)
      (hfa' _ ht1 ht2 ht3 ht4 ht5) (hfa' _ hc1 hc2 hc3 hc4 hc5)
      (hfa' _ hu1 hu2 hu3 hu4 hu5) (hfa' _ hh1 hh2 hh3 hh4 hh5)
  · rw [hlen (aoO j)]; exact haoL
  · rw [hlen (ajO j)]; exact hajL
  · rw [hlen (dgO j)]; exact hdgOL
  · rw [hlen (mtO j)]; exact hmtL
  · rw [hlen (ca j)]; exact hcaL
  · rw [hlen (co j)]; exact hcoL
  · exact hSmp j σ σ' hSm hfa' hfv'
  · exact hSsw j σ σ' hSw hfa' hfv'

/-! ### §10b The same discharge at the **windowed** orientation region

Finding 3 above records that this pass consumes the orientation region
through exactly two facts: `trInCsr_of_inNCsr`, i.e. only the *windowed*
`TrInCsr`, and the arc-count cell `nA j` (which is all
`symCsrSizes_exact` reads of it — `symCsrSizes_exact hst _ _` uses
`hst.2` and nothing else).  Both are clauses of `augStInNW`
(`SolveAugOrient.lean:1921`), so the discharge is available verbatim at
that region too.

This is not a convenience.  `augStInN` contains the *exact-length*
`InNCsr`, and `SolveAugRoundSeams`'s `augRd_augStInN_forces_constant`
shows that no round pass can carry it from `D` to `greedyStep rk D`:
IMP+ `store` is `List.set`, no run changes an array's length, and the
region pins that length to its orientation's arc count.  The rounds are
therefore stated at `augStInNW` — which is also what
`augBaseOrientIn_orCom` delivers — and
`covAugAdjSelIn_of_base_rounds_sym` takes **one** `AugSt` for all three
residuals.  Without this variant the base pass, the rounds and the
symmetrization have no common region and the augmentation does not
compose at all.

`augStInNW → augStInN` is *false* (the allocation exceeds the extent),
so this is a genuinely new statement and not a weakening of §10: the
two are incomparable preconditions, and §10 is left exactly as it
landed. -/

open Classical in
/-- **`AugSymCsrIn`, discharged at `augStInNW`** — `augSymCsrIn_symCom`
at the windowed orientation region, the one the base pass produces and
the rounds can carry.  Same program, same budget, same hypothesis
bundle; only the region changes. -/
theorem augSymCsrIn_symComW (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (io it nA : ℕ → String)
    (nNy nSy soO stO qoY qtY dgY : ℕ → String)
    (aoO ajO dgO mtO : ℕ → String)
    (Srd Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnm : ∀ j, SyNames (io j) (it j) (qoY j) (qtY j) (dgY j) (soO j) (stO j))
    (hcy : ∀ j, nNy j ∉ syScalars ∧ nSy j ∉ syScalars ∧ nSy j ≠ nNy j ∧
      nNy j ≠ (arenaNames j).nN ∧ nNy j ≠ (arenaNames j).nS ∧
      nSy j ≠ (arenaNames j).nN ∧ nSy j ≠ (arenaNames j).nS)
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ qoY j ∧ b ≠ qtY j ∧ b ≠ dgY j ∧ b ≠ soO j ∧ b ≠ stO j)
    (hSrd : ∀ j σ, Srd j σ →
      symCsrSizes nA soO stO j σ ∧
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (qoY j)).length ∧
      σ.vars (nA j) ≤ (σ.arrs (qtY j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (dgY j)).length ∧
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (aoO j)).length ∧
      2 * σ.vars (nA j) ≤ (σ.arrs (ajO j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (dgO j)).length ∧
      2 * σ.vars (nA j) ≤ (σ.arrs (mtO j)).length)
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j → b ≠ stO j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ syScalars → y ∉ tpScalars → y ≠ nNy j → y ≠ nSy j →
        σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j → b ≠ stO j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ syScalars → y ∉ tpScalars → y ≠ nNy j → y ≠ nSy j →
        σ'.vars y = σ.vars y) → Ssw j σ') :
    AugSymCsrIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      nNy nSy soO stO aoO ajO dgO mtO
      (fun j A => augStInNW io it nA j A) Srd Smp Ssw
      (fun j => symCom (arenaNames j).nN (io j) (it j) (qoY j) (qtY j) (dgY j)
        (soO j) (stO j) (nNy j) (nSy j))
      90 80 60 := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hArena, ⟨hTrE, -, hnA⟩, hSrdσ, hcaL, hcoL, hSm, hSw⟩ := hσ
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩ := hcy j
  obtain ⟨hsz, hqoL, hqtL, hdgL, haoL, hajL, hdgOL, hmtL⟩ := hSrd j σ hSrdσ
  -- the two figures, and that they are words
  have henc : EncodesGraph x n G := hx.1
  have hnN : σ.vars (arenaNames j).nN = A.N := hArena.n_eq
  have hNn : A.N ≤ n := hArena.st.N_le_root
  have hxB : x.length + 1 < mcB q x := length_add_one_lt_mcB (three_le_length henc) hq
  have hlenx := henc.length_eq
  have hNB : A.N < mcB q x := by omega
  have hsq : n * n < mcB q x := sq_lt_mcB henc hq
  have hNsq : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
  have hBsq : A.N * A.N < mcB q x := by omega
  have h2a : 2 * arcCount (selChain (sel A.N) A.G R) ≤ A.N * A.N :=
    two_mul_arcCount_le_sq_orient _
  -- the exact lengths, from the descriptor and the arc-count cell alone
  have hsoLen : (σ.arrs (soO j)).length = A.N + 1 := by rw [hsz.1, hnN]
  have hstLen : (σ.arrs (stO j)).length
      = 2 * arcCount (selChain (sel A.N) A.G R) := by rw [hsz.2, hnA]
  -- the region, as the windowed CSR the transpose reads: `augStInNW`'s
  -- own first clause, with no bridge in between
  obtain ⟨off, tgt, hTr⟩ := hTrE
  rw [hnN] at hqoL hdgL haoL hdgOL
  rw [hnA] at hqtL hajL hmtL
  obtain ⟨σ', hrun, ⟨⟨hcsr', hnNy', hnSy'⟩, hfv, hfa, -, -⟩, hlen⟩ :=
    (specArrsLength (symCom_spec (B := mcB q x) (nN := (arenaNames j).nN)
      (io := io j) (it := it j) (qo := qoY j) (qt := qtY j) (dg := dgY j)
      (so := soO j) (st := stO j) (nNy := nNy j) (nSy := nSy j)
      (D := selChain (sel A.N) A.G R) (off := off) (tgt := tgt)
      (hnm j) (arenaNames_nN_notMem_syScalars j) (arenaNames_nN_notMem_tpScalars j)
      hy1 hy2 hy3 hBsq).frame).run
      ⟨hnN, hTr, hqoL, hqtL, hdgL, hsoLen, hstLen⟩
  -- the frame, in the shapes the transports consume
  have hfa' : ∀ b, b ≠ qoY j → b ≠ qtY j → b ≠ dgY j → b ≠ soO j → b ≠ stO j →
      σ'.arrs b = σ.arrs b :=
    fun b h1 h2 h3 h4 h5 => hfa b (not_mem_warrs_symCom h1 h2 h3 h4 h5)
  have hfv' : ∀ y, y ∉ syScalars → y ∉ tpScalars → y ≠ nNy j → y ≠ nSy j →
      σ'.vars y = σ.vars y :=
    fun y h1 h2 h3 h4 => hfv y (not_mem_wvars_symCom h1 h2 h3 h4)
  obtain ⟨ho1, ho2, ho3, ho4, ho5⟩ := harn j (arenaNames j).off (Or.inl rfl)
  obtain ⟨ht1, ht2, ht3, ht4, ht5⟩ := harn j (arenaNames j).tgt (Or.inr (Or.inl rfl))
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ :=
    harn j (arenaNames j).col (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ :=
    harn j (arenaNames j).up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨hh1, hh2, hh3, hh4, hh5⟩ :=
    harn j (arenaNames j).hist (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hvN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN :=
    hfv' _ (arenaNames_nN_notMem_syScalars j) (arenaNames_nN_notMem_tpScalars j)
      (Ne.symm hy4) (Ne.symm hy6)
  have hvS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS :=
    hfv' _ (arenaNames_nS_notMem_syScalars j) (arenaNames_nS_notMem_tpScalars j)
      (Ne.symm hy5) (Ne.symm hy7)
  refine ⟨σ', hrun.mono (by simp only [symK]; omega), ?_,
    ⟨2 * arcCount (selChain (sel A.N) A.G R), hcsr', hnNy', hnSy', hNB, by omega,
      symCsr_ns_le hcsr', ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact arenaStW_of_eq hArena hvN hvS (hfa' _ ho1 ho2 ho3 ho4 ho5)
      (hfa' _ ht1 ht2 ht3 ht4 ht5) (hfa' _ hc1 hc2 hc3 hc4 hc5)
      (hfa' _ hu1 hu2 hu3 hu4 hu5) (hfa' _ hh1 hh2 hh3 hh4 hh5)
  · rw [hlen (aoO j)]; exact haoL
  · rw [hlen (ajO j)]; exact hajL
  · rw [hlen (dgO j)]; exact hdgOL
  · rw [hlen (mtO j)]; exact hmtL
  · rw [hlen (ca j)]; exact hcaL
  · rw [hlen (co j)]; exact hcoL
  · exact hSmp j σ σ' hSm hfa' hfv'
  · exact hSsw j σ σ' hSw hfa' hfv'

/-! ## §11 Nothing above is vacuous

`augSymCsrIn_symCom` leaves `Srd`, `Smp` and `Ssw` as parameters and
constrains them only through implications, so — like every residual of
this shape — it is *also* satisfied at `Srd := fun _ _ => False`, where
`AugSymCsrIn`'s own precondition is unsatisfiable and the discharge says
nothing.  This section is the check that the intended instantiation is
not that one, and it is the argument `SolveAugBaseFrame` §3 makes in
prose, here as a checked object.

Three things are exhibited.

1. **`symSrd`** — the descriptor `hSrd` asks for, read off `σ`.
   `symSrd_spec` is that it discharges `hSrd` definitionally, so
   nothing is weakened by naming it.
2. **`exists_symPre`** — the inhabitation that matters.  From **any**
   state carrying the arena (`ArenaStW`) and the orientation region
   (`augStInN`), the descriptor is established by allocating only the
   nine regions it names, leaving every scalar and every other array
   untouched; `ArenaStW` and `augStInN` therefore survive verbatim.  So
   `symSrd` is not merely inhabited — it is inhabited *jointly with the
   rest of `AugSymCsrIn`'s precondition*, which is exactly what a
   `False` descriptor cannot be, and it is why no fact beyond the two
   figure cells has to be supplied: the sizing is `A.N` and
   `arcCount D` read out of `σ` itself (`symCsrSizes_exact`).
3. **`augSymCsrIn_symCom_std`** — the whole hypothesis bundle
   (`hnm`, `hcy`, `harn`, `hSrd`, `hSmp`, `hSsw`) discharged at
   concrete `lv`-indexed names with `Srd := symSrd`, in the shape
   `fratCsrAt_fratCom`'s own `example` has.

`Smp` and `Ssw` need no witness of their own: both hypotheses are
frame-shaped — `Smp j σ` together with agreement off the written
regions implies `Smp j σ'` — so `fun _ _ => True` satisfies them and is
inhabited, which is what `augSymCsrIn_symCom_std` uses.  A descriptor
that is genuinely carried across the pass is F7's to choose; nothing in
§10 constrains it beyond that frame shape.

**The one obligation this section does not discharge, named exactly.**
`exists_symPre` is conditional on a state satisfying `ArenaStW` *and*
`augStInN io it nA j A (selChain (sel A.N) A.G R)` — that the machine
holds an in-neighbour CSR of the **final** orientation, with its arc
count in `nA j`.  That is not this leaf's to produce: it is
`AugRoundIn`'s postcondition at `i = R` (`SolveAugCompose` §3, carried
to `R` by `spec_comIter` inside `covAugAdjSelIn_of_base_rounds_sym`),
and it is a sibling's residual.  What is shown here is that the
*merge's own* demand adds nothing to it: given such a state, the
descriptor is free — nine allocations, no scalar touched, and no
constraint linking the two figures beyond the cells the state already
carries. -/

/-- **The rounds' descriptor this pass asks of its caller**, as a
predicate on `σ` alone: the exact sizing `symCsrSizes`
(`SolveAugBaseFrame` §3), the merge's three scratch allocations, and
the four regions the build that follows writes.  Every clause is read
against the arena's own carrier cell and the orientation region's own
arc-count cell, so none of it needs to name `A` or `D`. -/
def symSrd (nA soO stO qoY qtY dgY aoO ajO dgO mtO : ℕ → String)
    (j : ℕ) (σ : Env) : Prop :=
  symCsrSizes nA soO stO j σ ∧
    σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (qoY j)).length ∧
    σ.vars (nA j) ≤ (σ.arrs (qtY j)).length ∧
    σ.vars (arenaNames j).nN ≤ (σ.arrs (dgY j)).length ∧
    σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (aoO j)).length ∧
    2 * σ.vars (nA j) ≤ (σ.arrs (ajO j)).length ∧
    σ.vars (arenaNames j).nN ≤ (σ.arrs (dgO j)).length ∧
    2 * σ.vars (nA j) ≤ (σ.arrs (mtO j)).length

/-- `symSrd` discharges §10's `hSrd` on the nose — it *is* the
conjunction, so the discharge loses nothing by naming it. -/
theorem symSrd_spec (nA soO stO qoY qtY dgY aoO ajO dgO mtO : ℕ → String) :
    ∀ (j : ℕ) (σ : Env), symSrd nA soO stO qoY qtY dgY aoO ajO dgO mtO j σ →
      symCsrSizes nA soO stO j σ ∧
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (qoY j)).length ∧
      σ.vars (nA j) ≤ (σ.arrs (qtY j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (dgY j)).length ∧
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (aoO j)).length ∧
      2 * σ.vars (nA j) ≤ (σ.arrs (ajO j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (dgO j)).length ∧
      2 * σ.vars (nA j) ≤ (σ.arrs (mtO j)).length :=
  fun _ _ h => h

/-- **The descriptor is established by allocating its own regions and
nothing else.**  From an arbitrary state, the nine regions `symSrd`
names are given the two figures the state already carries — `soO` and
`stO` at the *exact* lengths `GraphCsr` demands, the other seven at or
above their bounds — while every scalar, the tapes, and every other
array are the state's own.  The two figure cells are untouched, so the
sizing is against the same `A.N` and `arcCount D` the rest of the
precondition pins. -/
theorem exists_symSrd {nA soO stO qoY qtY dgY aoO ajO dgO mtO : ℕ → String} {j : ℕ}
    (h1 : soO j ∉ [stO j, qoY j, qtY j, dgY j, aoO j, ajO j, dgO j, mtO j])
    (h2 : stO j ∉ [qoY j, qtY j, dgY j, aoO j, ajO j, dgO j, mtO j])
    (σ : Env) :
    ∃ σ', σ'.vars = σ.vars ∧
      (∀ b, b ≠ soO j → b ≠ stO j → b ≠ qoY j → b ≠ qtY j → b ≠ dgY j →
        b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j → σ'.arrs b = σ.arrs b) ∧
      symSrd nA soO stO qoY qtY dgY aoO ajO dgO mtO j σ' := by
  classical
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 h2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h1
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := h2
  obtain ⟨N, hN⟩ : ∃ N, σ.vars (arenaNames j).nN = N := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, σ.vars (nA j) = a := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : String → List ℕ, F = fun b =>
      if b = soO j then List.replicate (N + 1) 0
      else if b = stO j then List.replicate (2 * a) 0
      else if b = qoY j ∨ b = qtY j ∨ b = dgY j ∨ b = aoO j ∨ b = ajO j ∨
        b = dgO j ∨ b = mtO j then List.replicate (2 * a + N + 1) 0
      else σ.arrs b := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Env, τ = { σ with arrs := F } := ⟨_, rfl⟩
  have hFa : ∀ b, τ.arrs b = F b := fun b => by rw [hτ]
  have hFv : τ.vars = σ.vars := by rw [hτ]
  have g1 : F (soO j) = List.replicate (N + 1) 0 := by rw [hF]; simp
  have g2 : F (stO j) = List.replicate (2 * a) 0 := by rw [hF]; simp [Ne.symm e1]
  have g3 : F (qoY j) = List.replicate (2 * a + N + 1) 0 := by
    rw [hF]; simp [Ne.symm e2, Ne.symm f1]
  have g4 : F (qtY j) = List.replicate (2 * a + N + 1) 0 := by
    rw [hF]; simp [Ne.symm e3, Ne.symm f2]
  have g5 : F (dgY j) = List.replicate (2 * a + N + 1) 0 := by
    rw [hF]; simp [Ne.symm e4, Ne.symm f3]
  have g6 : F (aoO j) = List.replicate (2 * a + N + 1) 0 := by
    rw [hF]; simp [Ne.symm e5, Ne.symm f4]
  have g7 : F (ajO j) = List.replicate (2 * a + N + 1) 0 := by
    rw [hF]; simp [Ne.symm e6, Ne.symm f5]
  have g8 : F (dgO j) = List.replicate (2 * a + N + 1) 0 := by
    rw [hF]; simp [Ne.symm e7, Ne.symm f6]
  have g9 : F (mtO j) = List.replicate (2 * a + N + 1) 0 := by
    rw [hF]; simp [Ne.symm e8, Ne.symm f7]
  refine ⟨τ, hFv, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
    rw [hFa, hF]
    simp [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9]
  · rw [hFa, g1, List.length_replicate, hFv, hN]
  · rw [hFa, g2, List.length_replicate, hFv, ha]
  · rw [hFa, g3, List.length_replicate, hFv, hN]; omega
  · rw [hFa, g4, List.length_replicate, hFv, ha]; omega
  · rw [hFa, g5, List.length_replicate, hFv, hN]; omega
  · rw [hFa, g6, List.length_replicate, hFv, hN]; omega
  · rw [hFa, g7, List.length_replicate, hFv, ha]; omega
  · rw [hFa, g8, List.length_replicate, hFv, hN]; omega
  · rw [hFa, g9, List.length_replicate, hFv, ha]; omega

/-- **`AugSymCsrIn`'s precondition is satisfiable at `symSrd`.**  The
arena and the orientation region are carried across the reallocation
untouched — none of the nine regions is one of the arena's five arrays
or the region's own pair — so from any state holding them there is one
holding them *and* the descriptor.

The conclusion also returns the reallocation's own frame: every scalar
and every array outside the nine is the original's.  So `AugSymCsrIn`'s
two remaining precondition clauses — the `ca j` and `co j` allocations —
survive as well whenever those two regions are not among the nine, and
the precondition is satisfiable *in full*.

This is the anti-vacuity fact §10 needs: at `Srd := symSrd` the
discharge quantifies over a nonempty set of states whenever an arena
state carrying the orientation exists at all. -/
theorem exists_symPre {io it nA soO stO qoY qtY dgY aoO ajO dgO mtO : ℕ → String}
    {j : ℕ}
    (h1 : soO j ∉ [stO j, qoY j, qtY j, dgY j, aoO j, ajO j, dgO j, mtO j])
    (h2 : stO j ∉ [qoY j, qtY j, dgY j, aoO j, ajO j, dgO j, mtO j])
    (hkeep : ∀ b, b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
      b = (arenaNames j).col ∨ b = (arenaNames j).up ∨ b = (arenaNames j).hist ∨
      b = io j ∨ b = it j →
      b ≠ soO j ∧ b ≠ stO j ∧ b ≠ qoY j ∧ b ≠ qtY j ∧ b ≠ dgY j ∧
      b ≠ aoO j ∧ b ≠ ajO j ∧ b ≠ dgO j ∧ b ≠ mtO j)
    {Λ n₀ ℓp hb : ℕ} {A : Arena Λ n₀}
    {tab : Fin A.N → Fin ℓp → List (Fin A.N)} {D : Orientation A.N} {σ : Env}
    (hA : ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ)
    (hst : augStInN io it nA j A D σ) :
    ∃ σ', ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ' ∧
      augStInN io it nA j A D σ' ∧
      symSrd nA soO stO qoY qtY dgY aoO ajO dgO mtO j σ' ∧
      σ'.vars = σ.vars ∧
      (∀ b, b ≠ soO j → b ≠ stO j → b ≠ qoY j → b ≠ qtY j → b ≠ dgY j →
        b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j → σ'.arrs b = σ.arrs b) := by
  obtain ⟨σ', hv, hkeepArr, hsrd⟩ := exists_symSrd (nA := nA) h1 h2 σ
  have hgo := hkeep (arenaNames j).off (Or.inl rfl)
  have hgt := hkeep (arenaNames j).tgt (Or.inr (Or.inl rfl))
  have hgc := hkeep (arenaNames j).col (Or.inr (Or.inr (Or.inl rfl)))
  have hgu := hkeep (arenaNames j).up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hgh := hkeep (arenaNames j).hist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hgi := hkeep (io j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hgt' := hkeep (it j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  refine ⟨σ', ?_, ?_, hsrd, hv, hkeepArr⟩
  · exact arenaStW_of_eq hA (by rw [hv]) (by rw [hv])
      (hkeepArr _ hgo.1 hgo.2.1 hgo.2.2.1 hgo.2.2.2.1 hgo.2.2.2.2.1 hgo.2.2.2.2.2.1
        hgo.2.2.2.2.2.2.1 hgo.2.2.2.2.2.2.2.1 hgo.2.2.2.2.2.2.2.2)
      (hkeepArr _ hgt.1 hgt.2.1 hgt.2.2.1 hgt.2.2.2.1 hgt.2.2.2.2.1 hgt.2.2.2.2.2.1
        hgt.2.2.2.2.2.2.1 hgt.2.2.2.2.2.2.2.1 hgt.2.2.2.2.2.2.2.2)
      (hkeepArr _ hgc.1 hgc.2.1 hgc.2.2.1 hgc.2.2.2.1 hgc.2.2.2.2.1 hgc.2.2.2.2.2.1
        hgc.2.2.2.2.2.2.1 hgc.2.2.2.2.2.2.2.1 hgc.2.2.2.2.2.2.2.2)
      (hkeepArr _ hgu.1 hgu.2.1 hgu.2.2.1 hgu.2.2.2.1 hgu.2.2.2.2.1 hgu.2.2.2.2.2.1
        hgu.2.2.2.2.2.2.1 hgu.2.2.2.2.2.2.2.1 hgu.2.2.2.2.2.2.2.2)
      (hkeepArr _ hgh.1 hgh.2.1 hgh.2.2.1 hgh.2.2.2.1 hgh.2.2.2.2.1 hgh.2.2.2.2.2.1
        hgh.2.2.2.2.2.2.1 hgh.2.2.2.2.2.2.2.1 hgh.2.2.2.2.2.2.2.2)
  · obtain ⟨⟨off, tgt, hc, h0, hnd, hR⟩, hcell⟩ := hst
    refine ⟨⟨off, tgt, hc.of_eq ?_ ?_, h0, hnd, hR⟩, by rw [hv]; exact hcell⟩
    · exact hkeepArr _ hgi.1 hgi.2.1 hgi.2.2.1 hgi.2.2.2.1 hgi.2.2.2.2.1
        hgi.2.2.2.2.2.1 hgi.2.2.2.2.2.2.1 hgi.2.2.2.2.2.2.2.1 hgi.2.2.2.2.2.2.2.2
    · exact hkeepArr _ hgt'.1 hgt'.2.1 hgt'.2.2.1 hgt'.2.2.2.1 hgt'.2.2.2.2.1
        hgt'.2.2.2.2.2.1 hgt'.2.2.2.2.2.2.1 hgt'.2.2.2.2.2.2.2.1 hgt'.2.2.2.2.2.2.2.2

/-! ### The concrete instantiation

Fourteen `lv`-indexed names on distinct four-character bases, so that
every disequality the bundle asks for is `lv_ne_of_base_ne` or
`lv_ne_fixed` on the bases and nothing else — the shape
`fratCsrAt_fratCom`'s `example` has, at a family that is per-level as a
real assembly's would be. -/

/-- The orientation region's offsets. -/
abbrev symIo (j : ℕ) : String := lv "zi.o" j
/-- The orientation region's targets. -/
abbrev symIt (j : ℕ) : String := lv "zi.t" j
/-- The orientation region's arc-count cell. -/
abbrev symNA (j : ℕ) : String := lv "zn.a" j
/-- The merged carrier cell. -/
abbrev symNNy (j : ℕ) : String := lv "zn.n" j
/-- The merged slot-count cell. -/
abbrev symNSy (j : ℕ) : String := lv "zn.s" j
/-- The merged offsets. -/
abbrev symSoO (j : ℕ) : String := lv "zs.o" j
/-- The merged targets. -/
abbrev symStO (j : ℕ) : String := lv "zs.t" j
/-- The transpose's offsets. -/
abbrev symQoY (j : ℕ) : String := lv "zq.o" j
/-- The transpose's targets. -/
abbrev symQtY (j : ℕ) : String := lv "zq.t" j
/-- The counting sort's degrees. -/
abbrev symDgY (j : ℕ) : String := lv "zd.g" j
/-- The build's adjacency offsets. -/
abbrev symAoO (j : ℕ) : String := lv "za.o" j
/-- The build's adjacency targets. -/
abbrev symAjO (j : ℕ) : String := lv "za.j" j
/-- The build's degrees. -/
abbrev symDgO (j : ℕ) : String := lv "zd.o" j
/-- The build's mates. -/
abbrev symMtO (j : ℕ) : String := lv "zm.t" j

/-- The concrete descriptor: `symSrd` at the fourteen names. -/
abbrev symSrdStd : ℕ → Env → Prop :=
  symSrd symNA symSoO symStO symQoY symQtY symDgY symAoO symAjO symDgO symMtO

theorem symNames_std (j : ℕ) :
    SyNames (symIo j) (symIt j) (symQoY j) (symQtY j) (symDgY j)
      (symSoO j) (symStO j) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;> exact lv_ne_of_base_ne (by decide) (by decide) j j

/-- The descriptor is inhabited jointly with the arena and the
orientation region, at the concrete names: `exists_symPre`'s
hypotheses are all base disequalities. -/
theorem exists_symPre_std {j Λ n₀ ℓp hb : ℕ} {A : Arena Λ n₀}
    {tab : Fin A.N → Fin ℓp → List (Fin A.N)} {D : Orientation A.N} {σ : Env}
    (hA : ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ)
    (hst : augStInN symIo symIt symNA j A D σ) :
    ∃ σ', ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ' ∧
      augStInN symIo symIt symNA j A D σ' ∧ symSrdStd j σ' ∧
      σ'.vars = σ.vars ∧
      (∀ b, b ≠ symSoO j → b ≠ symStO j → b ≠ symQoY j → b ≠ symQtY j →
        b ≠ symDgY j → b ≠ symAoO j → b ≠ symAjO j → b ≠ symDgO j →
        b ≠ symMtO j → σ'.arrs b = σ.arrs b) := by
  refine exists_symPre (io := symIo) (it := symIt) ?_ ?_ ?_ hA hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact lv_ne_of_base_ne (by decide) (by decide) j j
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact lv_ne_of_base_ne (by decide) (by decide) j j
  · rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j⟩

open Classical in
/-- **The whole hypothesis bundle, discharged at concrete names.**  The
descriptor is `symSrd` — inhabited jointly with the rest of the
precondition by `exists_symPre_std` — and the two transported
descriptors are `True`, whose frame hypotheses hold by `trivial`.  So
§10 is not a statement about an empty precondition. -/
theorem augSymCsrIn_symCom_std (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (hq : 1 ≤ q) :
    AugSymCsrIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      symNNy symNSy symSoO symStO symAoO symAjO symDgO symMtO
      (fun j A => augStInN symIo symIt symNA j A)
      symSrdStd (fun _ _ => True) (fun _ _ => True)
      (fun j => symCom (arenaNames j).nN (symIo j) (symIt j) (symQoY j) (symQtY j)
        (symDgY j) (symSoO j) (symStO j) (symNNy j) (symNSy j))
      90 80 60 := by
  refine augSymCsrIn_symCom C hC φ sel R G c w q ℓp htabF hbf Adm ca co
    symIo symIt symNA symNNy symNSy symSoO symStO symQoY symQtY symDgY
    symAoO symAjO symDgO symMtO _ _ _ hq symNames_std ?_ ?_
    (symSrd_spec _ _ _ _ _ _ _ _ _ _) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial)
  · intro j
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [syScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lv_ne_fixed (by decide) (by decide) j
    · simp only [syScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lv_ne_fixed (by decide) (by decide) j
    all_goals exact lv_ne_of_base_ne (by decide) (by decide) j j
  · rintro j b (rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j⟩

/-! ### The windowed region is inhabited jointly too

§10b's discharge is at `augStInNW`, so its anti-vacuity witness has to
be as well.  Nothing new is needed: `augStInNW` is rebuilt from a
`TrInCsr` and the arc-count cell by `inNCsr_winA_of_trInCsr`
(`SolveAugOrient` §1), so the reallocation only has to carry the pair
`(io j, it j)` across — which it does, since neither is one of the nine
regions. -/

/-- `TrInCsr` transports along its own two regions: every clause naming
the state names `σ.arrs o` or `σ.arrs t` and nothing else. -/
theorem symTrInCsr_of_eq {o t : String} {m ns : ℕ} {D : Orientation m}
    {off tgt : ℕ → ℕ} {σ σ' : Env} (h : TrInCsr o t D ns off tgt σ)
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t) :
    TrInCsr o t D ns off tgt σ' where
  zero := h.zero
  step := h.step
  last := h.last
  offLen := by rw [ho]; exact h.offLen
  tgtLen := by rw [ht]; exact h.tgtLen
  offGet := by rw [ho]; exact h.offGet
  tgtGet := by rw [ht]; exact h.tgtGet
  tgtLt := h.tgtLt
  sound := h.sound
  complete := h.complete
  inj := h.inj

/-- **The windowed orientation region from a `TrInCsr` and the cell.**
Both of `augStInNW`'s first two clauses come from the same windowed
CSR — the second through `inNCsr_winA_of_trInCsr` — so a producer never
has to build the exact-length reading by hand. -/
theorem augStInNW_of_trInCsr {io it nA : ℕ → String} {j : ℕ} {Λ n₀ : ℕ}
    {A : Arena Λ n₀} {D : Orientation A.N} {off tgt : ℕ → ℕ} {σ : Env}
    (hto : it j ≠ io j)
    (h : TrInCsr (io j) (it j) D (arcCount D) off tgt σ)
    (hc : σ.vars (nA j) = arcCount D) : augStInNW io it nA j A D σ :=
  ⟨⟨off, tgt, h⟩, inNCsr_winA_of_trInCsr hto h, hc⟩

/-- **`AugSymCsrIn`'s precondition at `augStInNW` is satisfiable at
`symSrd`** — `exists_symPre` for the windowed region. -/
theorem exists_symPreW {io it nA soO stO qoY qtY dgY aoO ajO dgO mtO : ℕ → String}
    {j : ℕ} (hto : it j ≠ io j)
    (h1 : soO j ∉ [stO j, qoY j, qtY j, dgY j, aoO j, ajO j, dgO j, mtO j])
    (h2 : stO j ∉ [qoY j, qtY j, dgY j, aoO j, ajO j, dgO j, mtO j])
    (hkeep : ∀ b, b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
      b = (arenaNames j).col ∨ b = (arenaNames j).up ∨ b = (arenaNames j).hist ∨
      b = io j ∨ b = it j →
      b ≠ soO j ∧ b ≠ stO j ∧ b ≠ qoY j ∧ b ≠ qtY j ∧ b ≠ dgY j ∧
      b ≠ aoO j ∧ b ≠ ajO j ∧ b ≠ dgO j ∧ b ≠ mtO j)
    {Λ n₀ ℓp hb : ℕ} {A : Arena Λ n₀}
    {tab : Fin A.N → Fin ℓp → List (Fin A.N)} {D : Orientation A.N} {σ : Env}
    (hA : ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ)
    (hst : augStInNW io it nA j A D σ) :
    ∃ σ', ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ' ∧
      augStInNW io it nA j A D σ' ∧
      symSrd nA soO stO qoY qtY dgY aoO ajO dgO mtO j σ' ∧
      σ'.vars = σ.vars ∧
      (∀ b, b ≠ soO j → b ≠ stO j → b ≠ qoY j → b ≠ qtY j → b ≠ dgY j →
        b ≠ aoO j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j → σ'.arrs b = σ.arrs b) := by
  obtain ⟨σ', hv, hkeepArr, hsrd⟩ := exists_symSrd (nA := nA) h1 h2 σ
  have hgo := hkeep (arenaNames j).off (Or.inl rfl)
  have hgt := hkeep (arenaNames j).tgt (Or.inr (Or.inl rfl))
  have hgc := hkeep (arenaNames j).col (Or.inr (Or.inr (Or.inl rfl)))
  have hgu := hkeep (arenaNames j).up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hgh := hkeep (arenaNames j).hist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hgi := hkeep (io j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hgt' := hkeep (it j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  refine ⟨σ', ?_, ?_, hsrd, hv, hkeepArr⟩
  · exact arenaStW_of_eq hA (by rw [hv]) (by rw [hv])
      (hkeepArr _ hgo.1 hgo.2.1 hgo.2.2.1 hgo.2.2.2.1 hgo.2.2.2.2.1 hgo.2.2.2.2.2.1
        hgo.2.2.2.2.2.2.1 hgo.2.2.2.2.2.2.2.1 hgo.2.2.2.2.2.2.2.2)
      (hkeepArr _ hgt.1 hgt.2.1 hgt.2.2.1 hgt.2.2.2.1 hgt.2.2.2.2.1 hgt.2.2.2.2.2.1
        hgt.2.2.2.2.2.2.1 hgt.2.2.2.2.2.2.2.1 hgt.2.2.2.2.2.2.2.2)
      (hkeepArr _ hgc.1 hgc.2.1 hgc.2.2.1 hgc.2.2.2.1 hgc.2.2.2.2.1 hgc.2.2.2.2.2.1
        hgc.2.2.2.2.2.2.1 hgc.2.2.2.2.2.2.2.1 hgc.2.2.2.2.2.2.2.2)
      (hkeepArr _ hgu.1 hgu.2.1 hgu.2.2.1 hgu.2.2.2.1 hgu.2.2.2.2.1 hgu.2.2.2.2.2.1
        hgu.2.2.2.2.2.2.1 hgu.2.2.2.2.2.2.2.1 hgu.2.2.2.2.2.2.2.2)
      (hkeepArr _ hgh.1 hgh.2.1 hgh.2.2.1 hgh.2.2.2.1 hgh.2.2.2.2.1 hgh.2.2.2.2.2.1
        hgh.2.2.2.2.2.2.1 hgh.2.2.2.2.2.2.2.1 hgh.2.2.2.2.2.2.2.2)
  · obtain ⟨⟨off, tgt, hTr⟩, -, hcell⟩ := hst
    refine augStInNW_of_trInCsr hto (symTrInCsr_of_eq hTr ?_ ?_) (by rw [hv]; exact hcell)
    · exact hkeepArr _ hgi.1 hgi.2.1 hgi.2.2.1 hgi.2.2.2.1 hgi.2.2.2.2.1
        hgi.2.2.2.2.2.1 hgi.2.2.2.2.2.2.1 hgi.2.2.2.2.2.2.2.1 hgi.2.2.2.2.2.2.2.2
    · exact hkeepArr _ hgt'.1 hgt'.2.1 hgt'.2.2.1 hgt'.2.2.2.1 hgt'.2.2.2.2.1
        hgt'.2.2.2.2.2.1 hgt'.2.2.2.2.2.2.1 hgt'.2.2.2.2.2.2.2.1 hgt'.2.2.2.2.2.2.2.2

/-- The windowed region is inhabited jointly with the descriptor at the
concrete names. -/
theorem exists_symPreW_std {j Λ n₀ ℓp hb : ℕ} {A : Arena Λ n₀}
    {tab : Fin A.N → Fin ℓp → List (Fin A.N)} {D : Orientation A.N} {σ : Env}
    (hA : ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ)
    (hst : augStInNW symIo symIt symNA j A D σ) :
    ∃ σ', ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ' ∧
      augStInNW symIo symIt symNA j A D σ' ∧ symSrdStd j σ' ∧
      σ'.vars = σ.vars ∧
      (∀ b, b ≠ symSoO j → b ≠ symStO j → b ≠ symQoY j → b ≠ symQtY j →
        b ≠ symDgY j → b ≠ symAoO j → b ≠ symAjO j → b ≠ symDgO j →
        b ≠ symMtO j → σ'.arrs b = σ.arrs b) := by
  refine exists_symPreW (io := symIo) (it := symIt)
    (lv_ne_of_base_ne (by decide) (by decide) j j) ?_ ?_ ?_ hA hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact lv_ne_of_base_ne (by decide) (by decide) j j
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact lv_ne_of_base_ne (by decide) (by decide) j j
  · rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j⟩

open Classical in
/-- **§10b's hypothesis bundle, discharged at the concrete names** —
`augSymCsrIn_symCom_std` at the windowed region. -/
theorem augSymCsrIn_symComW_std (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (hq : 1 ≤ q) :
    AugSymCsrIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      symNNy symNSy symSoO symStO symAoO symAjO symDgO symMtO
      (fun j A => augStInNW symIo symIt symNA j A)
      symSrdStd (fun _ _ => True) (fun _ _ => True)
      (fun j => symCom (arenaNames j).nN (symIo j) (symIt j) (symQoY j) (symQtY j)
        (symDgY j) (symSoO j) (symStO j) (symNNy j) (symNSy j))
      90 80 60 := by
  refine augSymCsrIn_symComW C hC φ sel R G c w q ℓp htabF hbf Adm ca co
    symIo symIt symNA symNNy symNSy symSoO symStO symQoY symQtY symDgY
    symAoO symAjO symDgO symMtO _ _ _ hq symNames_std ?_ ?_
    (symSrd_spec _ _ _ _ _ _ _ _ _ _) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial)
  · intro j
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [syScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lv_ne_fixed (by decide) (by decide) j
    · simp only [syScalars, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lv_ne_fixed (by decide) (by decide) j
    all_goals exact lv_ne_of_base_ne (by decide) (by decide) j j
  · rintro j b (rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j,
        lv_ne_of_base_ne (by decide) (by decide) j j⟩

/-! ## §12 Axiom audit

§1–§9 rest on the three standard axioms alone.  §10's discharge quotes
`Headline.headlineSetup` in its statement and therefore — exactly like
the landed `augBaseAdjIn_bldAdjCom` and `augSymIn_of_symCsr_build` it
composes with — additionally carries Lax12's endorsed
`uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms trInCsr_of_inNCsr

#print axioms two_mul_arcCount_le_sq_orient

#print axioms graphCsr_of_symRows

#print axioms symComW_spec

#print axioms symCom_spec

#print axioms augSymCsrIn_symCom

#print axioms exists_symPre

#print axioms exists_symPre_std

#print axioms augSymCsrIn_symCom_std

#print axioms augStInNW_of_trInCsr

#print axioms augSymCsrIn_symComW

#print axioms exists_symPreW

#print axioms exists_symPreW_std

#print axioms augSymCsrIn_symComW_std

end Lax3Proofs.Prog
