import Lax3Proofs.SolveAugBaseFrame
import Lax3Proofs.SolveAugStepEmit

/-!
# F6c12-5b — `AugRoundIn`'s fraternal peel

**The leaf.** `StepEmitIn` (`SolveAugEmit.lean:844`) takes its ranking as
an *arbitrary* `rk`, through `RankAt sg rk`. `AugRoundIn`
(`SolveAugCompose.lean:391`) asks its round to land at
`greedyStep (selRank (sel A.N) (fratGraph (selChain … i))) …`. Feeding
the one into the other therefore needs the **selection rank of the
fraternal graph**, in the array `StepEmitIn` reads — and nothing landed
computed it. Every peel in the package so far
(`bucketPeelCom`, `covSelPeelIn_bucketPeelCom`, `augBasePeelIn`) peels
the *arena's own* graph off a `DelAdjSt`; the round instead holds
`fratGraph D` as the `CsrPrefix fo ft (fratGraph D) nf` that
`fratCsrAt_fratCom` (`SolveAugFratCom.lean:2054`) produces. This file
is that bridge.

**No new peel.** The landed peel is generic in the graph — only its
*input region* is specialised — so the leaf composes two landed
programs and writes no loop of its own:

```
fratPeelCom = bldAdjCom  (the CSR → deletable-adjacency build)
            ; bucketPeelCom  (the linear bucket peel)
```

The `winA` trap that forces `covAdjBuildIn_bldCom`'s route elsewhere
does not apply: the fraternal region is *not* the arena's CSR, so the
build may be run on fresh arrays. The one adjustment is that
`AdjBuildAt`'s `GraphCsr` clause pins the two allocations' lengths
*exactly* while `CsrPrefix` only bounds them, so §2 goes through
`bldAdj_spec`'s `SrcCsr` precondition instead — `srcCsr_of_graphCsr` is
already stated at a window, which is precisely what `CsrPrefix` is.

**The budget** is `fratPeelK n nf = 394·n + 176·nf + 64`, and the
identity that prices it is `nf = slotCount (fratGraph D)`
(`graphCsr_ns_eq_slotCount`): the fraternal CSR's slot count *is* the
figure the peel is charged at, so the peel's `118·slotCount` term is
`118·nf` with nothing to estimate. With `nf ≤ fratPairCount D` (the
last clause of `FratCsrAt`'s postcondition) the whole cost sits inside
`augRoundBudget`'s `kn` and **`kf`** terms — `fratPeelK_le_augRoundBudget`
— so the `R + 1` repetitions of the pass do not multiply. No `n * n`
appears in the *time*.

**What remains.** Two things, both for the composer of `AugRoundIn`.

* The scratch this pass asks for is `n` rank cells, `n` bucket tops and
  `n * n + n` bucket cells — the peel's cell block is quadratic in
  *space* (`covSelPeelIn_bucketPeelCom` says the same of the arena
  peel). The round already carries an `n * n` region — `FratCsrAt`'s
  mark matrix `mk`, restored to all-zero by `fratCsrAt_fratCom` — but
  `mk` is `n * n`, not `n * n + n`, so the composer must either widen it
  or name a separate allocation. Nothing here can supply it: an
  allocation clause binds whoever establishes the precondition.
* The word bound `n + n * n + 1 < B` is the peel's, not this file's
  invention; at an admissible input it comes from `EncodesGraph` and
  `1 ≤ q` exactly as in `covSelPeelIn_bucketPeelCom` (`sq_lt_mcB` is
  the same fact one step weaker).

The `≤`-sized allocations of `nf` slots are stated here, and `nf` is
*derived* to be at most `n * n` (`offF_le_sq` through the `SrcCsr`), so
the contract does not ask its caller for a second word bound.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Augmentation (Orientation fratGraph)
open Lax3Proofs.CoverRoutine (MinDegSel selRank selPerm)

/-! ## §1 The names the pass keeps apart

Nine array names — the two the fraternal CSR lives in, the four the
build writes, and the three the peel writes — and two scalar cells. The
build and the peel overlap on `dg` and `mt` by design (the peel
recomputes both), so the only requirement is that the nine be pairwise
distinct and the two cells lie outside the eighteen scratch scalars. -/

/-- The nine array names the pass mentions, in one list. -/
def fpArrs (fo ft ao aj dg mt sg tp sk : String) : List String :=
  [fo, ft, ao, aj, dg, mt, sg, tp, sk]

/-- **The name side condition**: the nine regions are pairwise
distinct. `CsrPrefix` needs `fo ≠ ft` (it cuts two different windows),
`bldAdj_spec` needs its five writable names apart from the two it
reads, and `bucketPeelCom_spec` needs `Distinct6` — all of which this
one clause supplies. -/
structure FpNames (fo ft ao aj dg mt sg tp sk : String) : Prop where
  /-- The nine regions are pairwise distinct. -/
  nodup : (fpArrs fo ft ao aj dg mt sg tp sk).Nodup

/-- The eighteen scalars the two passes assign to: the build's six and
the peel's twelve. -/
def fpScalars : List String :=
  ["bd.i", "bd.j", "bd.u", "bd.w", "bd.p", "bd.q",
    "bk.n", "bk.i", "bk.u", "bk.m", "bk.t", "bk.z", "bk.c", "bk.r", "bk.f",
    "bk.v", "bk.w", "bk.d"]

/-- **The cell side condition**: the two figure cells survive the pass,
so a composer still reads `n` and `nf` out of them afterwards. -/
structure FpCells (nN nF : String) : Prop where
  /-- The carrier cell is none of the pass's scratch. -/
  nN_notMem : nN ∉ fpScalars
  /-- Nor is the slot-count cell. -/
  nF_notMem : nF ∉ fpScalars

section Names

variable {fo ft ao aj dg mt sg tp sk : String}

/-- The nine names, unpacked into the thirty-six disequalities the two
landed contracts ask for. -/
private theorem fpNames_ne (h : FpNames fo ft ao aj dg mt sg tp sk) :
    (fo ≠ ft ∧ fo ≠ ao ∧ fo ≠ aj ∧ fo ≠ dg ∧ fo ≠ mt ∧ fo ≠ sg ∧ fo ≠ tp ∧ fo ≠ sk) ∧
    (ft ≠ ao ∧ ft ≠ aj ∧ ft ≠ dg ∧ ft ≠ mt ∧ ft ≠ sg ∧ ft ≠ tp ∧ ft ≠ sk) ∧
    (ao ≠ aj ∧ ao ≠ dg ∧ ao ≠ mt ∧ ao ≠ sg ∧ ao ≠ tp ∧ ao ≠ sk) ∧
    (aj ≠ dg ∧ aj ≠ mt ∧ aj ≠ sg ∧ aj ≠ tp ∧ aj ≠ sk) ∧
    (dg ≠ mt ∧ dg ≠ sg ∧ dg ≠ tp ∧ dg ≠ sk) ∧
    (mt ≠ sg ∧ mt ≠ tp ∧ mt ≠ sk) ∧ (sg ≠ tp ∧ sg ≠ sk) ∧ tp ≠ sk := by
  have hnd := h.nodup
  simp only [fpArrs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  tauto

/-- The peel's six-way distinctness. -/
theorem FpNames.distinct6 (h : FpNames fo ft ao aj dg mt sg tp sk) :
    Distinct6 ao mt sg dg tp sk := by
  obtain ⟨-, -, ⟨-, hoD, hoM, hoS, hoT, hoK⟩, -, ⟨hDM, hDS, hDT, hDK⟩,
    ⟨hMS, hMT, hMK⟩, ⟨hST, hSK⟩, hTK⟩ := fpNames_ne h
  exact ⟨hoM, hoS, hoD, hoT, hoK, hMS, Ne.symm hDM, hMT, hMK, Ne.symm hDS,
    hST, hSK, hDT, hDK, hTK⟩

/-- The build's ten-plus-fifteen distinctness, with the peel's cell
block standing in for the (unused) order region. -/
theorem FpNames.bldNames (h : FpNames fo ft ao aj dg mt sg tp sk) :
    BldNames fo ft sg ao aj dg mt sk := by
  obtain ⟨⟨-, hFo, hFj, hFd, hFm, hFs, -, hFk⟩,
    ⟨hTo, hTj, hTd, hTm, hTs, -, hTk⟩,
    ⟨hoJ, hoD, hoM, hoS, -, hoK⟩, ⟨hjD, hjM, hjS, -, hjK⟩,
    ⟨hDM, hDS, -, hDK⟩, ⟨hMS, -, hMK⟩, ⟨-, hSK⟩, -⟩ := fpNames_ne h
  exact ⟨hoJ, hoD, hoM, hoK, hjD, hjM, hjK, hDM, hDK, hMK, Ne.symm hFo,
    Ne.symm hTo, hoS, Ne.symm hFj, Ne.symm hTj, hjS, Ne.symm hFd, Ne.symm hTd,
    hDS, Ne.symm hFm, Ne.symm hTm, hMS, Ne.symm hFk, Ne.symm hTk, Ne.symm hSK⟩

/-- The row region is none of the five the peel touches. -/
theorem FpNames.aj_ne (h : FpNames fo ft ao aj dg mt sg tp sk) :
    aj ≠ ao ∧ aj ≠ mt ∧ aj ≠ sg ∧ aj ≠ dg ∧ aj ≠ tp ∧ aj ≠ sk := by
  obtain ⟨-, -, ⟨hoJ, -⟩, ⟨hjD, hjM, hjS, hjT, hjK⟩, -⟩ := fpNames_ne h
  exact ⟨Ne.symm hoJ, hjM, hjS, hjD, hjT, hjK⟩

/-- The fraternal CSR's two windows are unambiguous. -/
theorem FpNames.fo_ft (h : FpNames fo ft ao aj dg mt sg tp sk) : fo ≠ ft :=
  (fpNames_ne h).1.1

/-- The fraternal CSR is untouched: neither pass writes either of its
two regions. -/
theorem FpNames.csr_ne (h : FpNames fo ft ao aj dg mt sg tp sk) :
    (fo ≠ ao ∧ fo ≠ aj ∧ fo ≠ dg ∧ fo ≠ mt ∧ fo ≠ sg ∧ fo ≠ tp ∧ fo ≠ sk) ∧
      (ft ≠ ao ∧ ft ≠ aj ∧ ft ≠ dg ∧ ft ≠ mt ∧ ft ≠ sg ∧ ft ≠ tp ∧ ft ≠ sk) := by
  obtain ⟨⟨-, hf⟩, ht, -⟩ := fpNames_ne h
  exact ⟨hf, ht⟩

end Names

section Cells

variable {nN nF : String}

/-- The build's six scratch scalars, from the eighteen. -/
theorem FpCells.bld (h : FpCells nN nF) : BldCells nN nF := by
  have h1 := h.nN_notMem
  have h2 := h.nF_notMem
  simp only [fpScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 h2
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
    h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2.1⟩

end Cells

/-- A name outside the eighteen is outside each of them. -/
private theorem fpScalars_ne {y : String} (h : y ∉ fpScalars) :
    (y ≠ "bd.i" ∧ y ≠ "bd.j" ∧ y ≠ "bd.u" ∧ y ≠ "bd.w" ∧ y ≠ "bd.p" ∧ y ≠ "bd.q") ∧
      (y ≠ "bk.n" ∧ y ≠ "bk.i" ∧ y ≠ "bk.u" ∧ y ≠ "bk.m" ∧ y ≠ "bk.t" ∧ y ≠ "bk.z" ∧
        y ≠ "bk.c" ∧ y ≠ "bk.r" ∧ y ≠ "bk.f" ∧ y ≠ "bk.v" ∧ y ≠ "bk.w" ∧
        y ≠ "bk.d") := by
  simp only [fpScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  tauto

/-! ## §2 The windowed CSR, read as a source CSR

`CsrPrefix` is `GraphCsr` at the truncation `winA`, and
`srcCsr_of_graphCsr` is already stated across a window — it asks only
that the allocation agree with the exact-length state below the two
extents, which a `take` does by construction. This is the whole of the
shape mismatch the leaf exists for. -/

/-- **The fraternal CSR feeds the build.** From the windowed prefix the
fraternal pass delivers, the `SrcCsr` package `bldAdj_spec` consumes —
offsets that are the degree sums, rows that enumerate the
neighbourhoods without repetition. -/
theorem srcCsr_of_csrPrefix {fo ft : String} {n nf : ℕ} {G : SimpleGraph (Fin n)}
    {σ : Env} (h : CsrPrefix fo ft G nf σ) (hne : fo ≠ ft) :
    ∃ off tgt : ℕ → ℕ, SrcCsr fo ft G nf off tgt σ := by
  obtain ⟨hoL, htL, hg⟩ := h
  have hwo : (fun b => if b = fo then some (n + 1) else if b = ft then some nf else none)
      fo = some (n + 1) := by simp
  have hwt : (fun b => if b = fo then some (n + 1) else if b = ft then some nf else none)
      ft = some nf := by simp [Ne.symm hne]
  refine srcCsr_of_graphCsr hg hoL htL ?_ ?_
  · intro i hi
    rw [arrs_winA_some hwo σ, List.getElem?_take_of_lt (by omega)]
  · intro p hp
    rw [arrs_winA_some hwt σ, List.getElem?_take_of_lt hp]

/-- Reading a cell inside the allocation. -/
private theorem getElem?_of_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- **`RankArr` is `RankAt` at the selection rank.** The peel leaves the
permutation `selPerm`; `StepEmitIn` reads the function `selRank`. They
are the same datum — `selPerm_val` is `rfl` — and the two region
predicates differ only in `getD` versus `[·]?`, which the allocation
clause reconciles. -/
theorem rankAt_of_rankArr {sg : String} {n : ℕ} {F : SimpleGraph (Fin n)}
    {sel : MinDegSel n} {σ : Env} (h : RankArr sg (selPerm sel F) σ) :
    RankAt sg (selRank sel F) σ := by
  obtain ⟨hlen, hget⟩ := h
  refine ⟨hlen, fun v => ?_⟩
  rw [getElem?_of_getD (lt_of_lt_of_le v.isLt hlen), hget v]
  rfl

/-! ## §3 The pass, and its contract -/

/-- **The fraternal peel**: build the deletable adjacency region of
`fratGraph D` from the fraternal CSR, then run the linear bucket peel on
it. Both halves are landed programs; this file adds no loop. -/
def fratPeelCom (nN nF fo ft ao aj dg mt sg tp sk : String) : Com :=
  .seq (bldAdjCom nN nF fo ft ao aj dg mt)
    (bucketPeelCom ao aj dg mt sg tp sk nN)

/-- **The pass's budget** at `(n, nf)`: the build's `81·n + 58·nf + 24`
and the peel's `313·n + 118·nf + 40`, the latter read at
`nf = slotCount (fratGraph D)`. Linear in both figures — no `n * n`. -/
def fratPeelK (n nf : ℕ) : ℕ := 394 * n + 176 * nf + 64

/-- **`FratPeelAt`: the fraternal peel as a contract.** From

* the fraternal CSR in `(fo, ft)`, in the windowed form `CsrPrefix`
  that `fratCsrAt_fratCom` delivers, with its slot count in `nF` and
  the carrier in `nN`;
* the build's three raw allocations `(ao, aj, mt)` and the degrees `dg`;
* the peel's rank region `sg`, bucket tops `tp` and cell block `sk`,

leave in `sg` **the selection rank of `fratGraph D`** —
`RankAt sg (selRank (bucketSel n) (fratGraph D))`, the exact predicate
`StepEmitIn` consumes — with the fraternal CSR itself unchanged, every
array length preserved, and nothing but the seven working regions and
the eighteen scratch scalars touched.

The only word bound asked for is the peel's own,
`n + n * n + 1 < B`; `nf < B` is *derived* (`offF_le_sq`), not
requested. -/
def FratPeelAt (B : ℕ) (nN nF fo ft ao aj dg mt sg tp sk : String) (fpC : Com)
    (kp : ℕ → ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} (D : Orientation n) (nf : ℕ),
    Spec B
      (fun σ => CsrPrefix fo ft (fratGraph D) nf σ ∧
        σ.vars nN = n ∧ σ.vars nF = nf ∧
        n + n * n + 1 < B ∧
        n + 1 ≤ (σ.arrs ao).length ∧ nf ≤ (σ.arrs aj).length ∧
        n ≤ (σ.arrs dg).length ∧ nf ≤ (σ.arrs mt).length ∧
        n ≤ (σ.arrs sg).length ∧ n ≤ (σ.arrs tp).length ∧
        n * n + n ≤ (σ.arrs sk).length)
      fpC
      (fun σ σ' => CsrPrefix fo ft (fratGraph D) nf σ' ∧
        RankAt sg (selRank (bucketSel n) (fratGraph D)) σ' ∧
        (∀ b, b ≠ ao → b ≠ aj → b ≠ dg → b ≠ mt → b ≠ sg → b ≠ tp → b ≠ sk →
          σ'.arrs b = σ.arrs b) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ∉ fpScalars → σ'.vars y = σ.vars y))
      (kp n nf)

/-- **`FratPeelAt`, discharged** by `fratPeelCom` at `fratPeelK` — the
landed build then the landed peel, with `nf = slotCount (fratGraph D)`
(`graphCsr_ns_eq_slotCount`) turning the peel's slot term into the
contract's own figure. -/
theorem fratPeelAt_fratPeelCom {B : ℕ} {nN nF fo ft ao aj dg mt sg tp sk : String}
    (hnm : FpNames fo ft ao aj dg mt sg tp sk) (hcl : FpCells nN nF) :
    FratPeelAt B nN nF fo ft ao aj dg mt sg tp sk
      (fratPeelCom nN nF fo ft ao aj dg mt sg tp sk) fratPeelK := by
  intro n D nf σ hσ
  obtain ⟨hpre, hnN, hnF, hB, haoL, hajL, hdgL, hmtL, hsgL, htpL, hskL⟩ := hσ
  obtain ⟨hja, hjm, hjr, hjd, hjt, hjs⟩ := hnm.aj_ne
  obtain ⟨hfo, hft⟩ := hnm.csr_ne
  obtain ⟨hbi, hbj, hbu, hbw, hbp, hbq⟩ := (fpScalars_ne hcl.nN_notMem).1
  -- the source CSR, off the window
  obtain ⟨off, tgt, hsrc⟩ := srcCsr_of_csrPrefix hpre hnm.fo_ft
  -- the slot count is the figure the peel is charged at
  have hslot : nf = slotCount (fratGraph D) :=
    graphCsr_ns_eq_slotCount hpre.2.2
  have hnfsq : nf ≤ n * n := by
    have hle := offF_le_sq hsrc.zero hsrc.step n le_rfl
    rw [hsrc.last] at hle
    exact hle
  have hnB : n < B := by omega
  have hnfB : nf < B := by omega
  -- phase 1: the deletable adjacency region of `fratGraph D`
  obtain ⟨σ1, hrun1, ⟨-, hdel1⟩, hfv1, hfa1, -, -⟩ :=
    (bldAdj_spec (G := fratGraph D) (off := off) (tgt := tgt)
      hnm.bldNames hcl.bld hnB hnfB).frame.run
      ⟨hsrc, hnN, hnF, haoL, hajL, hdgL, hmtL⟩
  have hlen1 := run_arrs_length_eq hrun1
  have hfa1' : ∀ b : String, b ≠ ao → b ≠ aj → b ≠ dg → b ≠ mt →
      σ1.arrs b = σ.arrs b := fun b h1 h2 h3 h4 =>
    hfa1 b (not_mem_warrs_bldAdjCom h1 h2 h3 h4)
  have hfv1' : ∀ y : String, y ∉ fpScalars → σ1.vars y = σ.vars y := by
    intro y hy
    obtain ⟨⟨y1, y2, y3, y4, y5, y6⟩, -⟩ := fpScalars_ne hy
    exact hfv1 y (not_mem_wvars_bldAdjCom y1 y2 y3 y4 y5 y6)
  have hnN1 : σ1.vars nN = n := by
    rw [hfv1 nN (not_mem_wvars_bldAdjCom hbi hbj hbu hbw hbp hbq)]; exact hnN
  -- phase 2: the linear bucket peel
  obtain ⟨σ2, hrun2, hrank⟩ :=
    (bucketPeelCom_spec (nnSrc := nN) (ra := sg) (F := fratGraph D)
      hnm.distinct6 hja hjm hjr hjd hjt hjs hB).run
      ⟨hdel1, by rw [hlen1 sg]; exact hsgL, by rw [hlen1 tp]; exact htpL,
        by rw [hlen1 sk]; exact hskL, hnN1⟩
  have hlen2 := run_arrs_length_eq hrun2
  have hfa2 : ∀ b : String, b ≠ sg → b ≠ mt → b ≠ dg → b ≠ tp → b ≠ sk →
      σ2.arrs b = σ1.arrs b := fun b h1 h2 h3 h4 h5 =>
    bucketPeelCom_arrs_eq hrun2 b h1 h2 h3 h4 h5
  refine ⟨σ2, (hrun1.seq hrun2).mono ?_, ?_, rankAt_of_rankArr hrank, ?_, ?_, ?_⟩
  · simp only [fratPeelK]; omega
  · refine csrPrefix_of_eq hpre hnm.fo_ft ?_ ?_
    · rw [hfa2 fo hfo.2.2.2.2.1 hfo.2.2.2.1 hfo.2.2.1 hfo.2.2.2.2.2.1
        hfo.2.2.2.2.2.2]
      exact hfa1' fo hfo.1 hfo.2.1 hfo.2.2.1 hfo.2.2.2.1
    · rw [hfa2 ft hft.2.2.2.2.1 hft.2.2.2.1 hft.2.2.1 hft.2.2.2.2.2.1
        hft.2.2.2.2.2.2]
      exact hfa1' ft hft.1 hft.2.1 hft.2.2.1 hft.2.2.2.1
  · intro b h1 h2 h3 h4 h5 h6 h7
    rw [hfa2 b h5 h4 h3 h6 h7]
    exact hfa1' b h1 h2 h3 h4
  · intro b; rw [hlen2 b, hlen1 b]
  · intro y hy
    obtain ⟨-, ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12⟩⟩ := fpScalars_ne hy
    rw [bucketPeelCom_vars_eq hrun2 y z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12]
    exact hfv1' y hy

/-- The hypothesis bundle is satisfiable, so nothing above is vacuous:
nine distinct region names and two figure cells outside the pass's own
scratch. -/
example : FratPeelAt 64 "fp.nN" "fp.nF" "fr.o" "fr.t" "ad.o" "ad.j" "ad.d" "ad.m"
    "pk.r" "pk.p" "pk.k"
    (fratPeelCom "fp.nN" "fp.nF" "fr.o" "fr.t" "ad.o" "ad.j" "ad.d" "ad.m"
      "pk.r" "pk.p" "pk.k") fratPeelK :=
  fratPeelAt_fratPeelCom ⟨by decide⟩ ⟨by decide, by decide⟩

/-! ## §4 The price, inside the round's envelope -/

/-- **The peel fits `augRoundBudget`'s `kf` term.** Its two figures are
the carrier and the fraternal CSR's slot count; the latter is bounded by
`fratPairCount D` — `FratCsrAt`'s own last postcondition clause — so the
whole pass is `394·n + 176·fratPairCount D + 64`, which is
`augRoundBudget 394 0 176 0 64 D`. The `ka` and `kt` terms are not
needed at all, and there is no `n * n` term to price. -/
theorem fratPeelK_le_augRoundBudget {n : ℕ} (D : Orientation n) {nf : ℕ}
    (hnf : nf ≤ fratPairCount D) :
    fratPeelK n nf ≤ augRoundBudget 394 0 176 0 64 D := by
  have h := Nat.mul_le_mul_left 176 hnf
  simp only [fratPeelK, augRoundBudget]
  omega

/-- The same, read against a round budget that also pays for the
fraternal enumeration and the emit: any `kn ≥ 394`, `kf ≥ 176`,
`kc ≥ 64` covers the peel. -/
theorem fratPeelK_le_augRoundBudget' {n : ℕ} (D : Orientation n) {nf : ℕ}
    (hnf : nf ≤ fratPairCount D) {kn ka kf kt kc : ℕ}
    (hkn : 394 ≤ kn) (hkf : 176 ≤ kf) (hkc : 64 ≤ kc) :
    fratPeelK n nf ≤ augRoundBudget kn ka kf kt kc D := by
  have h1 : 394 * n ≤ kn * n := Nat.mul_le_mul_right n hkn
  have h2 : 176 * nf ≤ kf * fratPairCount D :=
    le_trans (Nat.mul_le_mul_left 176 hnf) (Nat.mul_le_mul_right _ hkf)
  simp only [fratPeelK, augRoundBudget]
  omega

/-- **The budget sits inside the pre-verified envelope**, in the
spelling `emK_le_levelCharge` uses for the sibling pass: one greedy
round is charged `levelCharge D = 3n + 2·arcCount + 4·fratPairCount +
2·transPairCount`, and the peel costs a *constant multiple* of that
charge — so it changes no exponent, only the `f` of the envelope
theorem. -/
theorem fratPeelK_le_levelCharge {n : ℕ} (D : Orientation n) {nf : ℕ}
    (hnf : nf ≤ fratPairCount D) :
    fratPeelK n nf ≤ 132 * levelCharge D + 64 := by
  have h := Nat.mul_le_mul_left 176 hnf
  simp only [fratPeelK, levelCharge]
  omega

/-- **The budget, priced by an in-degree bound**: at in-degree `≤ d` the
fraternal peel costs at most `n·(394 + 176·d²) + 64`. The carrier enters
linearly and never squared — the `d`-parameterization that keeps `n²`
out of the round, exactly as `emK_le` does for the emit. This is what
makes the peel safe to repeat `R + 1` times. -/
theorem fratPeelK_le {n : ℕ} {D : Orientation n} {d nf : ℕ} (hd : D.InDegLE d)
    (hnf : nf ≤ fratPairCount D) :
    fratPeelK n nf ≤ n * (394 + 176 * (d * d)) + 64 := by
  have h2 := fratPairCount_le hd
  calc fratPeelK n nf = 394 * n + 176 * nf + 64 := rfl
    _ ≤ 394 * n + 176 * (n * (d * d)) + 64 := by omega
    _ = n * (394 + 176 * (d * d)) + 64 := by ring

/-- The peel's own graph-size figure is inside the round's fraternal
term with room to spare: `arcCount`-shaped quantities are bounded by
`fratPairCount D` too (`arcCount_le_fratPairCount`), which is why the
`kf` term is the right home rather than `ka`. -/
theorem arcCount_le_fratPairCount' {n : ℕ} (D : Orientation n) :
    arcCount D ≤ fratPairCount D := arcCount_le_fratPairCount D

/-! ## §5 The axiom surface -/

#print axioms srcCsr_of_csrPrefix
#print axioms rankAt_of_rankArr
#print axioms fratPeelAt_fratPeelCom
#print axioms fratPeelK_le_augRoundBudget
#print axioms fratPeelK_le_augRoundBudget'
#print axioms fratPeelK_le_levelCharge
#print axioms fratPeelK_le

end Lax3Proofs.Prog
