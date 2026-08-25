import Lax3Proofs.SolveAugFrameProg
import Lax3Proofs.SolveSweepBucketRound
import Lax3Proofs.SolveAugEmitCom

/-!
# F6c12-5a-ii (continued) — two more of the augmentation frame's passes

`SolveAugCompose` (F6c12-5a) split the augmentation's base and
symmetrization halves into four named passes with pinned budget shapes
and no programs, and `SolveAugFrameProg` discharged the first,
`AugBaseAdjIn`. This file takes the two that later landings unblocked:

1. **`AugBasePeelIn` (§2) — DISCHARGED.** The base's peel, at the
   *linear* contract. When the pass was first looked at there was no
   peel program at all below `Θ(N²)`; `SolveSweepBucketRound` has since
   landed one — `bucketPeelCom`, discharging `CovSelPeelIn` at
   `bucketSel` with **no `A.N²` time term**. §2 composes it.

2. **`AugSymCsrIn` (§3) — NOT discharged here**; §3 records exactly what
   is missing and why the landed transpose is only half of it.

## §2, and the one thing the composition has to add

`bucketPeelCom` reads the deletable adjacency region of the graph it
peels and **consumes** it: its write set is `{ra, mt, dg, tp, sk}`, so
the degree array and the mate array — two of `DelAdjSt`'s four — are
gone when it stops. `CovSelPeelIn`, the contract it was written for, is
stated to match: the region appears in its precondition and *not* in its
postcondition, because the cover sweep never reads it again.

`AugBasePeelIn` is the opposite: the region has to survive, since
`AugBaseOrientIn` is what reads it next. So the pass is

    bucketPeelCom … ; bldAdjCom …

— peel the region into the rank array, then **rebuild the region from
the arena's own CSR**, which the peel never touched. The rebuild writes
exactly `{ao, aj, dg, mt}` and so leaves the rank array the peel just
produced (`RankArr.of_eq`), and the route to `bldAdj_spec` is
`augBaseAdjIn_bldAdjCom`'s — `srcCsr_of_graphCsr` at the arena's window,
because `AdjBuildAt` pins the two array lengths exactly and the arena
only ever supplies `≤`.

No second copy of the region is allocated: the rebuild lands in the same
four names the peel emptied.

The budget is `394·A.N + 352·arcCount (selChain sel A.G 0) + 64`:
`313·A.N + 118·slotCount A.G + 40` for the peel and
`81·A.N + 58·ns + 24` for the rebuild, with `slotCount A.G = ns` (the
arena's own slot count, `SrcCsr.ns_eq_sum`) and
`slotCount A.G = 2·arcCount (selChain sel A.G 0)`
(`slotCount_eq_two_mul_arcCount_baseOr`, `SolveAugFrameProg` §1) —
**by equality, no inequality spent, and no `A.N²` term anywhere**. That
is the whole point of taking the bucket peel rather than the landed
quadratic `peelCom`: the augmentation runs a peel `R + 1` times.

Against `augChainCost_le_selChainCharge`'s coefficient bounds `bn ≤ k`
and `ba ≤ 3·k`, the base pass's running total is now
`bn = 81 + 394 = 475` and `ba = 116 + 352 = 468` (`AugBaseAdjIn` plus
this pass), which closes at `k = 475`: `468 ≤ 1425` leaves the arc
coefficient nearly all of its slack for `AugBaseOrientIn`, and the
carrier coefficient is what the choice of `k` now tracks.

## The selection is `bucketSel`, and it has to be

`bucketPeelCom` produces `selPerm (bucketSel N) F` and nothing else, so
§2 is stated at `sel = fun m => bucketSel m`. That is the selection the
whole ordering chain already runs at (`covOrderIn_bucketPeel`), and
`augBaseAdjIn_bldAdjCom` holds at every selection, so the two base
passes compose.

## §3 What `AugSymCsrIn` still needs

`SolveAugEmitCom` landed `transposeIn_tpCom` — `TransposeIn` at
`tpK n a = 41n + 40a + 30` — which turns an in-neighbour CSR of `D`
into an *out*-neighbour CSR. `AugSymCsrIn` asks for a `GraphCsr` of
`D.toGraph`, whose row at `v` is `D.inN v ∪ outNbrs D v`. The transpose
is therefore one of two passes, and the second — the offsets of the
merged rows, and the two copies into each of them — **has no landed
counterpart**: `bldOffCom`/`bldMateCom` build a *deletable adjacency*
region from a source CSR, not a `GraphCsr` from two of them, and
`tpCom` itself is a counting sort of a single input. Writing that merge
is a program leaf of its own, not an assembly of landed pieces, and it
is not attempted here.

What §3 records is the three facts about the merge that are *not* that
program, each of which changes what it has to be aimed at:

* **its slot count is forced.** `AugSymCsrIn` asks only for
  `ns ≤ 2·arcCount D`, but a CSR of `D.toGraph` has no freedom —
  `slotCount_eq_two_mul_arcCount` at `Orientation.orients_toGraph` makes
  the clause an equality (`symCsr_ns_eq`, `symCsr_ns_le`);
* **its offsets need no prefix sum.** The merged offset function is the
  *pointwise sum* of the input CSR's and the transpose's
  (`toGraph_step_add`), so the offset pass is one addition and one store
  a vertex rather than a scan with a running total;
* **it cannot allocate, so its caller must.** `GraphCsr` pins both array
  lengths exactly and IMP+ preserves every length, so the exact
  allocation has to hold before the pass runs (`graphCsr_pre_lengths`) —
  and it is expressible where the precondition can carry it
  (`symCsrSizes`, `symCsrSizes_exact`).
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.Augmentation (Orientation baseOr baseOr_orients)
open Lax3Proofs.CoverRoutine (MinDegSel selPerm selChain)
open Lax3Proofs.TgtCoupling (outNbrs)

/-! ## §1 The pass's scratch scalars

The base peel writes two blocks of scalars — the bucket peel's twelve
`bk.*` and the region build's six (`bldScalars`) — and nothing else. A
descriptor that avoids all eighteen is carried across the whole pass,
which is the only shape §2's `Smp`/`Ssw` transports are stated in. -/

/-- The eighteen scalars the base peel pass writes. -/
def basePeelScalars : List String :=
  ["bk.n", "bk.i", "bk.u", "bk.m", "bk.t", "bk.z", "bk.c", "bk.r", "bk.f",
    "bk.v", "bk.w", "bk.d"] ++ bldScalars

theorem not_mem_bldScalars_of_basePeel {y : String} (h : y ∉ basePeelScalars) :
    y ∉ bldScalars := fun hy => h (List.mem_append_right _ hy)

theorem bk_ne_of_basePeel {y : String} (h : y ∉ basePeelScalars) :
    y ≠ "bk.n" ∧ y ≠ "bk.i" ∧ y ≠ "bk.u" ∧ y ≠ "bk.m" ∧ y ≠ "bk.t" ∧
      y ≠ "bk.z" ∧ y ≠ "bk.c" ∧ y ≠ "bk.r" ∧ y ≠ "bk.f" ∧ y ≠ "bk.v" ∧
      y ≠ "bk.w" ∧ y ≠ "bk.d" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rintro rfl
      exact h (by simp [basePeelScalars])

/-! ## §2 The base's peel, discharged at the linear contract -/

open Classical in
/-- **`AugBasePeelIn`, discharged** — the second of the base pass's
three, at the program `bucketPeelCom … ; bldAdjCom …` and the budget
`394·A.N + 352·arcCount (selChain bucketSel A.G 0) + 64`, with **no
`A.N * A.N` term**.

The pass leaves the rank array at `selPerm (bucketSel A.N) A.G` — the
elimination ranking round `0` of the chain is oriented along — and the
deletable adjacency region of `A.G` exactly as it found it.

Three things are worth naming about the proof:

* the bucket peel *consumes* the region it reads (its write set contains
  the degree and mate arrays), and `AugBasePeelIn` demands the region
  back, so the pass rebuilds it from the arena's CSR afterwards. The
  rebuild's write set is `{bao, baj, bdg, bmt}`, which is disjoint from
  the rank array, so the peel's output survives it (`RankArr.of_eq`);
* the rebuild goes through `srcCsr_of_graphCsr` + `bldAdj_spec`, not
  `adjBuildAt_bldAdjCom`: the arena's CSR arrays are `≥` its dimensions
  and `AdjBuildAt`'s `GraphCsr` clause pins them `=`;
* the two slot terms are converted by equalities only —
  `SrcCsr.ns_eq_sum` reads the arena's `nS` cell as `A.G`'s degree sum,
  `offF_eq_slotCount` reads the region's own extent as the same figure,
  and `slotCount_eq_two_mul_arcCount_baseOr` reads that as
  `2·arcCount (selChain bucketSel A.G 0)`.

The scratch the pass asks for is the peel's own: the rank region, the
bucket tops (`n` cells) and the bucket cells (`n² + n` cells). That
block is quadratic in **space** and the pass is linear in **time**; it
is the same shape as the adjacency region the peel reads. -/
theorem augBasePeelIn_bucketPeelBuild (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (bao baj bdg bmt bra tpO skO raY odY : ℕ → String)
    (Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnd : ∀ j, Distinct6 (bao j) (bmt j) (bra j) (bdg j) (tpO j) (skO j))
    (hnj : ∀ j, baj j ≠ bao j ∧ baj j ≠ bmt j ∧ baj j ≠ bra j ∧ baj j ≠ bdg j ∧
      baj j ≠ tpO j ∧ baj j ≠ skO j)
    (hnm : ∀ j, BldNames (arenaNames j).off (arenaNames j).tgt (raY j)
      (bao j) (baj j) (bdg j) (bmt j) (odY j))
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ bao j ∧ b ≠ baj j ∧ b ≠ bdg j ∧ b ≠ bmt j ∧ b ≠ bra j ∧
        b ≠ tpO j ∧ b ≠ skO j)
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b : String, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
        b ≠ bra j → b ≠ tpO j → b ≠ skO j → σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ∉ basePeelScalars → σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b : String, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
        b ≠ bra j → b ≠ tpO j → b ≠ skO j → σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ∉ basePeelScalars → σ'.vars y = σ.vars y) → Ssw j σ') :
    AugBasePeelIn C hC φ (fun m => bucketSel m) G c w q ℓp htabF hbf Adm ca co
      bao baj bdg bmt bra
      (fun j σ => n ≤ (σ.arrs (bra j)).length ∧ n ≤ (σ.arrs (tpO j)).length ∧
        n * n + n ≤ (σ.arrs (skO j)).length)
      Smp Ssw
      (fun j => .seq
        (bucketPeelCom (bao j) (baj j) (bdg j) (bmt j) (bra j) (tpO j) (skO j)
          (arenaNames j).nN)
        (bldAdjCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
          (arenaNames j).tgt (bao j) (baj j) (bdg j) (bmt j)))
      394 352 64 := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hAW, hdel, ⟨hralen, htplen, hsklen⟩, hcaL, hcoL, hSm, hSw⟩ := hσ
  obtain ⟨hja, hjm, hjr, hjd, hjt, hjs⟩ := hnj j
  have hndj := hnd j
  have hnmj := hnm j
  have hcl := bldCells_arenaNames j
  -- the two figures, and that they are words
  have henc : EncodesGraph x n G := hx.1
  have hlenx := henc.length_eq
  have hNn : A.N ≤ n := hAW.st.N_le_root
  have hnN : σ.vars (arenaNames j).nN = A.N := hAW.n_eq
  have hBnd : A.N + A.N * A.N + 1 < mcB q x := by
    have h1 : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
    have h2 : (x.length + 1) * (x.length + 1) ≤ mcB q x := by
      rw [mcB, pow_two]
      exact Nat.le_mul_of_pos_left _ hq
    have h3 : n * n + n + 1 < (x.length + 1) * (x.length + 1) := by nlinarith
    omega
  have hNB : A.N < mcB q x := by omega
  -- the region the peel eats, and the two figures it is laid out at
  obtain ⟨offF, hoff0, hoffs, haoLen, -, hajLen, hmtLen, hdgLen, -, -, -, -⟩ :=
    id hdel
  have hslot : offF A.N = slotCount A.G := offF_eq_slotCount hoff0 hoffs
  have hoffsq : offF A.N ≤ A.N * A.N := offF_le_sq hoff0 hoffs A.N le_rfl
  have hsk' : A.N * A.N + A.N ≤ (σ.arrs (skO j)).length := by
    have h1 : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
    omega
  -- 1. the peel: the rank array, at the cost of the region
  obtain ⟨σ₁, hrun1, hrank1⟩ :=
    (bucketPeelCom_spec (ao := bao j) (aj := baj j) (dg := bdg j) (mt := bmt j)
      (ra := bra j) (tp := tpO j) (sk := skO j) (nnSrc := (arenaNames j).nN)
      hndj hja hjm hjr hjd hjt hjs hBnd (F := A.G)).run
      ⟨hdel, le_trans hNn hralen, le_trans hNn htplen, hsk', hnN⟩
  have hlen1 := run_arrs_length_eq hrun1
  have harrs1 : ∀ b : String, b ≠ bra j → b ≠ bmt j → b ≠ bdg j → b ≠ tpO j →
      b ≠ skO j → σ₁.arrs b = σ.arrs b :=
    fun b h1 h2 h3 h4 h5 => bucketPeelCom_arrs_eq hrun1 b h1 h2 h3 h4 h5
  have hvars1 : ∀ y : String, y ∉ basePeelScalars → σ₁.vars y = σ.vars y := by
    intro y hy
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ := bk_ne_of_basePeel hy
    exact bucketPeelCom_vars_eq hrun1 y k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12
  obtain ⟨hnN1, hnS1⟩ := arena_vars_eq_of_bucketPeel hrun1 j
  -- the arena is untouched by the peel
  have hAW1 : ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ₁ := by
    refine arenaStW_of_eq hAW hnN1 hnS1 ?_ ?_ ?_ ?_ ?_
    · obtain ⟨-, -, k3, k4, k5, k6, k7⟩ := harn j _ (Or.inl rfl)
      exact harrs1 _ k5 k4 k3 k6 k7
    · obtain ⟨-, -, k3, k4, k5, k6, k7⟩ := harn j _ (Or.inr (Or.inl rfl))
      exact harrs1 _ k5 k4 k3 k6 k7
    · obtain ⟨-, -, k3, k4, k5, k6, k7⟩ := harn j _ (Or.inr (Or.inr (Or.inl rfl)))
      exact harrs1 _ k5 k4 k3 k6 k7
    · obtain ⟨-, -, k3, k4, k5, k6, k7⟩ :=
        harn j _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      exact harrs1 _ k5 k4 k3 k6 k7
    · obtain ⟨-, -, k3, k4, k5, k6, k7⟩ :=
        harn j _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      exact harrs1 _ k5 k4 k3 k6 k7
  -- 2. the rebuild: the arena's CSR, read through its window
  have hot : (arenaNames j).tgt ≠ (arenaNames j).off :=
    lv_ne_of_base_ne (by decide) (by decide) j j
  have hoL1 : A.N + 1 ≤ (σ₁.arrs (arenaNames j).off).length :=
    hAW1.fits _ _ arenaWs_off
  have htL1 : σ₁.vars (arenaNames j).nS ≤ (σ₁.arrs (arenaNames j).tgt).length :=
    hAW1.fits _ _ (arenaWs_tgt hot)
  have hcsrw : GraphCsr (arenaNames j).off (arenaNames j).tgt A.G
      (σ₁.vars (arenaNames j).nS)
      (winA (arenaWs (arenaNames j) ((Headline.headlineSetup C hC φ).pal j) (ℓp j)
        (hbf j) A.N (σ₁.vars (arenaNames j).nS)) σ₁) := hAW1.st.csr
  obtain ⟨off, tgt, hsrc⟩ :=
    srcCsr_of_graphCsr hcsrw hoL1 htL1
      (fun i hi => by
        rw [arrs_winA_some arenaWs_off, List.getElem?_take_of_lt (by omega)])
      (fun p hp => by
        rw [arrs_winA_some (arenaWs_tgt hot), List.getElem?_take_of_lt hp])
  -- the arena's slot count is the region's own extent
  have hns : σ₁.vars (arenaNames j).nS = slotCount A.G := hsrc.ns_eq_sum
  have hnsB : σ₁.vars (arenaNames j).nS < mcB q x := by omega
  have hnN1' : σ₁.vars (arenaNames j).nN = A.N := by rw [hnN1, hnN]
  obtain ⟨σ₂, hrun2, ⟨⟨-, hdel2⟩, hfv, hfa, -, -⟩, hlen2⟩ :=
    (specArrsLength (bldAdj_spec (G := A.G) (off := off) (tgt := tgt)
      (B := mcB q x) hnmj hcl hNB hnsB).frame).run
      ⟨hsrc, hnN1', rfl,
        by rw [hlen1 (bao j)]; exact haoLen,
        by rw [hlen1 (baj j), hns, ← hslot]; exact hajLen,
        by rw [hlen1 (bdg j)]; exact hdgLen,
        by rw [hlen1 (bmt j), hns, ← hslot]; exact hmtLen⟩
  -- the rebuild's frame, in the two shapes the transports consume
  have hfa' : ∀ b : String, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
      σ₂.arrs b = σ₁.arrs b :=
    fun b h1 h2 h3 h4 => hfa b (not_mem_warrs_bldAdjCom h1 h2 h3 h4)
  have hfv' : ∀ y : String, y ∉ bldScalars → σ₂.vars y = σ₁.vars y := by
    intro y hy
    simp only [bldScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hy
    exact hfv y (not_mem_wvars_bldAdjCom h0 h1 h2 h3 h4 h5)
  -- the whole pass's frame
  have harrsT : ∀ b : String, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
      b ≠ bra j → b ≠ tpO j → b ≠ skO j → σ₂.arrs b = σ.arrs b := by
    intro b h1 h2 h3 h4 h5 h6 h7
    rw [hfa' b h1 h2 h3 h4, harrs1 b h5 h4 h3 h6 h7]
  have hlenT : ∀ b : String, (σ₂.arrs b).length = (σ.arrs b).length := by
    intro b; rw [hlen2 b, hlen1 b]
  have hvarsT : ∀ y : String, y ∉ basePeelScalars → σ₂.vars y = σ.vars y := by
    intro y hy
    rw [hfv' y (not_mem_bldScalars_of_basePeel hy), hvars1 y hy]
  -- the rank array survives the rebuild
  have hraT : σ₂.arrs (bra j) = σ₁.arrs (bra j) :=
    hfa' _ (Ne.symm hndj.ar) hjr.symm hndj.rd hndj.mr.symm
  refine ⟨σ₂, (hrun1.seq hrun2).mono ?_, ?_, hdel2, hrank1.of_eq hraT, ?_, ?_, ?_,
    hSmp j σ σ₂ hSm harrsT hlenT hvarsT, hSsw j σ σ₂ hSw harrsT hlenT hvarsT⟩
  · -- the budget: both slot terms are `2·arcCount` of round `0`, by equality
    have harc : slotCount A.G = 2 * arcCount (selChain (bucketSel A.N) A.G 0) := by
      rw [selChain_zero]
      exact slotCount_eq_two_mul_arcCount_baseOr A.G (selPerm (bucketSel A.N) A.G)
    have hbeta : arcCount (selChain ((fun m => bucketSel m) A.N) A.G 0)
        = arcCount (selChain (bucketSel A.N) A.G 0) := rfl
    rw [hns, harc]
    omega
  · -- the arena survives the rebuild too
    refine arenaStW_of_eq hAW1 (hfv' _ hcl.nN_notMem) (hfv' _ hcl.nS_notMem) ?_ ?_ ?_
      ?_ ?_
    · obtain ⟨k1, k2, k3, k4, -, -, -⟩ := harn j _ (Or.inl rfl)
      exact hfa' _ k1 k2 k3 k4
    · obtain ⟨k1, k2, k3, k4, -, -, -⟩ := harn j _ (Or.inr (Or.inl rfl))
      exact hfa' _ k1 k2 k3 k4
    · obtain ⟨k1, k2, k3, k4, -, -, -⟩ := harn j _ (Or.inr (Or.inr (Or.inl rfl)))
      exact hfa' _ k1 k2 k3 k4
    · obtain ⟨k1, k2, k3, k4, -, -, -⟩ :=
        harn j _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      exact hfa' _ k1 k2 k3 k4
    · obtain ⟨k1, k2, k3, k4, -, -, -⟩ :=
        harn j _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      exact hfa' _ k1 k2 k3 k4
  · -- the peel's scratch is length-only, and no length changes
    exact ⟨by rw [hlenT (bra j)]; exact hralen, by rw [hlenT (tpO j)]; exact htplen,
      by rw [hlenT (skO j)]; exact hsklen⟩
  · rw [hlenT (ca j)]; exact hcaL
  · rw [hlenT (co j)]; exact hcoL

/-! ## §2b The same discharge at a **parametric** base descriptor

§2 *pins* `AugBasePeelIn`'s `Sbd` to its own three length clauses.  That
is fatal to the composition and not merely inconvenient:
`augBaseIn_of_adj_peel_orient` takes **one** `Sbd` for all three base
passes, and `augBaseOrientIn_orCom` asks that same `Sbd` to bound
`io`/`it`/`cn` against the arena's carrier cell — which the pinned triple
never mentions, so a state whose carrier cell exceeds every array refutes
it, at every choice of the six names (`coverAllBase_hSbd_unsatisfiable`,
`SolveCoverAllJoin` §4b).

The repair costs no new program and no new proof about `bucketPeelCom`:
§2's `Smp` is already a *parameter* carried across the whole pass by a
frame-shaped transport, so instantiating it at `Smp ∧ Sbd` carries an
arbitrary `Sbd` through the peel as well, and the rule of consequence
reshuffles the two conjunctions.  §2 is left exactly as it landed and
follows from §2b at `Sbd :=` its own triple. -/

open Classical in
/-- **`AugBasePeelIn`, discharged at any base descriptor** the caller
can (a) read the peel's three allocations off and (b) carry across the
peel's writes.  Same program, same budget `394, 352, 64`, same
hypothesis bundle; only `Sbd` is freed, which is what lets the three
base passes share one.

The transport `hSbd` is handed the write frame, the length clause (IMP+
changes no length) and the scalar frame — the same three §2's own
`hSmp`/`hSsw` get — so a descriptor made of lengths and of content in
arrays the pass does not write rides through with nothing to prove. -/
theorem augBasePeelInS_bucketPeelBuild (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (bao baj bdg bmt bra tpO skO raY odY : ℕ → String)
    (Sbd Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnd : ∀ j, Distinct6 (bao j) (bmt j) (bra j) (bdg j) (tpO j) (skO j))
    (hnj : ∀ j, baj j ≠ bao j ∧ baj j ≠ bmt j ∧ baj j ≠ bra j ∧ baj j ≠ bdg j ∧
      baj j ≠ tpO j ∧ baj j ≠ skO j)
    (hnm : ∀ j, BldNames (arenaNames j).off (arenaNames j).tgt (raY j)
      (bao j) (baj j) (bdg j) (bmt j) (odY j))
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ bao j ∧ b ≠ baj j ∧ b ≠ bdg j ∧ b ≠ bmt j ∧ b ≠ bra j ∧
        b ≠ tpO j ∧ b ≠ skO j)
    (hSbdL : ∀ (j : ℕ) (σ : Env), Sbd j σ →
      n ≤ (σ.arrs (bra j)).length ∧ n ≤ (σ.arrs (tpO j)).length ∧
        n * n + n ≤ (σ.arrs (skO j)).length)
    (hSbd : ∀ (j : ℕ) (σ σ' : Env), Sbd j σ →
      (∀ b : String, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
        b ≠ bra j → b ≠ tpO j → b ≠ skO j → σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ∉ basePeelScalars → σ'.vars y = σ.vars y) → Sbd j σ')
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b : String, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
        b ≠ bra j → b ≠ tpO j → b ≠ skO j → σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ∉ basePeelScalars → σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b : String, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
        b ≠ bra j → b ≠ tpO j → b ≠ skO j → σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ∉ basePeelScalars → σ'.vars y = σ.vars y) → Ssw j σ') :
    AugBasePeelIn C hC φ (fun m => bucketSel m) G c w q ℓp htabF hbf Adm ca co
      bao baj bdg bmt bra Sbd Smp Ssw
      (fun j => .seq
        (bucketPeelCom (bao j) (baj j) (bdg j) (bmt j) (bra j) (tpO j) (skO j)
          (arenaNames j).nN)
        (bldAdjCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
          (arenaNames j).tgt (bao j) (baj j) (bdg j) (bmt j)))
      394 352 64 := by
  intro x hx j hj A hAdm hbot
  refine (augBasePeelIn_bucketPeelBuild C hC φ G c w q ℓp htabF hbf Adm ca co
    bao baj bdg bmt bra tpO skO raY odY (fun j σ => Smp j σ ∧ Sbd j σ) Ssw hq
    hnd hnj hnm harn ?_ hSsw x hx j hj A hAdm hbot).conseq ?_ ?_ le_rfl
  · rintro jj σ σ' ⟨h1, h2⟩ ha hl hv
    exact ⟨hSmp jj σ σ' h1 ha hl hv, hSbd jj σ σ' h2 ha hl hv⟩
  · rintro σ ⟨hA, hdel, hSb, hca, hco, hSm, hSw⟩
    exact ⟨hA, hdel, hSbdL j σ hSb, hca, hco, ⟨hSm, hSb⟩, hSw⟩
  · rintro σ σ' - ⟨hA, hdel, hra, -, hca, hco, ⟨hSm, hSb⟩, hSw⟩
    exact ⟨hA, hdel, hra, hSb, hca, hco, hSm, hSw⟩

/-! ## §3 `AugSymCsrIn`: the arithmetic it needs, and the sizing it
forces

The transpose half of the symmetrization is landed
(`transposeIn_tpCom`, at `tpK n a = 41n + 40a + 30`). The merge half —
`D.inN v` and `outNbrs D v` laid end to end, one row per vertex — is a
program leaf of its own, with no landed counterpart: `tpCom` is a
counting sort of a *single* input CSR and `bldOffCom`/`bldMateCom`
build a *deletable adjacency* region, not a `GraphCsr`, out of one.
`AugSymCsrIn` is therefore **not discharged here**.

What is proved here is everything about the pass that is not that
program, because both facts change what the merge has to be aimed at.

**The `ns` clause is an equality.** `AugSymCsrIn` asks only for
`ns ≤ 2·arcCount D`, but a CSR of `D.toGraph` has no freedom: its slot
count *is* the degree sum, and the degree sum of `D.toGraph` is
`2·arcCount D` by `SolveAugFrameProg` §1's handshake read at
`Orientation.orients_toGraph`. So a merge emitting one slot per
(arc, endpoint) pair meets the clause exactly, with nothing to prove
twice and nothing to spend.

**The pass cannot allocate; the caller must.** `GraphCsr` is `Lib.Csr`'s
relation, whose two clauses are array *equalities* — `σ.arrs o` **is**
the length-`(N+1)` offset array and `σ.arrs t` **is** the length-`ns`
target array. IMP+ has no allocation: `store`'s semantics is
`List.set`, so every run preserves every array's length
(`run_arrs_length_eq`). Hence any program discharging `AugSymCsrIn`
must be *handed* `soO j` at exactly `A.N + 1` cells and `stO j` at
exactly `2·arcCount (selChain sel A.G R)` cells
(`graphCsr_pre_lengths`) — a windowed `≥` allocation, which is what the
arena and every scratch descriptor in the frame supply, is not enough.

This is not a hole in the contract: the figure is recoverable from the
data the precondition already carries. `augStInN`'s own scalar `nA`
holds `arcCount D` (`§7 of SolveAugCompose`) and the arena's `nN` holds
`A.N`, so the rounds' descriptor `Srd` — which sees only `j` and `σ`,
and can name neither `A` nor `D` — pins both lengths with
`symCsrSizes`, and `symCsrSizes_exact` turns that into the two exact
figures. No new cell and no new pass is needed for the sizing; it has
to be *stated*, and until it is, the merge has nothing to write into. -/

/-- **The symmetrization's slot count is exactly twice the arc count.**
`SolveAugFrameProg` §1's handshake, read at `D.toGraph` — the graph the
symmetrization builds is oriented by `D` by construction
(`Orientation.orients_toGraph`), so no side condition is left over. -/
theorem slotCount_toGraph_eq_two_mul_arcCount {N : ℕ} (D : Orientation N) :
    slotCount D.toGraph = 2 * arcCount D :=
  slotCount_eq_two_mul_arcCount D.orients_toGraph

/-- **The merged offsets are the pointwise sum of the two inputs'** —
the merge needs no prefix sum. If `oi` steps by the in-degrees (the
input CSR's own offset function, `TrInCsr.step`) and `oo` by the
out-degrees (the transpose's, `OutCsrAt`'s), then `oi + oo` steps by the
degrees of `D.toGraph`, which is exactly `SrcCsr`/`GraphCsr`'s step
clause for the symmetrized graph.

The content is `SolveAugFrameProg` §1's split of a neighbourhood into
its in- and out-arcs, read at `D.toGraph`; `asymm` is what makes it a
partition. Together with `oi N = oo N = arcCount D` this also gives the
extent `2·arcCount D` (`slotCount_toGraph_eq_two_mul_arcCount`), so the
merge's offset pass is one addition and one store per vertex. -/
theorem toGraph_step_add {N : ℕ} (D : Orientation N) (oi oo : ℕ → ℕ)
    (hi : ∀ v : Fin N, oi ((v : ℕ) + 1) = oi (v : ℕ) + (D.inN v).card)
    (ho : ∀ v : Fin N, oo ((v : ℕ) + 1) = oo (v : ℕ) + (outNbrs D v).card)
    (v : Fin N) :
    oi ((v : ℕ) + 1) + oo ((v : ℕ) + 1)
      = (oi (v : ℕ) + oo (v : ℕ)) + (D.toGraph.neighborSet v).ncard := by
  rw [hi v, ho v,
    ncard_neighborSet_eq_card_inN_add_card_outNbrs D.orients_toGraph v]
  ring

/-- **A `GraphCsr` pins its two arrays' lengths exactly** — `Lib.Csr`'s
first two clauses are array equalities, not allocations. -/
theorem graphCsr_lengths {o t : String} {N ns : ℕ} {G : SimpleGraph (Fin N)}
    {σ : Env} (h : GraphCsr o t G ns σ) :
    (σ.arrs o).length = N + 1 ∧ (σ.arrs t).length = ns := by
  obtain ⟨_off, _tgt, hc, -, -, -⟩ := h
  exact ⟨hc.length_off, hc.length_tgt⟩

/-- **A `GraphCsr`'s slot count is the degree sum.** The exact-length
relation read at the windowed one: `srcCsr_of_graphCsr` at the identity
window, then `SrcCsr.ns_eq_sum`. -/
theorem graphCsr_ns_eq_slotCount {o t : String} {N ns : ℕ}
    {G : SimpleGraph (Fin N)} {σ : Env} (h : GraphCsr o t G ns σ) :
    ns = slotCount G := by
  obtain ⟨_off, _tgt, hsrc⟩ :=
    srcCsr_of_graphCsr h (graphCsr_lengths h).1.ge (graphCsr_lengths h).2.ge
      (fun _ _ => rfl) (fun _ _ => rfl)
  exact hsrc.ns_eq_sum

/-- **`AugSymCsrIn`'s `ns` clause, as an equality.** Any CSR of
`D.toGraph` has exactly `2·arcCount D` slots, so the contract's
`ns ≤ 2·arcCount D` is met on the nose by the only slot count a merge
can produce. -/
theorem symCsr_ns_eq {o t : String} {N ns : ℕ} {D : Orientation N} {σ : Env}
    (h : GraphCsr o t D.toGraph ns σ) : ns = 2 * arcCount D := by
  rw [graphCsr_ns_eq_slotCount h]
  exact slotCount_toGraph_eq_two_mul_arcCount D

/-- The contract's clause itself, a fortiori. -/
theorem symCsr_ns_le {o t : String} {N ns : ℕ} {D : Orientation N} {σ : Env}
    (h : GraphCsr o t D.toGraph ns σ) : ns ≤ 2 * arcCount D :=
  le_of_eq (symCsr_ns_eq h)

/-- **No IMP+ program can create the two lengths a `GraphCsr` asserts.**
`store` is `List.set`, so lengths are run-invariant; the exact
allocation therefore has to hold *before* the pass runs. This is the
obligation `AugSymCsrIn` puts on whatever establishes its
precondition. -/
theorem graphCsr_pre_lengths {B K : ℕ} {c : Com} {σ σ' : Env} {o t : String}
    {N ns : ℕ} {G : SimpleGraph (Fin N)} (hrun : Run B c σ σ' K)
    (h : GraphCsr o t G ns σ') :
    (σ.arrs o).length = N + 1 ∧ (σ.arrs t).length = ns := by
  have hlen := run_arrs_length_eq hrun
  exact ⟨by rw [← hlen o]; exact (graphCsr_lengths h).1,
    by rw [← hlen t]; exact (graphCsr_lengths h).2⟩

/-- **The sizing, expressed where the pass's precondition can carry
it.** `Srd j σ` sees only the level and the state — it can name neither
the arena nor the orientation — but it does not have to: the carrier
sits in the arena's `nN` cell and the arc count in `augStInN`'s own `nA`
cell, so both exact lengths are statements about `σ` alone. -/
def symCsrSizes (nA soO stO : ℕ → String) (j : ℕ) (σ : Env) : Prop :=
  (σ.arrs (soO j)).length = σ.vars (arenaNames j).nN + 1 ∧
    (σ.arrs (stO j)).length = 2 * σ.vars (nA j)

/-- **… and it says exactly what the merge needs.** Against the arena's
carrier cell and the orientation region's own arc-count cell,
`symCsrSizes` is the two exact allocations `GraphCsr` demands. -/
theorem symCsrSizes_exact {io it nA soO stO : ℕ → String} {j : ℕ} {Λ n₀ : ℕ}
    {A : Arena Λ n₀} {D : Orientation A.N} {σ : Env}
    (hst : augStInN io it nA j A D σ)
    (hn : σ.vars (arenaNames j).nN = A.N)
    (hsz : symCsrSizes nA soO stO j σ) :
    (σ.arrs (soO j)).length = A.N + 1 ∧
      (σ.arrs (stO j)).length = 2 * arcCount D :=
  ⟨by rw [hsz.1, hn], by rw [hsz.2, hst.2]⟩

/-! ## §4 Axiom audit

§3 rests on the three standard axioms alone. §2's discharge quotes
`Headline.headlineSetup` in its statement and therefore — exactly like
the landed `covSelPeelIn_bucketPeelCom` and `augBaseAdjIn_bldAdjCom` it
composes — additionally carries Lax12's endorsed
`uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms augBasePeelIn_bucketPeelBuild

#print axioms augBasePeelInS_bucketPeelBuild

#print axioms slotCount_toGraph_eq_two_mul_arcCount

#print axioms toGraph_step_add

#print axioms graphCsr_ns_eq_slotCount

#print axioms symCsr_ns_eq

#print axioms graphCsr_pre_lengths

#print axioms symCsrSizes_exact

end Lax3Proofs.Prog
