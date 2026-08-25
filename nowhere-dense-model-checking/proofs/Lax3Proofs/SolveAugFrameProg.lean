import Lax3Proofs.SolveAugCompose
import Lax3Proofs.TgtCoupling

/-!
# F6c12-5a-ii — the augmentation frame's four small passes

`SolveAugCompose` (F6c12-5a) proved `CovAugAdjIn` **verbatim** from
three residuals and then split the base and symmetrization halves into
four smaller named passes, each with a pinned budget shape and **no
program**:

1. `AugBaseAdjIn` — the adjacency region of `A.G`;
2. `AugBasePeelIn` — the peel giving `selPerm sel A.G`, at the *linear*
   shape;
3. `AugBaseOrientIn` — the orientation `baseOr A.G (selPerm sel A.G)`,
   which is `selChain sel A.G 0`;
4. `AugSymCsrIn` — the transpose feeding the symmetrization.

This file is that leaf. **Discharged here: (1).** `(2)`, `(3)` and `(4)`
are *not* discharged — §3 below says exactly what each of them still
needs and why none of it is a matter of assembling landed pieces.

## §1 The handshake `SolveAugCompose` left open

The base pass's budgets are stated at `arcCount (selChain sel A.G 0)`
and not via a slot count, because — as F6c12-5a recorded — the identity
relating the two was landed nowhere. §1 proves it, in the only
generality the frame needs and in the direction that matters:

    D.Orients G  →  ∑ v, (G.neighborSet v).ncard = 2 * arcCount D

(`sum_ncard_neighborSet_eq_two_mul_arcCount`). Every edge of `G` carries
exactly one arc of `D` and is counted at both of its ends, so the CSR
slot count of `G` is twice `D`'s arc count; `asymm` is what makes the
split of a neighbourhood into in- and out-arcs a partition rather than a
cover. Since `slotCount` *is* the degree sum, the same theorem reads as

    slotCount G = 2 * arcCount (baseOr G π)

(`slotCount_eq_two_mul_arcCount_baseOr`) — the identity F6c12-5a's
packet named and said was landed nowhere. It is what turns the build
pass's `58·ns` into `116·arcCount`, and it is what any later base pass
charged per CSR slot will need.

## §2 The base's region build, discharged

`AugBaseAdjIn`'s program is the landed `bldAdjCom` at the **arena's own
CSR pair**, and the route is `covAdjBuildIn_bldCom`'s, not
`adjBuildAt_bldAdjCom`'s. The trap: `AdjBuildAt` asks for a plain
`GraphCsr`, whose `Csr` clause pins the two array lengths **exactly**,
while the arena supplies its CSR only behind `winA` — its arrays are
`≥` the dimensions, never `=`. So the build is reached through
`srcCsr_of_graphCsr` + `bldAdj_spec`, reading the windowed CSR into a
`SrcCsr` at the window's `≤` lengths, exactly as the landed cover-sweep
build does. `augBaseAdjIn_bldAdjCom` is that, minus the rank inversion
(`bldOrdCom`), which the base pass has no rank array for yet.

The budget is `81·A.N + 116·arcCount (selChain sel A.G 0) + 24`:
`bldAdj_spec` charges `81·N + 58·ns + 24` and §1 says `ns` — the
arena's own slot count, `SrcCsr.ns_eq_sum` — is exactly `2·arcCount`.
No inequality is spent and there is no `A.N²` term. Against
`augChainCost_le_selChainCharge`'s coefficient bounds `bn ≤ k`,
`ba ≤ 3·k`, this pass alone closes at `k = 81` (`116 ≤ 243`), leaving
the arc coefficient the slack half for the other two base passes.

Hypotheses are of the F7-suppliable kinds only: `1 ≤ q`, the build
pass's own region discipline (`BldNames`, `BldCells`, the four output
regions being none of the arena's other three arrays), the augmentation
scratch's four allocations, and the three descriptors' transport across
`bldAdjCom`'s writes.

## §3 What is **not** proved here

`AugBasePeelIn`, `AugBaseOrientIn` and `AugSymCsrIn` are named-but-
unproved, and none of them is assembly:

* **The peel.** No peel *program* is landed anywhere at the linear
  contract. `SolveSweepBucketProg` §5 is explicit that
  `linearPeelBudget` is "the shape a peel pass built on §1–§4 can meet,
  not a budget proved of any program here"; `peelLoop_linear_bucket`
  and `peelLoop_linear_static_cursor` are **loop rules**, and the entry
  sort `AdjSortIn` is itself a residual. The only landed peel program,
  `covSelPeelIn_peelCom_mdSel`, is the quadratic one
  (`86·N² + 43·N + 14`) that this whole split exists to avoid.
* **The orientation.** Producing `augStInN`'s `InNCsr` of
  `baseOr A.G π` from a `DelAdjSt` of `A.G` and a `RankArr` is a fresh
  three-phase CSR construction — count each vertex's rank-smaller
  neighbours, prefix-sum, scatter — with no landed counterpart:
  `bldOffCom`/`bldDegCom`/`bldMateCom` build a *deletable adjacency*
  region out of a source CSR, which is neither the input nor the output
  shape here.
* **The transpose.** `TransposeIn` (`SolveAugEmit.lean:806`) is the
  matching contract and is a **residual there too** — `SolveAugEmit`
  proves the transpose's arithmetic (`outOff_last`, `mem_adjSet`) and
  names the pass. Merging `D.inN v` with `outNbrs D v` into a
  `GraphCsr` of `D.toGraph` is a second pass again with no landed
  program.

§1's handshake is deliberately stated for a general orientation, so
that the transpose leaf can discharge `AugSymCsrIn`'s own
`ns ≤ 2·arcCount` obligation with it when that pass is written.
-/

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
open Lax3Proofs.TgtCoupling (outNbrs mem_outNbrs sum_card_outNbrs)

/-! ## §1 The handshake: slots are twice the arcs

`SolveAugCompose` states the base pass's three budgets at
`arcCount (selChain sel A.G 0)` rather than at a slot count, and records
that the identity relating the two is landed nowhere. Here it is. -/

/-- **A vertex's neighbours split into its in- and out-arcs.** If `D`
orients `G` then every neighbour of `v` is at the far end of exactly one
arc of `D`. `asymm` is what makes the two halves disjoint, so this is a
genuine partition and not merely a cover. -/
theorem ncard_neighborSet_eq_card_inN_add_card_outNbrs {N : ℕ}
    {G : SimpleGraph (Fin N)} {D : Orientation N} (h : D.Orients G) (v : Fin N) :
    (G.neighborSet v).ncard = (D.inN v).card + (outNbrs D v).card := by
  classical
  have hdisj : Disjoint (D.inN v) (outNbrs D v) :=
    Finset.disjoint_left.2 fun u hu hu' => D.asymm u v hu (mem_outNbrs.1 hu')
  have hset :
      G.neighborSet v = ((D.inN v ∪ outNbrs D v : Finset (Fin N)) : Set (Fin N)) := by
    ext u
    simp only [SimpleGraph.mem_neighborSet, Finset.mem_coe, Finset.mem_union,
      mem_outNbrs]
    rw [h v u]
    exact ⟨Or.symm, Or.symm⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj]

/-- **The handshake.** The CSR slot count of `G` — the degree sum, which
is the figure every build pass's budget is charged at — is twice the arc
count of any orientation of `G`.

`SolveAugCompose` §6 states the base pass's budgets at `arcCount` and
not via a slot count precisely because this identity was landed nowhere;
it is proved here once, in the generality the whole augmentation frame
needs. For the base it is read at `baseOr A.G (selPerm sel A.G)`; for
the symmetrization it is what discharges `AugSymCsrIn`'s
`ns ≤ 2·arcCount` clause once that pass exists. -/
theorem sum_ncard_neighborSet_eq_two_mul_arcCount {N : ℕ}
    {G : SimpleGraph (Fin N)} {D : Orientation N} (h : D.Orients G) :
    ∑ v : Fin N, (G.neighborSet v).ncard = 2 * arcCount D := by
  classical
  calc ∑ v : Fin N, (G.neighborSet v).ncard
      = ∑ v : Fin N, ((D.inN v).card + (outNbrs D v).card) :=
        Finset.sum_congr rfl fun v _ =>
          ncard_neighborSet_eq_card_inN_add_card_outNbrs h v
    _ = (∑ v : Fin N, (D.inN v).card) + ∑ v : Fin N, (outNbrs D v).card :=
        Finset.sum_add_distrib
    _ = arcCount D + arcCount D := by
        rw [sum_card_outNbrs D]; simp only [arcCount]
    _ = 2 * arcCount D := by ring

/-- **The handshake, in the `slotCount` spelling** — the figure the
peel's linear budget (`linearPeelBudget`) is charged at. `slotCount` is
by definition the degree sum (`SolveSweepBucket.lean:239`), so this is
the previous theorem read at the name the peel uses. -/
theorem slotCount_eq_two_mul_arcCount {N : ℕ} {G : SimpleGraph (Fin N)}
    {D : Orientation N} (h : D.Orients G) : slotCount G = 2 * arcCount D :=
  sum_ncard_neighborSet_eq_two_mul_arcCount h

/-- **`slotCount G = 2·arcCount (baseOr G π)`** — the handshake exactly
as F6c12-5a's packet names it, and exactly as it was *not* landed
anywhere before this file. Every base pass whose cost is a constant per
CSR slot of `A.G` reads its budget into `augBaseBudget`'s
`arcCount (selChain sel A.G 0)` term through this. -/
theorem slotCount_eq_two_mul_arcCount_baseOr {N : ℕ} (G : SimpleGraph (Fin N))
    (π : Equiv.Perm (Fin N)) : slotCount G = 2 * arcCount (baseOr G π) :=
  slotCount_eq_two_mul_arcCount (baseOr_orients G π)

/-- **The handshake at round `0`.** `selChain sel G 0` is
`baseOr G (selPerm sel G)` (`selChain_zero`, `rfl`), which orients `G`
(`baseOr_orients`), so `G`'s slot count is twice round `0`'s arc count —
the reading that turns a build pass's `ns` term into the
`arcCount (selChain sel G 0)` term `augBaseBudget` is stated at. -/
theorem sum_ncard_neighborSet_eq_two_mul_arcCount_selChain_zero {N : ℕ}
    (sel : MinDegSel N) (G : SimpleGraph (Fin N)) :
    ∑ v : Fin N, (G.neighborSet v).ncard = 2 * arcCount (selChain sel G 0) := by
  rw [selChain_zero]
  exact sum_ncard_neighborSet_eq_two_mul_arcCount (baseOr_orients G (selPerm sel G))

/-! ## §2 The base's region build, discharged

`AugBaseAdjIn` at the landed `bldAdjCom`, read through the arena's
window. The route is `covAdjBuildIn_bldCom`'s and not
`adjBuildAt_bldAdjCom`'s, for the reason in the module docstring: the
arena's CSR arrays are `≥` its dimensions, and `AdjBuildAt`'s
`GraphCsr` clause pins them `=`. -/

/-- The two figures of an admissible arena are words. (The same fact
`covAdjBuildIn_bldCom` uses; it is `private` in `SolveSweepBuild`, so it
is re-derived here rather than reached for.) -/
private theorem sq_lt_mcB' {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {q : ℕ}
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
/-- **`AugBaseAdjIn`, discharged** — the first of the base pass's three,
at the landed program `bldAdjCom` and the budget
`81·A.N + 116·arcCount (selChain sel A.G 0) + 24`.

The pass materializes the deletable adjacency region of `A.G` at the
empty deleted set in the four names `bao, baj, bdg, bmt`, from the
arena's own CSR pair, leaving the arena, the two allocations and both
scratch descriptors intact.

Two things are worth naming about the proof:

* the arena's CSR is windowed (`ArenaStW`), so it is read into a
  `SrcCsr` by `srcCsr_of_graphCsr` at the window's `≤` lengths and fed
  to `bldAdj_spec`. `AdjBuildAt`, whose `GraphCsr` clause pins the two
  lengths exactly, is **not** usable here, and the direct
  `adjBuildAt_bldAdjCom` route — the one the symmetrization's build half
  takes, its CSR being in fresh arrays — is unavailable;
* the slot term is converted by §1's handshake and by nothing else:
  `SrcCsr.ns_eq_sum` reads the arena's `nS` cell as `A.G`'s degree sum,
  and that sum *is* `2·arcCount (selChain sel A.G 0)`, so `58·ns` is
  exactly `116·arcCount`.

The selection `sel` is free: round `0`'s arc count is `A.G`'s edge count
whatever the tie-break, so the conclusion holds at every selection and
in particular at `mdSel` and at `bucketSel`. -/
theorem augBaseAdjIn_bldAdjCom (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (bao baj bdg bmt raY odY : ℕ → String)
    (Sag Sbd Smp Ssw : ℕ → Env → Prop)
    (hq : 1 ≤ q)
    (hnm : ∀ j, BldNames (arenaNames j).off (arenaNames j).tgt (raY j)
      (bao j) (baj j) (bdg j) (bmt j) (odY j))
    (hcol : ∀ j, ∀ b ∈ [bao j, baj j, bdg j, bmt j],
      b ≠ (arenaNames j).col ∧ b ≠ (arenaNames j).up ∧ b ≠ (arenaNames j).hist)
    (hSag : ∀ j σ, Sag j σ →
      σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (bao j)).length ∧
      σ.vars (arenaNames j).nS ≤ (σ.arrs (baj j)).length ∧
      σ.vars (arenaNames j).nN ≤ (σ.arrs (bdg j)).length ∧
      σ.vars (arenaNames j).nS ≤ (σ.arrs (bmt j)).length)
    (hSbd : ∀ (j : ℕ) (σ σ' : Env), Sag j σ →
      (∀ b, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ bldScalars → σ'.vars y = σ.vars y) → Sbd j σ')
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ bldScalars → σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
        σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ bldScalars → σ'.vars y = σ.vars y) → Ssw j σ') :
    AugBaseAdjIn C hC φ sel G c w q ℓp htabF hbf Adm ca co
      bao baj bdg bmt Sag Sbd Smp Ssw
      (fun j => bldAdjCom (arenaNames j).nN (arenaNames j).nS
        (arenaNames j).off (arenaNames j).tgt (bao j) (baj j) (bdg j) (bmt j))
      81 116 24 := by
  intro x hx j hj A hAdm hbot σ hσ
  obtain ⟨hArena, hcaL, hcoL, hSg, hSm, hSw⟩ := hσ
  have hcl := bldCells_arenaNames j
  have hnmj := hnm j
  -- the two figures, and that they are words
  have henc : EncodesGraph x n G := hx.1
  have hnN : σ.vars (arenaNames j).nN = A.N := hArena.n_eq
  have hNn : A.N ≤ n := hArena.st.N_le_root
  have hxB : x.length + 1 < mcB q x := length_add_one_lt_mcB (three_le_length henc) hq
  have hlenx := henc.length_eq
  have hNB : A.N < mcB q x := by omega
  have hnsq : σ.vars (arenaNames j).nS ≤ A.N * A.N := hArena.ns_le_sq
  have hsq : n * n < mcB q x := sq_lt_mcB' henc hq
  have hnsB : σ.vars (arenaNames j).nS < mcB q x := by
    have h : A.N * A.N ≤ n * n := Nat.mul_le_mul hNn hNn
    omega
  -- the arena's CSR, read through the window
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
  obtain ⟨off, tgt, hsrc⟩ :=
    srcCsr_of_graphCsr hcsrw hoL htL
      (fun i hi => by
        rw [arrs_winA_some arenaWs_off, List.getElem?_take_of_lt (by omega)])
      (fun p hp => by
        rw [arrs_winA_some (arenaWs_tgt hot), List.getElem?_take_of_lt hp])
  -- the landed build, framed
  obtain ⟨hSao, hSaj, hSdg, hSmt⟩ := hSag j σ hSg
  rw [hnN] at hSao hSdg
  obtain ⟨σ', hrun, ⟨⟨-, hdel⟩, hfv, hfa, -, -⟩, hlen⟩ :=
    (specArrsLength (bldAdj_spec (G := A.G) (off := off) (tgt := tgt)
      (B := mcB q x) hnmj hcl hNB hnsB).frame).run
      ⟨hsrc, hnN, rfl, hSao, hSaj, hSdg, hSmt⟩
  -- the frame, in the two shapes the transports consume
  have hfa' : ∀ b, b ≠ bao j → b ≠ baj j → b ≠ bdg j → b ≠ bmt j →
      σ'.arrs b = σ.arrs b :=
    fun b h1 h2 h3 h4 => hfa b (not_mem_warrs_bldAdjCom h1 h2 h3 h4)
  have hfv' : ∀ y, y ∉ bldScalars → σ'.vars y = σ.vars y := by
    intro y hy
    simp only [bldScalars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hy
    exact hfv y (not_mem_wvars_bldAdjCom h0 h1 h2 h3 h4 h5)
  obtain ⟨hcolA, hupA, hhistA⟩ := hcol j (bao j) (by simp)
  obtain ⟨hcolJ, hupJ, hhistJ⟩ := hcol j (baj j) (by simp)
  obtain ⟨hcolD, hupD, hhistD⟩ := hcol j (bdg j) (by simp)
  obtain ⟨hcolM, hupM, hhistM⟩ := hcol j (bmt j) (by simp)
  refine ⟨σ', hrun.mono ?_, ?_, hdel, ?_, ?_, ?_, ?_, ?_⟩
  · -- the budget: the arena's slot count *is* twice round `0`'s arc count
    have hns : σ.vars (arenaNames j).nS
        = 2 * arcCount (selChain (sel A.N) A.G 0) := by
      rw [hsrc.ns_eq_sum]
      exact sum_ncard_neighborSet_eq_two_mul_arcCount_selChain_zero (sel A.N) A.G
    rw [hns]
    omega
  · -- the arena is intact
    exact arenaStW_of_eq hArena (hfv' _ hcl.nN_notMem) (hfv' _ hcl.nS_notMem)
      (hfa' _ (Ne.symm hnmj.ao_o) (Ne.symm hnmj.aj_o) (Ne.symm hnmj.dg_o)
        (Ne.symm hnmj.mt_o))
      (hfa' _ (Ne.symm hnmj.ao_t) (Ne.symm hnmj.aj_t) (Ne.symm hnmj.dg_t)
        (Ne.symm hnmj.mt_t))
      (hfa' _ (Ne.symm hcolA) (Ne.symm hcolJ) (Ne.symm hcolD) (Ne.symm hcolM))
      (hfa' _ (Ne.symm hupA) (Ne.symm hupJ) (Ne.symm hupD) (Ne.symm hupM))
      (hfa' _ (Ne.symm hhistA) (Ne.symm hhistJ) (Ne.symm hhistD) (Ne.symm hhistM))
  · exact hSbd j σ σ' hSg hfa' hfv'
  · rw [hlen (ca j)]; exact hcaL
  · rw [hlen (co j)]; exact hcoL
  · exact hSmp j σ σ' hSm hfa' hfv'
  · exact hSsw j σ σ' hSw hfa' hfv'

/-! ## §3 Axiom audit

§1 rests on the three standard axioms alone. §2's discharge quotes
`Headline.headlineSetup` in its statement and therefore — exactly like
the landed `covAdjBuildIn_bldCom` whose route it takes — additionally
carries Lax12's endorsed `uniformlyQuasiWide_of_nowhereDense`. -/

#print axioms ncard_neighborSet_eq_card_inN_add_card_outNbrs

#print axioms sum_ncard_neighborSet_eq_two_mul_arcCount

#print axioms slotCount_eq_two_mul_arcCount_baseOr

#print axioms sum_ncard_neighborSet_eq_two_mul_arcCount_selChain_zero

#print axioms augBaseAdjIn_bldAdjCom

end Lax3Proofs.Prog
