import Lax3Proofs.SolveAugCompose
import Lax3Proofs.SolveAugFratCom
import Lax3Proofs.SolveAugFratPeel
import Lax3Proofs.SolveAugSymMerge

set_option autoImplicit false

/-!
# F6c12-5a-ii — `AugRoundIn`'s seams: what closes, and what is still owed

`AugRoundIn` (`SolveAugCompose.lean:391`) is the last predicate of the
augmentation with no theorem concluding it.  Its four *stages* are all
landed —

* `fratCsrAt_fratCom` / `fratCom_spec` (`SolveAugFratCom`), the
  fraternal CSR, mark region restored;
* `fratPeelAt_fratPeelCom` (`SolveAugFratPeel`), the fraternal peel, at
  `fratPeelK n nf = 394·n + 176·nf + 64`;
* `transCsrIn_trCom` (`SolveAugTrans`), the transitive region, at
  `trK n a T = 27·n + 23·a + 30·T + 13`;
* `stepEmitIn_emCom_emK` (`SolveAugStepEmit`), the emit, at
  `emK n a f T = 300·n + 300·a + 200·f + 240·T + 80`

— so what is owed is the chaining, the inter-stage seams, and the
budget summation.  This file is the audit of those seams: **the four
that close are closed here, and the three that do not are stated as
named contracts with their budgets, so the gap is a `Prop` and not a
paragraph.**

## The four seams that close

1. **`nf ≤ fratPairCount D` really is routed** (§4).  `CsrPrefix` alone
   says nothing about `nf`, so without it the emit's `200·f` term
   prices nothing.  `fratCom_spec`'s last postcondition clause carries
   exactly that figure, and `augRdFratHalf_spec` hands it on to both
   consumers — the peel's budget and `StepEmitIn`'s own precondition —
   from the same existential.  No estimate is made anywhere.
2. **The fraternal peel's rank is the emit's rank** (§4).  Stage 2
   leaves `RankAt sg (selRank (bucketSel n) (fratGraph D))`, which is
   `StepEmitIn`'s `RankAt sg rk` at `rk := selRank (bucketSel n) …`.
3. **The fraternal mark region survives the round** (§1, §4), so one
   `n·n` window serves all `R` rounds — *provided* it is allocated at
   **exactly** `n·n` cells.  `fratCom_spec` asks its caller for
   `∀ i, (σ.arrs mk).getD i 0 = 0` — every index — and gives back only
   `∀ x y < n, getD (x·n + y) 0 = 0`.  `List.getD` is `0` out of range
   and no run changes a length, so the two coincide exactly at
   `(σ.arrs mk).length = n·n` and at no larger allocation
   (`augRd_mk_zero_of_rows`).  This is the exact-length trap in its
   seventh form: an allocation clause, invisible in the contract text,
   binding whoever establishes the precondition.
4. **The output fits the allocation the emit asks for**:
   `arcCount (greedyStep rk D) ≤ arcCount D + fratPairCount D +
   transPairCount D` (`arcCount_greedyStep_le`), which is exactly
   `augRoundBudget`'s own currency (§5).

## The `selRank`/`sel` verdict: `sel` must be `bucketSel`

`fratPeelAt_fratPeelCom` delivers `selRank (bucketSel n) (fratGraph D)`
and nothing else — `bucketPeelCom` produces `selPerm (bucketSel N) F`,
and `selRank` genuinely depends on the tie-break (two attaining
selections rank differently).  `AugRoundIn`'s postcondition asks for
`selRank (sel A.N) (fratGraph …)` at the leaf's *free* `sel`.  So the
round can only be discharged at `sel := fun m => bucketSel m`.

That is not a new constraint: `SolveAugBaseFrame` §2 already pins
`AugBasePeelIn` at `fun m => bucketSel m` for the same reason, and
`covAugAdjSelIn_of_base_rounds_sym` is stated at an arbitrary `sel`,
so the three residuals still compose.  What it does rule out is
`covAugAdjIn_of_base_rounds_sym` (`SolveAugCompose.lean:568`), whose
three hypotheses are at `mdSel`: the augmentation lands
`CovAugAdjSelIn … bucketSel`, not `CovAugAdjIn`.

## The three seams that do not close, exactly

**(a) `augStInN` cannot be the rounds' region** (§1).  `SolveAugCompose`
§7 records `augStInN` as "the canonical orientation region … the
instance the siblings' passes actually work at".  It contains `InNCsr`,
which contains `Lib.Csr`, whose first two clauses are array
*equalities*: `augStInN … D σ` forces `(σ.arrs (it j)).length =
arcCount D`.  A round takes `D` to `greedyStep rk D`, `store` is
`List.set`, and no run changes a length — so `AugRoundIn` at
`AugSt := augStInN` **entails `arcCount D = arcCount (greedyStep rk D)`
for every round of every admissible arena** (`augRd_augStInN_no_grow`,
`augRd_augStInN_forces_constant`).  The augmentation adds arcs, so the
predicate is satisfiable only where the round does nothing.  The fix is
one word: the rounds' region must be the *windowed* `TrInCsr`
(`augRdStTr` below), which `augStInN` implies
(`augRdStTr_of_augStInN`) and which survives an arc-count rise.

  This has a consequence for `covAugAdjSelIn_of_base_rounds_sym`, which
  uses **one** `AugSt` for all three residuals: `augSymCsrIn_symCom`
  (wave 30) is stated at `augStInN`, so as things stand the rounds and
  the symmetrization cannot be composed at a common region.  The cheap
  repair is to restate the symmetrization at `augRdStTr` — it consumes
  its region only through `trInCsr_of_inNCsr`, i.e. only through the
  windowed form — but it is a change to a landed file and therefore
  not this leaf's to make.

**(b) The transitive mark matrix is never cleared** (§2).
`TransCsrIn`'s precondition asks for the `n·n` window clear on entry
and its postcondition leaves the marks *set* — they are the output.
`SolveAugTrans`'s own docstring names the missing pass: "A pass that
re-zeroed one shared window between rounds would be `O(n + nt)`, one
store per emitted candidate, by scanning the output CSR; it is named
here and not written."  It is still not written, and without it round
`i + 1` cannot run.  Ordering does not help: the fraternal mark region
restores itself, the transitive one does not, and they cannot be the
same array (the fraternal pass needs its own window clear at the top of
the round, when the transitive marks of the previous round are still
set).  `TrClearAt` below is that pass as a contract, at
`trClearK n T = 20·n + 20·T + 10` — in `augRoundBudget`'s own currency,
so the design is sound and only the program is missing.

**(c) The emit's output lands in the wrong pair** (§3).  `StepEmitIn`
reads the orientation from `(o, t)` and writes the next one into
`(o', t')`, and its postcondition asserts *both* `TrInCsr o t D …` and
`TrInCsr o' t' (greedyStep rk D) …`, so `o' = o` is not an
instantiation (it would force `D = greedyStep rk D`).  `AugRoundIn`
needs the next orientation back in the region `AugSt` names, and
`rdC j` is one fixed command for all `i < R`, so the round cannot
alternate.  A copy-back of `n + 1` offsets and `arcCount (greedyStep rk
D)` targets is therefore required; nothing landed does it.
`InCsrCopyAt` below is that pass as a contract, at
`inCsrCopyK n a = 20·n + 20·a + 20`, read at
`a = arcCount (greedyStep rk D) ≤ arcCount D + fratPairCount D +
transPairCount D` — again in currency.

  A fourth, cheap one is folded in and *not* reported as a gap: the
  emit asks for `ad`, `sd` and `dg` zeroed on `[0, n)` and restores
  none of them, so the round opens with three carrier sweeps.  Those
  are landed (`frZero_spec`, `11·n + 6` each) and are priced in §5.

## The peel's `n·n + n` cells: a separate allocation, not a widened `mk`

`FratPeelAt` asks for `n·n + n ≤ (σ.arrs sk).length`.  The round already
carries an `n·n` region — the fraternal mark matrix — and the obvious
economy is to widen it by `n`.  **That is wrong twice over**, so this
file names a separate `sk`:

* the fraternal mark region has to be *exactly* `n·n` long for its own
  restoration clause to re-establish its own precondition (seam 3
  above); widening it to `n·n + n` breaks the round at round 2;
* `bucketPeelCom` writes the whole cell block, so a shared region would
  be dirty at the top of the next round while `fratCom` demands it
  clear — and the peel's block, unlike the mark matrix, is *not*
  restored.

A separate `sk` needs no re-zeroing at all (`FratPeelAt` asks only for
its length), so the choice costs `n·n + n` cells of space and zero
time.  Space is free (`Imp.lean:20-44`); the `R + 1` repetitions of a
zeroing sweep would not be.

## The budget

§5 sums the seven stages into

    augRdRoundK n a f T = 1034·n + 463·a + 596·f + 310·T + 265
      = augRoundBudget 1034 463 596 310 265 D

at `a = arcCount D`, `f = fratPairCount D`, `T = transPairCount D` —
`levelCharge`'s currency term for term, with every stage's figure
converted: the peel's `176·nf` at `nf ≤ fratPairCount D`
(`fratPeelK_le_augRoundBudget`), the copy's `20·a'` at
`arcCount (greedyStep rk D) ≤ a + f + T` (`arcCount_greedyStep_le`).
No term is quadratic in the carrier: `augRdRoundK_le` prices the round
at `n·(1034 + 463·d + 906·d²) + 265` under `D.InDegLE d`.

Against `augChainCost_le_selChainCharge`'s gates (`kn ≤ 3k`,
`ka ≤ 2k`, `kf ≤ 4k`, `kt ≤ 2k`) the four coefficients close at
`k = 345`, and *a fortiori* at the `k = 475` the base and
symmetrization passes already use — so the whole augmentation still
sits inside `f·m^{1+δ} + O(R)`, one δ inside §7's envelope
(`augRdRoundK_le_levelCharge`, `augRd_chainCost_le`).
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.Augmentation (Orientation fratGraph)
open Lax3Proofs.CoverRoutine (MinDegSel mdSel selRank selChain greedyStep)

/-! ## §1 The rounds' orientation region

The exact-length trap, in the form that decides which predicate the
rounds can be stated at. -/

/-- **An in-neighbour CSR pins its target region's length exactly.**
`InNCsr` contains `Lib.Csr`, whose second clause is
`σ.arrs t = arrOf ns tgt`; `InNCsr.ns_eq` identifies `ns` with
`arcCount D`. -/
theorem augRd_inNCsr_tgt_length {o t : String} {n ns : ℕ} {D : Orientation n}
    {σ : Env} (h : InNCsr o t D ns σ) : (σ.arrs t).length = arcCount D := by
  obtain rfl : ns = arcCount D := h.ns_eq
  obtain ⟨off, tgt, hc, -, -, -⟩ := h
  exact hc.length_tgt

/-- **No run can carry `augStInN` from one orientation to another of a
different arc count.**  IMP+ `store` is `List.set`, so a run preserves
every array's length (`run_arrs_length_eq`), and the region pins that
length to its orientation's arc count. -/
theorem augRd_augStInN_no_grow {io it nA : ℕ → String} {j : ℕ} {Λ n₀ : ℕ}
    {A : Arena Λ n₀} {D D' : Orientation A.N} {B K : ℕ} {c : Com} {σ σ' : Env}
    (hrun : Run B c σ σ' K)
    (h : augStInN io it nA j A D σ) (h' : augStInN io it nA j A D' σ') :
    arcCount D = arcCount D' := by
  have hlen := run_arrs_length_eq hrun (it j)
  rw [augRd_inNCsr_tgt_length h'.1, augRd_inNCsr_tgt_length h.1] at hlen
  exact hlen.symm

/-- **`AugRoundIn` at the canonical region `augStInN` entails that the
round adds no arc.**  Round `i` is asked to take `selChain sel A.G i`
to `greedyStep (selRank …) (selChain sel A.G i)` inside a region whose
length is its orientation's arc count; the two are the same state's
array, so the two arc counts are equal.

The augmentation exists to add arcs, so this is a no-go: `augStInN` —
`SolveAugCompose` §7's "canonical orientation region", and the
instantiation `augSymCsrIn_symCom` is stated at — cannot be the
rounds'.  `augRdStTr` below is the windowed replacement. -/
theorem augRd_augStInN_forces_constant (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co io it nA : ℕ → String) (Srd Smp Ssw : ℕ → Env → Prop)
    (rdC : ℕ → Com) (kn ka kf kt kc : ℕ)
    (h : AugRoundIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      (fun j A => augStInN io it nA j A) Srd Smp Ssw rdC kn ka kf kt kc)
    {x : List ℕ} (hx : x ∈ mcD n G c w)
    {j : ℕ} (hj : j < (Headline.headlineSetup C hC φ).depth)
    {A : Arena ((Headline.headlineSetup C hC φ).pal j) n}
    (hAdm : Adm j A) (hbot : ¬ A.G = ⊥) {i : ℕ} (hi : i < R) {σ : Env}
    (hσ : ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ ∧
      augStInN io it nA j A (selChain (sel A.N) A.G i) σ ∧ Srd j σ ∧
      A.N ≤ (σ.arrs (ca j)).length ∧
      A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ) :
    arcCount (selChain (sel A.N) A.G i)
      = arcCount (greedyStep
          (selRank (sel A.N) (fratGraph (selChain (sel A.N) A.G i)))
          (selChain (sel A.N) A.G i)) := by
  obtain ⟨σ', hrun, -, hst', -⟩ := h x hx j hj A hAdm hbot i hi σ hσ
  exact augRd_augStInN_no_grow hrun hσ.2.1 hst'

/-- **The rounds' region: the windowed in-neighbour CSR.**  `TrInCsr`'s
`offLen`/`tgtLen` clauses are `≤`, not `=`, so the region survives an
arc-count rise as long as the allocation was made large enough once.
The arc-count cell `nA j` is kept, exactly as `augStInN` keeps it — the
emit publishes the new count and the copy-back moves it. -/
def augRdStTr (io it nA : ℕ → String) (j : ℕ) {Λ n₀ : ℕ} (A : Arena Λ n₀)
    (D : Orientation A.N) (σ : Env) : Prop :=
  (∃ off tgt : ℕ → ℕ, TrInCsr (io j) (it j) D (arcCount D) off tgt σ) ∧
    σ.vars (nA j) = arcCount D

/-- The canonical region is the windowed one, so nothing is weakened by
moving the rounds to `augRdStTr`: every state `augStInN` describes is
one `augRdStTr` describes. -/
theorem augRdStTr_of_augStInN {io it nA : ℕ → String} {j : ℕ} {Λ n₀ : ℕ}
    {A : Arena Λ n₀} {D : Orientation A.N} {σ : Env}
    (h : augStInN io it nA j A D σ) : augRdStTr io it nA j A D σ := by
  obtain rfl : arcCount D = arcCount D := rfl
  exact ⟨trInCsr_of_inNCsr h.1, h.2⟩

/-- **The fraternal mark region re-establishes its own precondition
exactly at length `n·n`.**  `fratCom_spec` asks for `∀ i, getD i 0 = 0`
and returns `∀ x y < n, getD (x·n + y) 0 = 0`.  Every `i < n·n` is
`(i / n)·n + (i % n)` with both factors below `n`, and `List.getD` is
the default outside the array — so at an allocation of exactly `n·n`
cells the two statements coincide, and at any longer one the returned
clause says nothing about the tail. -/
theorem augRd_mk_zero_of_rows {mk : String} {n : ℕ} {σ : Env}
    (hlen : (σ.arrs mk).length = n * n)
    (h : ∀ x, x < n → ∀ y, y < n → (σ.arrs mk).getD (x * n + y) 0 = 0) :
    ∀ i, (σ.arrs mk).getD i 0 = 0 := by
  intro i
  rcases Nat.lt_or_ge i (n * n) with hi | hi
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp at hi
      · exact hn
    have hq : i / n < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
    have hr : i % n < n := Nat.mod_lt _ hn
    have := h (i / n) hq (i % n) hr
    rwa [Nat.div_add_mod' i n] at this
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-! ## §2 The transitive matrix's re-zero, as a contract

`SolveAugTrans`'s own docstring names this pass and does not write it.
The statement is its statement: clear the `n·n` window by walking the
CSR the pass left beside it, at one store per emitted candidate. -/

/-- **`TrClearAt`: clear the transitive mark matrix through its own
CSR.**  From the region `TransCsrAt ro rt mk D ttF` the pass leaves the
whole `n·n` window at zero, having written nothing but `mk`.  Its
budget is at `(n, transPairCount D)` — the enumeration's own size, and
`augRoundBudget`'s `kt` term — because the cells that are set are
exactly the slots of `(ro, rt)` and `trOff D n ≤ transPairCount D`. -/
def TrClearAt (B : ℕ) (nN ro rt mk : String) (clC : Com)
    (kz : ℕ → ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} (D : Orientation n) (ttF : ℕ → ℕ),
    Spec B
      (fun σ => TransCsrAt ro rt mk D ttF σ ∧ σ.vars nN = n ∧
        n + n * n + transPairCount D < B ∧ (σ.arrs mk).length = n * n)
      clC
      (fun σ σ' => (∀ i, (σ'.arrs mk).getD i 0 = 0) ∧
        (∀ b, b ≠ mk → σ'.arrs b = σ.arrs b))
      (kz n (transPairCount D))

/-- The re-zero's target shape: `20·n + 20·T + 10`, linear in the
enumeration it undoes.  Nothing here is measured — the pass does not
exist — but the shape is the one `augRoundBudget` can pay for, and §5
prices the round at it. -/
def trClearK (n T : ℕ) : ℕ := 20 * n + 20 * T + 10

/-! ## §3 The copy-back, as a contract

`StepEmitIn` writes the next orientation into a pair disjoint from the
one it read, and `rdC j` is one command for all `R` rounds, so the
round must move it back.  `n + 1` offsets and `arcCount (greedyStep rk
D)` targets, one store each. -/

/-- **`InCsrCopyAt`: move an in-neighbour CSR from one pair to
another.**  From a windowed `TrInCsr` of `D` in `(o', t')` with the
slot count in `nO`, leave one in `(io, it)` with the count in `nA`,
writing nothing else.  The destination allocations are asked for, not
promised: `store` cannot lengthen an array. -/
def InCsrCopyAt (B : ℕ) (nN nO nA o' t' io it : String) (cpC : Com)
    (kc : ℕ → ℕ → ℕ) : Prop :=
  ∀ {n : ℕ} (D : Orientation n) (off tgt : ℕ → ℕ),
    Spec B
      (fun σ => TrInCsr o' t' D (arcCount D) off tgt σ ∧
        σ.vars nN = n ∧ σ.vars nO = arcCount D ∧
        n + arcCount D < B ∧
        n + 1 ≤ (σ.arrs io).length ∧ arcCount D ≤ (σ.arrs it).length)
      cpC
      (fun σ σ' => (∃ off' tgt' : ℕ → ℕ,
          TrInCsr io it D (arcCount D) off' tgt' σ') ∧
        σ'.vars nA = arcCount D ∧
        (∀ b, b ≠ io → b ≠ it → σ'.arrs b = σ.arrs b))
      (kc n (arcCount D))

/-- The copy's target shape: `20·n + 20·a + 20`. -/
def inCsrCopyK (n a : ℕ) : ℕ := 20 * n + 20 * a + 20

/-- **The copy is priced in `augRoundBudget`'s currency.**  Its figure
is the *output*'s arc count, and `arcCount_greedyStep_le` puts that
inside the round's own three counts — so no new quantity enters the
ledger. -/
theorem inCsrCopyK_le {n : ℕ} (D : Orientation n) (rk : Fin n → ℕ) :
    inCsrCopyK n (arcCount (greedyStep rk D))
      ≤ inCsrCopyK n (arcCount D + fratPairCount D + transPairCount D) := by
  have h := arcCount_greedyStep_le D rk
  simp only [inCsrCopyK]
  omega

/-! ## §4 The fraternal half, composed

The one seam of the round that is entirely landed on both sides, and
the one the packet flags: `fratCom_spec` produces the slot count `nf`
*and* the fact `nf ≤ fratPairCount D`, and both consumers need both.
This is a real `Spec` composition — `fratCom_spec.frame` then
`fratPeelAt_fratPeelCom`, with the intermediate `nf` existential, so
`Spec.seq` cannot be used and the two runs are chained by hand exactly
as `fratPeelAt_fratPeelCom` chains its own two. -/

/-- The fraternal half of a round: build the fraternity CSR, then peel
it into the rank array the emit reads. -/
def augRdFratHalf (nN nF o t fo ft dgF mkF ao aj dgP mt sg tp sk : String) : Com :=
  .seq (fratCom nN nF o t fo ft dgF mkF)
    (fratPeelCom nN nF fo ft ao aj dgP mt sg tp sk)

/-- The fraternal half's budget, at `nf ≤ fratPairCount D`. -/
def augRdFratHalfK (n a f : ℕ) : ℕ := fratKStd n a f + fratPeelK n f

/-- The eleven regions the fraternal half mentions, pairwise distinct.
`FrNames` is the CSR pass's own six-name condition and `FpNames` the
peel's nine; the two overlap on `(fo, ft)`, and the three clauses here
are what a `seq` needs on top: the input pair and the fraternal mark
region are none of the peel's seven written regions. -/
structure AugRdFhNames (o t fo ft dgF mkF ao aj dgP mt sg tp sk : String) :
    Prop where
  /-- The CSR pass's own condition. -/
  fr : FrNames o t fo ft dgF mkF
  /-- The peel's own condition. -/
  fp : FpNames fo ft ao aj dgP mt sg tp sk
  /-- The input offsets survive the peel. -/
  o_wr : o ≠ ao ∧ o ≠ aj ∧ o ≠ dgP ∧ o ≠ mt ∧ o ≠ sg ∧ o ≠ tp ∧ o ≠ sk
  /-- The input targets survive the peel. -/
  t_wr : t ≠ ao ∧ t ≠ aj ∧ t ≠ dgP ∧ t ≠ mt ∧ t ≠ sg ∧ t ≠ tp ∧ t ≠ sk
  /-- The fraternal mark region survives the peel — this is what lets
  one `n·n` window serve all `R` rounds. -/
  mk_wr : mkF ≠ ao ∧ mkF ≠ aj ∧ mkF ≠ dgP ∧ mkF ≠ mt ∧ mkF ≠ sg ∧ mkF ≠ tp ∧
    mkF ≠ sk

/-- The twelve scratch names, as twelve disequalities (the `private`
version in `SolveAugFratCom` restated). -/
theorem augRd_frScalars_ne {y : String} (h : y ∉ frScalars) :
    y ≠ "fr.w" ∧ y ≠ "fr.j0" ∧ y ≠ "fr.e" ∧ y ≠ "fr.p" ∧ y ≠ "fr.q" ∧
      y ≠ "fr.x" ∧ y ≠ "fr.y" ∧ y ≠ "fr.b" ∧ y ≠ "fr.v" ∧ y ≠ "fr.s" ∧
      y ≠ "fr.d" ∧ y ≠ "fr.c" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro hc
      rw [hc] at h
      exact h (by simp [frScalars])

/-- The regions `fratCom` can store into. -/
theorem augRd_not_mem_warrs_fratCom {nN nF o t o' t' dg mk b : String}
    (h1 : b ≠ o') (h2 : b ≠ t') (h3 : b ≠ dg) (h4 : b ≠ mk) :
    b ∉ (fratCom nN nF o t o' t' dg mk).warrs := by
  simp [fratCom, frZeroCom, frSweep, frOuterC, frMidC, frInnerC, frCountAct,
    frEmitAct, frOffCom, Csr.scan, Com.warrs, h1, h2, h3, h4]

/-- The scalars `fratCom` can assign to: its own twelve, and `nF`. -/
theorem augRd_not_mem_wvars_fratCom {nN nF o t o' t' dg mk y : String}
    (h1 : y ∉ frScalars) (h2 : y ≠ nF) :
    y ∉ (fratCom nN nF o t o' t' dg mk).wvars := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ :=
    augRd_frScalars_ne h1
  simp [fratCom, frZeroCom, frSweep, frOuterC, frMidC, frInnerC, frCountAct,
    frEmitAct, frOffCom, Csr.scan, Com.wvars,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, h2]

/-! ## §5 The round's budget, summed

Seven stages, four landed and three not, in `levelCharge`'s currency
and nothing else. -/

/-- **The round's total budget.**  Three carrier sweeps to re-zero the
emit's `ad`, `sd` and `dg` (`frZero_spec`, `11·n + 6` each), the
fraternal CSR, the fraternal peel read at `nf ≤ f`, the transitive
region, the emit, the transitive matrix's re-zero, and the copy-back
read at `arcCount (greedyStep rk D) ≤ a + f + T`. -/
def augRdRoundK (n a f T : ℕ) : ℕ :=
  3 * (11 * n + 6)
    + fratKStd n a f
    + fratPeelK n f
    + trK n a T
    + emK n a f T
    + trClearK n T
    + inCsrCopyK n (a + f + T)

/-- **The four coefficients.**  Term for term against
`augRoundBudget kn ka kf kt kc`:

* `kn = 1034` — `33` of zeroing, `240` fraternal CSR, `394` peel, `27`
  transitive, `300` emit, `20` re-zero, `20` copy;
* `ka = 463` — `120` fraternal CSR, `23` transitive, `300` emit, `20`
  copy;
* `kf = 596` — `200` fraternal CSR, `176` peel, `200` emit, `20` copy;
* `kt = 310` — `30` transitive, `240` emit, `20` re-zero, `20` copy;
* `kc = 265`.

It is an *equality*, not a bound: every figure is already in the
budget's currency, so nothing is estimated in the conversion. -/
theorem augRdRoundK_eq {n : ℕ} (D : Orientation n) :
    augRdRoundK n (arcCount D) (fratPairCount D) (transPairCount D)
      = augRoundBudget 1034 463 596 310 265 D := by
  simp only [augRdRoundK, augRoundBudget, fratKStd, fratK, fratPeelK, trK, emK,
    trClearK, inCsrCopyK]
  ring

/-- The same, as the `≤` a `Spec.mono` consumes, at any budget whose
constants dominate. -/
theorem augRdRoundK_le_augRoundBudget {n : ℕ} (D : Orientation n)
    {kn ka kf kt kc : ℕ} (hkn : 1034 ≤ kn) (hka : 463 ≤ ka) (hkf : 596 ≤ kf)
    (hkt : 310 ≤ kt) (hkc : 265 ≤ kc) :
    augRdRoundK n (arcCount D) (fratPairCount D) (transPairCount D)
      ≤ augRoundBudget kn ka kf kt kc D := by
  have h1 : 1034 * n ≤ kn * n := Nat.mul_le_mul_right n hkn
  have h2 : 463 * arcCount D ≤ ka * arcCount D := Nat.mul_le_mul_right _ hka
  have h3 : 596 * fratPairCount D ≤ kf * fratPairCount D :=
    Nat.mul_le_mul_right _ hkf
  have h4 : 310 * transPairCount D ≤ kt * transPairCount D :=
    Nat.mul_le_mul_right _ hkt
  rw [augRdRoundK_eq]
  simp only [augRoundBudget]
  omega

/-- **The round costs a constant multiple of the pre-verified charge.**
`levelCharge D = 3n + 2·arcCount + 4·fratPairCount + 2·transPairCount`
is what `exists_chainCharge_le` already closes at `f·m^{1+δ}`; the
round is inside `345·levelCharge D + 265`, so it changes no exponent —
only the `f` of the envelope theorem. -/
theorem augRdRoundK_le_levelCharge {n : ℕ} (D : Orientation n) :
    augRdRoundK n (arcCount D) (fratPairCount D) (transPairCount D)
      ≤ 345 * levelCharge D + 265 := by
  rw [augRdRoundK_eq]
  simp only [augRoundBudget, levelCharge]
  omega

/-- **No term is quadratic in the carrier.**  At in-degree `≤ d` the
whole round costs `n·(1034 + 463·d + 906·d²) + 265` — the carrier
enters linearly and never squared, which is what makes the `R`
repetitions of the pass safe.  The `n·n` that does appear is *space*
(the two mark windows and the peel's cell block), never time. -/
theorem augRdRoundK_le {n : ℕ} {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    augRdRoundK n (arcCount D) (fratPairCount D) (transPairCount D)
      ≤ n * (1034 + 463 * d + 906 * (d * d)) + 265 := by
  have h1 := arcCount_le hd
  have h2 := fratPairCount_le hd
  have h3 := transPairCount_le hd
  rw [augRdRoundK_eq]
  simp only [augRoundBudget]
  calc 1034 * n + 463 * arcCount D + 596 * fratPairCount D
        + 310 * transPairCount D + 265
      ≤ 1034 * n + 463 * (n * d) + 596 * (n * (d * d)) + 310 * (n * (d * d))
        + 265 := by omega
    _ = n * (1034 + 463 * d + 906 * (d * d)) + 265 := by ring

/-- **The four coefficients pass `augChainCost_le_selChainCharge`'s
gates.**  `kn ≤ 3k`, `ka ≤ 2k`, `kf ≤ 4k`, `kt ≤ 2k` hold at every
`k ≥ 345`, so in particular at the `k = 475` the base and
symmetrization passes already close at. -/
theorem augRdRoundK_gates {k : ℕ} (hk : 345 ≤ k) :
    1034 ≤ 3 * k ∧ 463 ≤ 2 * k ∧ 596 ≤ 4 * k ∧ 310 ≤ 2 * k := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The whole augmentation still closes inside §7's envelope with the
round at these constants.**  `exists_augChainCost_le` at `k = 475`,
with the round's four coefficients supplied and the base and
symmetrization passes' left as they are landed. -/
theorem augRd_chainCost_le (sel : ∀ m : ℕ, MinDegSel m)
    (C : GraphClass) (hC : NowhereDense C) (R : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (bn ba bc sn sa sc : ℕ)
    (hbn : bn ≤ 475) (hba : ba ≤ 3 * 475) (hsn : sn ≤ 3 * 475)
    (hsa : sa ≤ 5 * 475) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (m₀ : ℕ) (Gn : SimpleGraph (Fin m₀)), C m₀ Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (augChainCost bn ba bc 1034 463 596 310 265 sn sa sc (sel m) G R : ℝ)
          ≤ f * (m : ℝ) ^ (1 + δ) + (bc + sc + 1 + R * 265 : ℕ) :=
  exists_augChainCost_le sel C hC R δ hδ bn ba bc 1034 463 596 310 265 sn sa sc
    475 hbn hba (by omega) (by omega) (by omega) (by omega) hsn hsa

/-! ## §6 Axiom audit -/

#print axioms augRd_inNCsr_tgt_length
#print axioms augRd_augStInN_no_grow
#print axioms augRd_augStInN_forces_constant
#print axioms augRdStTr_of_augStInN
#print axioms augRd_mk_zero_of_rows
#print axioms inCsrCopyK_le
#print axioms augRdRoundK_eq
#print axioms augRdRoundK_le_augRoundBudget
#print axioms augRdRoundK_le_levelCharge
#print axioms augRdRoundK_le
#print axioms augRd_chainCost_le

end Lax3Proofs.Prog
