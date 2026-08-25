import Lax3Proofs.SolveAugCompose
import Lax3Proofs.SolveAugFratCom
import Lax3Proofs.SolveAugFratPeel
import Lax3Proofs.SolveAugOrient
import Lax3Proofs.SolveAugStepEmit
import Lax3Proofs.SolveAugSymMerge

set_option autoImplicit false

/-!
# F6c12-5a-ii — `AugRoundIn`: the round composed, and the two passes it
still waits on

`AugRoundIn` (`SolveAugCompose.lean:391`) is the last predicate of the
augmentation with no theorem concluding it.  Its four *stages* are all
landed —

* `fratCom_spec` / `fratCsrAt_fratCom` (`SolveAugFratCom`), the
  fraternal CSR, mark region restored;
* `fratPeelAt_fratPeelCom` (`SolveAugFratPeel`), the fraternal peel, at
  `fratPeelK n nf = 394·n + 176·nf + 64`;
* `transCsrIn_trCom` (`SolveAugTrans`), the transitive region, at
  `trK n a T = 27·n + 23·a + 30·T + 13`;
* `stepEmitIn_emCom_emK` (`SolveAugStepEmit`), the emit, at
  `emK n a f T = 300·n + 300·a + 200·f + 240·T + 80`

— so what is owed is the chaining, the inter-stage seams, and the
budget summation.  **Three of the four stages are chained here into one
concrete command** (`augRdBody_spec`, §4b), and the two passes that
still separate that command from `AugRoundIn` are stated as named
contracts with their budgets (§2, §3), so what is missing is a `Prop`
and not a paragraph.

## What is proved here

1. **The fraternal CSR pass runs from the round's own windowed region**
   (§1b, `augRd_fratComW_spec`).  `fratCom_spec`'s precondition is the
   exact-length `InNCsr`, which at the machine's own state would demand
   `(σ.arrs t).length = arcCount D` — a figure that rises from round to
   round while an array's length cannot change.  `SolveChainWin`'s
   `specWindow` at the window `inWs o t n (arcCount D)` is the standing
   repair, and it carries the whole `Spec` verbatim.
2. **The fraternal half, composed** (§4, `augRdFratHalf_spec`): the
   windowed CSR pass then the landed peel, leaving `StepEmitIn`'s own
   `RankAt sg (selRank (bucketSel n) (fratGraph D))` and its own
   `CsrPrefix`, with `nf ≤ fratPairCount D` routed from the same
   existential — the clause without which the emit's `200·f` term
   prices nothing — and the fraternal mark region restored on **every**
   index.
3. **The round's body** (§4b, `augRdBody_spec`): the fraternal half,
   the transitive region and the emit, chained into
   `augRdBody`, leaving in `(o', t')` an in-neighbour CSR of
   `greedyStep (selRank (bucketSel n) (fratGraph D)) D` — round
   `i + 1` of the chain — with its arc count in `nO`.  This is
   everything a round *computes*.
4. **Its budget** (§4c, §5): `augRdBodyK n a f T = 961·n + 443·a +
   576·f + 270·T + 217`, an **equality** with
   `augRoundBudget 961 443 576 270 217 D` — every figure already in
   `levelCharge`'s currency, nothing estimated in the conversion.
5. **Anti-vacuity** (§4c): twenty-three concrete distinct region names
   discharging every hypothesis bundle (`augRdBody_names_std`), and the
   body's precondition proved **inhabited in full** from any state
   holding the orientation region (`exists_augRdAllocs`,
   `exists_augRdBodyPre`) — allocate, and nothing else.

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

**(a) The rounds' region must be `augStInNW`, and the symmetrization is
stated at `augStInN`** (§1).  `augStInN` (`SolveAugCompose` §7)
contains `InNCsr`, which contains `Lib.Csr`, whose first two clauses
are array *equalities*: `augStInN … D σ` forces
`(σ.arrs (it j)).length = arcCount D`.  A round takes `D` to
`greedyStep rk D`, `store` is `List.set`, and no run changes a length —
so `AugRoundIn` at `AugSt := augStInN` **entails
`arcCount D = arcCount (greedyStep rk D)` for every round of every
admissible arena** (`augRd_augStInN_no_grow`,
`augRd_augStInN_forces_constant`), and the augmentation exists to add
arcs.

  The repair is **landed, not owed**: `augStInNW`
  (`SolveAugOrient.lean:1921`) is `augStInN` read at the truncation,
  and `augBaseOrientIn_orCom` already delivers it, so that *is* the
  rounds' region.  What does not close is the far end:
  `augSymCsrIn_symCom` (wave 30) is stated at `augStInN`, and
  `augStInNW → augStInN` is false — the allocation is longer than the
  extent.  `covAugAdjSelIn_of_base_rounds_sym` uses **one** `AugSt` for
  all three residuals, so as things stand the rounds and the
  symmetrization cannot be composed at a common region.  The repair is
  one line in a landed file: `SolveAugSymMerge`'s own Finding 3 records
  that it consumes the region *only* through `trInCsr_of_inNCsr`, i.e.
  only through the windowed form, which is `augStInNW`'s first clause
  — so restating it at `augStInNW` costs nothing.  It is a change to a
  landed file and therefore not this leaf's to make.

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
`trClearK n T = 19·n + 23·T + 20` — in `augRoundBudget`'s own currency.
**Written in wave 32**: `SolveAugRoundIn`'s `ardClearCom` /
`ardClearAt`.

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
`inCsrCopyK n a = 12·n + 12·a + 32` — **written in wave 32**
(`SolveAugRoundIn`'s `ardCopyCom` / `ardCopyAt`) — read at
`a = arcCount (greedyStep rk D) ≤ arcCount D + fratPairCount D +
transPairCount D` — again in currency.

  A fourth, cheap one is folded in and *not* reported as a gap: the
  emit asks for `ad`, `sd` and `dg` zeroed on `[0, n)` and restores
  none of them, so the round opens with three carrier sweeps.  Those
  are landed (`frZero_spec`, `11·n + 6` each) and are priced in §5.
  `augRdBody_spec` asks for the three zeroed regions in its
  precondition rather than sweeping them, because one round does not
  need to restore what only the *next* round consumes.

**(d) The round's word bound has no landed route** (§4b).
`augRdBody_spec` asks for `n + n² + arcCount D + fratPairCount D +
transPairCount D < B` — the emit's own precondition, verbatim, and the
transitive pass's minus one term.  At `B = mcB q x` the landed material
supplies the first two (`SolveAugOrient`'s `sq_add_lt_mcB`,
`SolveAugSymMerge`'s `sq_lt_mcB`) and **nothing about the other
three**.  Under an in-degree bound the counts are `n·d`, `n·d²`, `n·d²`
(`arcCount_le`, `fratPairCount_le`, `transPairCount_le`), and
`exists_selChain_inDegLE_pow` gives the chain `d = ⌈c·m^δ⌉₊` — but no
theorem turns `n·d²` into `< mcB q x`.  `AugRoundIn`'s own docstring
names the hook ("a round pass needs its candidate counts to be words,
and that is available for the chain's own orientations — from
admissibility and `x ∈ mcD n G c w`"), and `Adm` is threaded through
every residual of the augmentation **with no landed instantiation at
all**.  So this is not an error, but it is an obligation nobody has
discharged, and it lands on whoever fixes `Adm`.

## The peel's `n·n + n` cells: a separate allocation, not a widened `mk`

`FratPeelAt` asks for `n·n + n ≤ (σ.arrs sk).length`.  The round already
carries an `n·n` region — the fraternal mark matrix — and the obvious
economy is to widen it by `n`.  **That is wrong twice over**, so this
file names a separate `sk`:

* the fraternal mark region has to be *exactly* `n·n` long for its own
  restoration clause to re-establish its own precondition
  (`augRd_mk_zero_of_rows`: `fratCom_spec` asks its caller for
  `∀ i, getD i 0 = 0` and gives back only `∀ x y < n,
  getD (x·n + y) 0 = 0`, and the two coincide at that length and at no
  larger one); widening it to `n·n + n` breaks the round at round 2;
* `bucketPeelCom` writes the whole cell block, so a shared region would
  be dirty at the top of the next round while `fratCom` demands it
  clear — and the peel's block, unlike the mark matrix, is *not*
  restored.

A separate `sk` needs no re-zeroing at all (`FratPeelAt` asks only for
its length), so the choice costs `n·n + n` cells of space and zero
time.  Space is free (`Imp.lean:20-44`); the `R + 1` repetitions of a
zeroing sweep would not be.

## The budget

§4c prices what is written: `augRdBodyK n a f T = 961·n + 443·a +
576·f + 270·T + 217`, at *equality* with
`augRoundBudget 961 443 576 270 217 D`.

§5 sums all seven stages — the three of §4b, the three carrier sweeps
and the two passes `SolveAugRoundIn` writes — into

    augRdRoundK n a f T = 1025·n + 455·a + 588·f + 305·T + 287
      = augRoundBudget 1025 455 588 305 287 D

at `a = arcCount D`, `f = fratPairCount D`, `T = transPairCount D` —
`levelCharge`'s currency term for term, with every stage's figure
converted: the peel's `176·nf` at `nf ≤ fratPairCount D`
(`fratPeelK_le_augRoundBudget`), the copy's `20·a'` at
`arcCount (greedyStep rk D) ≤ a + f + T` (`arcCount_greedyStep_le`).
The two named passes are now **written** (`SolveAugRoundIn` §2, §3) and
cost `64, 12, 12, 35, 70` of the five coefficients
(`augRdBodyK_le_augRdRoundK`).  No term is quadratic in the carrier:
`augRdRoundK_le` prices the round at
`n·(1025 + 455·d + 893·d²) + 287` under `D.InDegLE d`.

Against `augChainCost_le_selChainCharge`'s gates (`kn ≤ 3k`,
`ka ≤ 2k`, `kf ≤ 4k`, `kt ≤ 2k`) the four coefficients close at
`k = 342`, and *a fortiori* at the `k = 475` the base and
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
    (h : augStInN io it nA j A D σ) : augRdStTr io it nA j A D σ :=
  ⟨trInCsr_of_inNCsr h.1, h.2⟩

/-- The landed windowed region implies this file's, too: `augStInNW`
(`SolveAugOrient.lean:1921`) is what the base pass actually delivers,
and its first clause is `augRdStTr`'s. -/
theorem augRdStTr_of_augStInNW {io it nA : ℕ → String} {j : ℕ} {Λ n₀ : ℕ}
    {A : Arena Λ n₀} {D : Orientation A.N} {σ : Env}
    (h : augStInNW io it nA j A D σ) : augRdStTr io it nA j A D σ :=
  ⟨h.1, h.2.2⟩

/-- **`TrInCsr` transports along its own two regions.**  Every clause
naming the state names `σ.arrs o` or `σ.arrs t` and nothing else, so a
pass that writes neither carries the region across.  (`Csr.of_eq` is
this lemma for the exact-length relation; `TrInCsr` had none.) -/
theorem augRd_trInCsr_of_eq {o t : String} {n ns : ℕ} {D : Orientation n}
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

/-! ## §1b The fraternal CSR pass, at the *windowed* region

`fratCom_spec`'s precondition is `InNCsr o t D ns σ`, whose `Lib.Csr`
clauses are the two array **equalities** — so read at the machine's own
state it demands `(σ.arrs t).length = arcCount D`, a figure that rises
from round to round while an array's length cannot change.  Read that
way the pass could not be run twice.

It is not read that way.  `SolveAugOrient` Finding 1 records the
standing repair and `SolveChainWin.specWindow` performs it: the
exact-length relation is asserted of the **truncation** `winA`, and the
transport carries any such `Spec` verbatim to the max-size allocation.
Applied at the in-CSR window `inWs o t n (arcCount D)` it turns
`fratCom_spec` into a contract whose input is the windowed `TrInCsr` —
the shape every other stage of the round already speaks. -/

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

/-- **The fraternal CSR pass from a windowed in-neighbour CSR.**
`fratCom_spec` lifted through `specWindow` at `inWs o t n (arcCount D)`:
the input region is now `TrInCsr` (offsets and targets `≤`-allocated),
the four written regions are outside the window, and the budget is the
landed one unchanged.  The frame is carried along, because a round
composes with the next only if it knows what the pass did **not**
touch. -/
theorem augRd_fratComW_spec {B : ℕ} {nN nF o t o' t' dg mk : String}
    (hnm : FrNames o t o' t' dg mk) (hto : t ≠ o)
    (hnN : nN ∉ frScalars) (hnF : nF ∉ frScalars) (hFN : nF ≠ nN)
    {n : ℕ} (D : Orientation n) (off tgt : ℕ → ℕ) :
    Spec B
      (fun σ => TrInCsr o t D (arcCount D) off tgt σ ∧ σ.vars nN = n ∧
        n * n < B ∧ fratPairCount D < B ∧
        n + 1 ≤ (σ.arrs o').length ∧ fratPairCount D ≤ (σ.arrs t').length ∧
        n ≤ (σ.arrs dg).length ∧ n * n ≤ (σ.arrs mk).length ∧
        (∀ i, (σ.arrs mk).getD i 0 = 0))
      (fratCom nN nF o t o' t' dg mk)
      (fun σ σ' => TrInCsr o t D (arcCount D) off tgt σ' ∧
        (∃ nf : ℕ, CsrPrefix o' t' (fratGraph D) nf σ' ∧
          σ'.vars nF = nf ∧ nf ≤ fratPairCount D) ∧
        (∀ x, x < n → ∀ y, y < n → (σ'.arrs mk).getD (x * n + y) 0 = 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ∉ frScalars → y ≠ nF → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ o' → b ≠ t' → b ≠ dg → b ≠ mk → σ'.arrs b = σ.arrs b))
      (fratKStd n (arcCount D) (fratPairCount D)) := by
  classical
  have hwo : inWs o t n (arcCount D) o = some (n + 1) := inWs_o o t n (arcCount D)
  have hwt : inWs o t n (arcCount D) t = some (arcCount D) := inWs_t hto n (arcCount D)
  have hwn : ∀ b : String, b ≠ o → b ≠ t → inWs o t n (arcCount D) b = none := by
    intro b h1 h2; simp [inWs, h1, h2]
  have hno' : inWs o t n (arcCount D) o' = none :=
    hwn o' (Ne.symm hnm.o_o') (Ne.symm hnm.t_o')
  have hnt' : inWs o t n (arcCount D) t' = none :=
    hwn t' (Ne.symm hnm.o_t') (Ne.symm hnm.t_t')
  have hndg : inWs o t n (arcCount D) dg = none :=
    hwn dg (Ne.symm hnm.o_dg) (Ne.symm hnm.t_dg)
  have hnmk : inWs o t n (arcCount D) mk = none :=
    hwn mk (Ne.symm hnm.o_mk) (Ne.symm hnm.t_mk)
  refine (((specWindow (fratCom_spec hnm hnN hnF hFN D (arcCount D))
    (inWs o t n (arcCount D))).frame).pre ?_).post ?_
  · rintro σ ⟨hcsr, hnv, hB1, hB2, hoL, htL, hdL, hmL, hm0⟩
    refine ⟨?_, inNCsr_winA_of_trInCsr hto hcsr, hnv, hB1, hB2, ?_, ?_, ?_, ?_, ?_⟩
    · intro b m hb
      by_cases hbo : b = o
      · subst hbo; rw [hwo] at hb; cases hb; exact hcsr.offLen
      · by_cases hbt : b = t
        · subst hbt; rw [hwt] at hb; cases hb; exact hcsr.tgtLen
        · rw [hwn b hbo hbt] at hb; exact absurd hb (by simp)
    · rw [arrs_winA_none hno']; exact hoL
    · rw [arrs_winA_none hnt']; exact htL
    · rw [arrs_winA_none hndg]; exact hdL
    · rw [arrs_winA_none hnmk]; exact hmL
    · rw [arrs_winA_none hnmk]; exact hm0
  · rintro σ σ' ⟨hcsr, -⟩
      ⟨⟨-, ⟨-, nf, hpre, hnfv, hnfle, hmk0⟩, hlen, -⟩, hfv, hfa, -, -⟩
    have hfo : σ'.arrs o = σ.arrs o :=
      hfa o (augRd_not_mem_warrs_fratCom hnm.o_o' hnm.o_t' hnm.o_dg hnm.o_mk)
    have hft : σ'.arrs t = σ.arrs t :=
      hfa t (augRd_not_mem_warrs_fratCom hnm.t_o' hnm.t_t' hnm.t_dg hnm.t_mk)
    have ho'e : (winA (inWs o t n (arcCount D)) σ').arrs o' = σ'.arrs o' :=
      arrs_winA_none hno' σ'
    have ht'e : (winA (inWs o t n (arcCount D)) σ').arrs t' = σ'.arrs t' :=
      arrs_winA_none hnt' σ'
    have hmke : (winA (inWs o t n (arcCount D)) σ').arrs mk = σ'.arrs mk :=
      arrs_winA_none hnmk σ'
    refine ⟨augRd_trInCsr_of_eq hcsr hfo hft,
      ⟨nf, csrPrefix_of_eq hpre hnm.o'_t' ho'e.symm ht'e.symm, hnfv, hnfle⟩,
      ?_, hlen, ?_, ?_⟩
    · rw [← hmke]; exact hmk0
    · exact fun y hy1 hy2 => hfv y (augRd_not_mem_wvars_fratCom hy1 hy2)
    · exact fun b h1 h2 h3 h4 => hfa b (augRd_not_mem_warrs_fratCom h1 h2 h3 h4)

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
def trClearK (n T : ℕ) : ℕ := 19 * n + 23 * T + 20

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
        n + arcCount D + 1 < B ∧
        n + 1 ≤ (σ.arrs io).length ∧ arcCount D ≤ (σ.arrs it).length)
      cpC
      (fun σ σ' => (∃ off' tgt' : ℕ → ℕ,
          TrInCsr io it D (arcCount D) off' tgt' σ') ∧
        σ'.vars nA = arcCount D ∧
        (∀ b, b ≠ io → b ≠ it → σ'.arrs b = σ.arrs b))
      (kc n (arcCount D))

/-- The copy's measured shape: `12·n + 12·a + 32`
(`SolveAugRoundIn`'s `ardCopy_spec`). -/
def inCsrCopyK (n a : ℕ) : ℕ := 12 * n + 12 * a + 32

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
  /-- The fraternal degree region is none of the peel's seven either —
  needed to carry the peel's *own* seven allocations across the CSR
  pass, whose frame excludes it. -/
  dgF_wr : dgF ≠ ao ∧ dgF ≠ aj ∧ dgF ≠ dgP ∧ dgF ≠ mt ∧ dgF ≠ sg ∧ dgF ≠ tp ∧
    dgF ≠ sk

/-- The fraternity CSR pair against the peel's seven written regions —
the seven-and-seven half of `FpNames.nodup` the `seq` needs to carry
the peel's own allocations across the CSR pass. -/
theorem augRd_fpNames_csr {fo ft ao aj dgP mt sg tp sk : String}
    (h : FpNames fo ft ao aj dgP mt sg tp sk) :
    (fo ≠ ao ∧ fo ≠ aj ∧ fo ≠ dgP ∧ fo ≠ mt ∧ fo ≠ sg ∧ fo ≠ tp ∧ fo ≠ sk) ∧
      (ft ≠ ao ∧ ft ≠ aj ∧ ft ≠ dgP ∧ ft ≠ mt ∧ ft ≠ sg ∧ ft ≠ tp ∧ ft ≠ sk) := by
  have hnd := h.nodup
  simp only [fpArrs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  tauto

/-- **The fraternal half of a round, composed.**  `augRd_fratComW_spec`
(the windowed fraternal CSR) then `fratPeelAt_fratPeelCom` (the landed
peel), from the round's own windowed orientation region straight to

* `RankAt sg (selRank (bucketSel n) (fratGraph D))` — `StepEmitIn`'s
  ranking clause **verbatim**, so the emit's `sg` is this peel's `sg`;
* `CsrPrefix fo ft (fratGraph D) nf` together with
  `nf ≤ fratPairCount D` — `StepEmitIn`'s fraternal clause *and* the
  precondition without which its `200·f` term prices nothing.  Both
  come out of the same existential, so no estimate is made anywhere;
* the fraternal mark region restored to all-zero **on every index**,
  which re-establishes the CSR pass's own precondition and is what lets
  a single `n·n` window serve all `R` rounds.

The budget is `fratKStd n (arcCount D) f + fratPeelK n f`, the peel's
term read at `nf ≤ f` — the one conversion in the round's ledger, and
it is a `≤` between two figures of the *same* currency.

The mark region is asked for at **exactly** `n·n` cells.  That is not
tidiness: `fratCom_spec` returns `∀ x y < n, getD (x·n + y) 0 = 0` and
demands `∀ i, getD i 0 = 0`, and the two coincide at that length and no
longer one (`augRd_mk_zero_of_rows`).  The peel's `n·n + n` cells are a
*separate* region `sk` for the same reason. -/
theorem augRdFratHalf_spec {B : ℕ}
    {nN nF o t fo ft dgF mkF ao aj dgP mt sg tp sk : String}
    (hnm : AugRdFhNames o t fo ft dgF mkF ao aj dgP mt sg tp sk) (hto : t ≠ o)
    (hnN : nN ∉ frScalars) (hnF : nF ∉ frScalars) (hFN : nF ≠ nN)
    (hcl : FpCells nN nF)
    {n : ℕ} (D : Orientation n) (off tgt : ℕ → ℕ) :
    Spec B
      (fun σ => TrInCsr o t D (arcCount D) off tgt σ ∧ σ.vars nN = n ∧
        n * n < B ∧ fratPairCount D < B ∧ n + n * n + 1 < B ∧
        n + 1 ≤ (σ.arrs fo).length ∧ fratPairCount D ≤ (σ.arrs ft).length ∧
        n ≤ (σ.arrs dgF).length ∧ (σ.arrs mkF).length = n * n ∧
        (∀ i, (σ.arrs mkF).getD i 0 = 0) ∧
        n + 1 ≤ (σ.arrs ao).length ∧ fratPairCount D ≤ (σ.arrs aj).length ∧
        n ≤ (σ.arrs dgP).length ∧ fratPairCount D ≤ (σ.arrs mt).length ∧
        n ≤ (σ.arrs sg).length ∧ n ≤ (σ.arrs tp).length ∧
        n * n + n ≤ (σ.arrs sk).length)
      (augRdFratHalf nN nF o t fo ft dgF mkF ao aj dgP mt sg tp sk)
      (fun σ σ' => TrInCsr o t D (arcCount D) off tgt σ' ∧
        (∃ nf : ℕ, CsrPrefix fo ft (fratGraph D) nf σ' ∧
          σ'.vars nF = nf ∧ nf ≤ fratPairCount D) ∧
        RankAt sg (selRank (bucketSel n) (fratGraph D)) σ' ∧
        σ'.vars nN = n ∧
        (σ'.arrs mkF).length = n * n ∧ (∀ i, (σ'.arrs mkF).getD i 0 = 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ∉ frScalars → y ∉ fpScalars → y ≠ nF → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ fo → b ≠ ft → b ≠ dgF → b ≠ mkF → b ≠ ao → b ≠ aj →
          b ≠ dgP → b ≠ mt → b ≠ sg → b ≠ tp → b ≠ sk →
          σ'.arrs b = σ.arrs b))
      (augRdFratHalfK n (arcCount D) (fratPairCount D)) := by
  classical
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := hnm.o_wr
  obtain ⟨x1, x2, x3, x4, x5, x6, x7⟩ := hnm.t_wr
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hnm.mk_wr
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hnm.dgF_wr
  obtain ⟨⟨f1, f2, f3, f4, f5, f6, f7⟩, ⟨g1, g2, g3, g4, g5, g6, g7⟩⟩ :=
    augRd_fpNames_csr hnm.fp
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcsr, hnv, hB1, hB2, hB3, hfoL, hftL, hdgFL, hmkFL, hmkF0,
    haoL, hajL, hdgPL, hmtL, hsgL, htpL, hskL⟩ := hσ
  -- phase 1: the fraternity CSR, at the windowed input region
  obtain ⟨τ, hrun1, hcsr1, ⟨nf, hpre1, hnfv1, hnfle⟩, hmk1, hlen1, hfv1, hfa1⟩ :=
    (augRd_fratComW_spec hnm.fr hto hnN hnF hFN D off tgt).run
      ⟨hcsr, hnv, hB1, hB2, hfoL, hftL, hdgFL, le_of_eq hmkFL.symm, hmkF0⟩
  -- the peel's seven allocations are none of the CSR pass's four regions
  have hkeep : ∀ b : String, b ≠ fo → b ≠ ft → b ≠ dgF → b ≠ mkF →
      τ.arrs b = σ.arrs b := hfa1
  have haoτ : n + 1 ≤ (τ.arrs ao).length := by
    rw [hkeep ao (Ne.symm f1) (Ne.symm g1) (Ne.symm d1) (Ne.symm m1)]; exact haoL
  have hajτ : nf ≤ (τ.arrs aj).length := by
    rw [hkeep aj (Ne.symm f2) (Ne.symm g2) (Ne.symm d2) (Ne.symm m2)]; omega
  have hdgPτ : n ≤ (τ.arrs dgP).length := by
    rw [hkeep dgP (Ne.symm f3) (Ne.symm g3) (Ne.symm d3) (Ne.symm m3)]; exact hdgPL
  have hmtτ : nf ≤ (τ.arrs mt).length := by
    rw [hkeep mt (Ne.symm f4) (Ne.symm g4) (Ne.symm d4) (Ne.symm m4)]; omega
  have hsgτ : n ≤ (τ.arrs sg).length := by
    rw [hkeep sg (Ne.symm f5) (Ne.symm g5) (Ne.symm d5) (Ne.symm m5)]; exact hsgL
  have htpτ : n ≤ (τ.arrs tp).length := by
    rw [hkeep tp (Ne.symm f6) (Ne.symm g6) (Ne.symm d6) (Ne.symm m6)]; exact htpL
  have hskτ : n * n + n ≤ (τ.arrs sk).length := by
    rw [hkeep sk (Ne.symm f7) (Ne.symm g7) (Ne.symm d7) (Ne.symm m7)]; exact hskL
  have hnvτ : τ.vars nN = n := by rw [hfv1 nN hnN (Ne.symm hFN)]; exact hnv
  -- phase 2: the landed fraternal peel
  obtain ⟨σ', hrun2, hpre2, hrank, hfa2, hlen2, hfv2⟩ :=
    (fratPeelAt_fratPeelCom hnm.fp hcl D nf).run
      ⟨hpre1, hnvτ, hnfv1, hB3, haoτ, hajτ, hdgPτ, hmtτ, hsgτ, htpτ, hskτ⟩
  have hkeep2 : ∀ b : String, b ≠ ao → b ≠ aj → b ≠ dgP → b ≠ mt → b ≠ sg →
      b ≠ tp → b ≠ sk → σ'.arrs b = τ.arrs b := hfa2
  have hmkFσ' : σ'.arrs mkF = τ.arrs mkF := hkeep2 mkF m1 m2 m3 m4 m5 m6 m7
  have hmkFlen : (τ.arrs mkF).length = n * n := by rw [hlen1 mkF]; exact hmkFL
  refine ⟨σ', _, hrun1.seq hrun2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [augRdFratHalfK, fratPeelK]; omega
  · exact augRd_trInCsr_of_eq hcsr1 (hkeep2 o w1 w2 w3 w4 w5 w6 w7)
      (hkeep2 t x1 x2 x3 x4 x5 x6 x7)
  · exact ⟨nf, hpre2, by rw [hfv2 nF hcl.nF_notMem]; exact hnfv1, hnfle⟩
  · exact hrank
  · rw [hfv2 nN hcl.nN_notMem]; exact hnvτ
  · rw [hmkFσ', hmkFlen]
  · rw [hmkFσ']; exact augRd_mk_zero_of_rows hmkFlen hmk1
  · exact fun b => by rw [hlen2 b, hlen1 b]
  · intro y hy1 hy2 hy3
    rw [hfv2 y hy2, hfv1 y hy1 hy3]
  · intro b b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
    rw [hkeep2 b b5 b6 b7 b8 b9 b10 b11, hkeep b b1 b2 b3 b4]

/-! ## §4b The round's body: the fraternal half, the transitive region,
the emit

Three of the round's four computational stages, chained into one
command.  What comes out is the next orientation's in-neighbour CSR —
everything a round *computes*.  What is deliberately **not** here is
the two housekeeping passes §2 and §3 name: the transitive matrix is
left set and the output is left in `(o', t')`, so this is one round and
not `R` of them. -/

/-- The nine scratch names of the transitive pass, as nine
disequalities. -/
theorem augRd_trScalars_ne {y : String} (h : y ∉ trScalars) :
    y ≠ "tr.v" ∧ y ≠ "tr.j" ∧ y ≠ "tr.e" ∧ y ≠ "tr.w" ∧ y ≠ "tr.k" ∧
      y ≠ "tr.f" ∧ y ≠ "tr.z" ∧ y ≠ "tr.p" ∧ y ≠ "tr.b" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro hc
      rw [hc] at h
      exact h (by simp [trScalars])

/-- The regions `trCom` can store into: its own three. -/
theorem augRd_not_mem_warrs_trCom {nN nT o t ro rt mk b : String}
    (h1 : b ≠ ro) (h2 : b ≠ rt) (h3 : b ≠ mk) :
    b ∉ (trCom nN nT o t ro rt mk).warrs := by
  simp [trCom, trOuter, trMid, trInner, Csr.scan, Com.warrs, h1, h2, h3]

/-- The scalars `trCom` can assign to: its own nine, and `nT`. -/
theorem augRd_not_mem_wvars_trCom {nN nT o t ro rt mk y : String}
    (h1 : y ∉ trScalars) (h2 : y ≠ nT) :
    y ∉ (trCom nN nT o t ro rt mk).wvars := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := augRd_trScalars_ne h1
  simp [trCom, trOuter, trMid, trInner, Csr.scan, Com.wvars,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, h2]

/-- **The cross-stage separation.**  The eleven regions the fraternal
half writes are none of the thirteen the transitive pass and the emit
own — so the emit's three zeroed arrays and the transitive matrix's
clear window survive the fraternal half, and the fraternal mark
region's restoration survives the other two.  (`TrNames` and `EmNames`
supply everything *within* the last two stages, `EmNames.wrRd`
including `ro, rt, mkT` against the emit's seven.) -/
structure AugRdSep (fo ft dgF mkF ao aj dgP mt sg tp sk
    ro rt mkT o' t' qo qt ad sd dgE : String) : Prop where
  /-- No name of the first list is a name of the second. -/
  sep : ∀ a ∈ [fo, ft, dgF, mkF, ao, aj, dgP, mt, sg, tp, sk],
    ∀ b ∈ [ro, rt, mkT, o', t', qo, qt, ad, sd, dgE], a ≠ b

/-- The round's twenty working regions other than the fraternal mark
matrix — the ones whose allocation clauses are all `≤`. -/
def augRdAllocs (fo ft dgF ao aj dgP mt sg tp sk ro rt mkT o' t' qo qt ad sd
    dgE : String) : List String :=
  [fo, ft, dgF, ao, aj, dgP, mt, sg, tp, sk, ro, rt, mkT, o', t', qo, qt, ad,
    sd, dgE]

/-- The scalars `emCom` can assign to: the emit's own eight, the
transpose's ten, and the output count cell. -/
theorem augRd_mem_wvars_emCom
    {nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg y : String}
    (h : y ∈ (emCom nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg).wvars) :
    y ∈ emScalars ∨ y ∈ tpScalars ∨ y = nO := by
  simp only [emCom, emLoopCom, emHead, emRowScan, emStep, emCndIn, emCndOut,
    emCndFrat, emCndTrans, tpCom, tpCntCom, tpOffCom, tpScatCom, tpScatOut,
    tpScatIn, Csr.scan, Com.wvars, List.append_assoc, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.nil_append] at h
  simp only [emScalars, tpScalars, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- The same, contraposed — the shape a frame consumes. -/
theorem augRd_not_mem_wvars_emCom
    {nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg y : String}
    (h1 : y ∉ emScalars) (h2 : y ∉ tpScalars) (h3 : y ≠ nO) :
    y ∉ (emCom nN nO o t ro rt mk fo ft sg o' t' qo qt ad sd dg).wvars := by
  intro hc
  rcases augRd_mem_wvars_emCom hc with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

/-- **The round's body.**  `augRdFratHalf`, then the landed transitive
pass, then the landed emit. -/
def augRdBody (nN nF nT nO o t fo ft dgF mkF ao aj dgP mt sg tp sk
    ro rt mkT o' t' qo qt ad sd dgE : String) : Com :=
  .seq (augRdFratHalf nN nF o t fo ft dgF mkF ao aj dgP mt sg tp sk)
    (.seq (trCom nN nT o t ro rt mkT)
      (emCom nN nO o t ro rt mkT fo ft sg o' t' qo qt ad sd dgE))

/-- The body's budget: the fraternal half's, the transitive pass's and
the emit's, each at the figures `levelCharge` prices a round by. -/
def augRdBodyK (n a f T : ℕ) : ℕ :=
  augRdFratHalfK n a f + trK n a T + emK n a f T

/-- **The round's body, composed.**  From the round's own windowed
orientation region and the allocations, `augRdBody` leaves in
`(o', t')` an in-neighbour CSR of

  `greedyStep (selRank (bucketSel n) (fratGraph D)) D`

— round `i + 1` of the chain — with its arc count in `nO`, and the
fraternal mark region restored to all-zero at exactly `n·n` cells.

This is `AugRoundIn`'s postcondition data at the *emit's* output pair.
Turning it into `AugRoundIn` itself needs the two passes §2 and §3 name
and nothing else: the transitive matrix's re-zero and the copy-back
from `(o', t')` into `(o, t)`.

`selRank_lt` supplies the emit's `∀ v, rk v < B` from the word bound;
nothing else is assumed about the ranking. -/
theorem augRdBody_spec {B : ℕ}
    {nN nF nT nO o t fo ft dgF mkF ao aj dgP mt sg tp sk
      ro rt mkT o' t' qo qt ad sd dgE : String}
    (hfh : AugRdFhNames o t fo ft dgF mkF ao aj dgP mt sg tp sk)
    (htr : TrNames o t ro rt mkT)
    (hem : EmNames o t ro rt mkT fo ft sg o' t' qo qt ad sd dgE)
    (hsep : AugRdSep fo ft dgF mkF ao aj dgP mt sg tp sk
      ro rt mkT o' t' qo qt ad sd dgE)
    (hto : t ≠ o)
    (hnN : nN ∉ frScalars) (hnF : nF ∉ frScalars) (hFN : nF ≠ nN)
    (hcl : FpCells nN nF)
    (hnNtr : nN ∉ trScalars) (hnFtr : nF ∉ trScalars)
    (hnNT : nN ≠ nT) (hnFT : nF ≠ nT)
    (hnNem : nN ∉ emScalars) (hnNtp : nN ∉ tpScalars) (hnNO : nN ≠ nO)
    {n : ℕ} (D : Orientation n) (off tgt : ℕ → ℕ) :
    Spec B
      (fun σ => TrInCsr o t D (arcCount D) off tgt σ ∧ σ.vars nN = n ∧
        n + n * n + 1 < B ∧
        n + n * n + arcCount D + fratPairCount D + transPairCount D < B ∧
        n + 1 ≤ (σ.arrs fo).length ∧ fratPairCount D ≤ (σ.arrs ft).length ∧
        n ≤ (σ.arrs dgF).length ∧ (σ.arrs mkF).length = n * n ∧
        (∀ i, (σ.arrs mkF).getD i 0 = 0) ∧
        n + 1 ≤ (σ.arrs ao).length ∧ fratPairCount D ≤ (σ.arrs aj).length ∧
        n ≤ (σ.arrs dgP).length ∧ fratPairCount D ≤ (σ.arrs mt).length ∧
        n ≤ (σ.arrs sg).length ∧ n ≤ (σ.arrs tp).length ∧
        n * n + n ≤ (σ.arrs sk).length ∧
        n + 1 ≤ (σ.arrs ro).length ∧ transPairCount D ≤ (σ.arrs rt).length ∧
        n * n ≤ (σ.arrs mkT).length ∧
        (∀ i, i < n * n → (σ.arrs mkT).getD i 0 = 0) ∧
        n + 1 ≤ (σ.arrs o').length ∧
        arcCount D + fratPairCount D + transPairCount D ≤ (σ.arrs t').length ∧
        n + 1 ≤ (σ.arrs qo).length ∧ arcCount D ≤ (σ.arrs qt).length ∧
        n ≤ (σ.arrs ad).length ∧ n ≤ (σ.arrs sd).length ∧
        n ≤ (σ.arrs dgE).length ∧
        (∀ i, i < n → (σ.arrs ad).getD i 0 = 0) ∧
        (∀ i, i < n → (σ.arrs sd).getD i 0 = 0) ∧
        (∀ i, i < n → (σ.arrs dgE).getD i 0 = 0))
      (augRdBody nN nF nT nO o t fo ft dgF mkF ao aj dgP mt sg tp sk
        ro rt mkT o' t' qo qt ad sd dgE)
      (fun σ σ' =>
        (∃ off' tgt' : ℕ → ℕ,
          TrInCsr o' t' (greedyStep (selRank (bucketSel n) (fratGraph D)) D)
            (arcCount (greedyStep (selRank (bucketSel n) (fratGraph D)) D))
            off' tgt' σ') ∧
        σ'.vars nO =
          arcCount (greedyStep (selRank (bucketSel n) (fratGraph D)) D) ∧
        (σ'.arrs mkF).length = n * n ∧
        (∀ i, (σ'.arrs mkF).getD i 0 = 0) ∧
        (∃ ttF : ℕ → ℕ, TransCsrAt ro rt mkT D ttF σ') ∧
        σ'.vars nN = n ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ∉ frScalars → y ∉ fpScalars → y ∉ trScalars → y ∉ emScalars →
          y ∉ tpScalars → y ≠ nF → y ≠ nT → y ≠ nO → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ mkF →
          b ∉ augRdAllocs fo ft dgF ao aj dgP mt sg tp sk ro rt mkT o' t' qo qt
            ad sd dgE → σ'.arrs b = σ.arrs b))
      (augRdBodyK n (arcCount D) (fratPairCount D) (transPairCount D)) := by
  classical
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcsr, hnv, hB1, hB2, hfoL, hftL, hdgFL, hmkFL, hmkF0,
    haoL, hajL, hdgPL, hmtL, hsgL, htpL, hskL,
    hroL, hrtL, hmkTL, hmkT0, ho'L, ht'L, hqoL, hqtL, hadL, hsdL, hdgEL,
    had0, hsd0, hdgE0⟩ := hσ
  -- the fraternal half writes none of the last two stages' thirteen
  have hkeepA : ∀ b ∈ [ro, rt, mkT, o', t', qo, qt, ad, sd, dgE],
      ∀ τ τ' : Env,
      (∀ c, c ≠ fo → c ≠ ft → c ≠ dgF → c ≠ mkF → c ≠ ao → c ≠ aj →
        c ≠ dgP → c ≠ mt → c ≠ sg → c ≠ tp → c ≠ sk → τ'.arrs c = τ.arrs c) →
      τ'.arrs b = τ.arrs b := by
    intro b hb τ τ' hfr
    exact hfr b (Ne.symm (hsep.sep fo (by simp) b hb))
      (Ne.symm (hsep.sep ft (by simp) b hb))
      (Ne.symm (hsep.sep dgF (by simp) b hb))
      (Ne.symm (hsep.sep mkF (by simp) b hb))
      (Ne.symm (hsep.sep ao (by simp) b hb))
      (Ne.symm (hsep.sep aj (by simp) b hb))
      (Ne.symm (hsep.sep dgP (by simp) b hb))
      (Ne.symm (hsep.sep mt (by simp) b hb))
      (Ne.symm (hsep.sep sg (by simp) b hb))
      (Ne.symm (hsep.sep tp (by simp) b hb))
      (Ne.symm (hsep.sep sk (by simp) b hb))
  -- phase A: the fraternal half
  obtain ⟨τ, hrunA, hcsrA, ⟨nf, hfratA, hnfvA, hnfleA⟩, hrankA, hnvA,
    hmkFlA, hmkF0A, hlenA, hfvA, hfrA⟩ :=
    (augRdFratHalf_spec (B := B) hfh hto hnN hnF hFN hcl D off tgt).run
      ⟨hcsr, hnv, by omega, by omega, by omega, hfoL, hftL, hdgFL, hmkFL, hmkF0,
        haoL, hajL, hdgPL, hmtL, hsgL, htpL, hskL⟩
  have hAro : τ.arrs ro = σ.arrs ro := hkeepA ro (by simp) σ τ hfrA
  have hArt : τ.arrs rt = σ.arrs rt := hkeepA rt (by simp) σ τ hfrA
  have hAmkT : τ.arrs mkT = σ.arrs mkT := hkeepA mkT (by simp) σ τ hfrA
  have hAo' : τ.arrs o' = σ.arrs o' := hkeepA o' (by simp) σ τ hfrA
  have hAt' : τ.arrs t' = σ.arrs t' := hkeepA t' (by simp) σ τ hfrA
  have hAqo : τ.arrs qo = σ.arrs qo := hkeepA qo (by simp) σ τ hfrA
  have hAqt : τ.arrs qt = σ.arrs qt := hkeepA qt (by simp) σ τ hfrA
  have hAad : τ.arrs ad = σ.arrs ad := hkeepA ad (by simp) σ τ hfrA
  have hAsd : τ.arrs sd = σ.arrs sd := hkeepA sd (by simp) σ τ hfrA
  have hAdgE : τ.arrs dgE = σ.arrs dgE := hkeepA dgE (by simp) σ τ hfrA
  -- phase B: the transitive region
  obtain ⟨ρ, hrunB, ⟨hcsrB, ttF, htrB, hnTB⟩, hfvB, hfaB, -, -⟩ :=
    ((transCsrIn_trCom (B := B) (nT := nT) htr hnNtr D (arcCount D) off tgt).frame).run
      ⟨hcsrA, hnvA, by omega, by rw [hAro]; exact hroL, by rw [hArt]; exact hrtL,
        by rw [hAmkT]; exact hmkTL, by rw [hAmkT]; exact hmkT0⟩
  have hkeepB : ∀ b : String, b ≠ ro → b ≠ rt → b ≠ mkT → ρ.arrs b = τ.arrs b :=
    fun b h1 h2 h3 => hfaB b (augRd_not_mem_warrs_trCom h1 h2 h3)
  -- `EmNames.wrRd` keeps the emit's seven written regions off the
  -- transitive pass's three, so its allocations and its three zeroed
  -- arrays cross phase B unchanged
  have hemW : ∀ a ∈ emWr o' t' qo qt ad sd dgE, a ≠ ro ∧ a ≠ rt ∧ a ≠ mkT :=
    fun a ha => ⟨hem.wrRd a ha ro (by simp [emRd]),
      hem.wrRd a ha rt (by simp [emRd]), hem.wrRd a ha mkT (by simp [emRd])⟩
  have hBo' : ρ.arrs o' = σ.arrs o' := by
    obtain ⟨e1, e2, e3⟩ := hemW o' (by simp [emWr])
    rw [hkeepB o' e1 e2 e3, hAo']
  have hBt' : ρ.arrs t' = σ.arrs t' := by
    obtain ⟨e1, e2, e3⟩ := hemW t' (by simp [emWr])
    rw [hkeepB t' e1 e2 e3, hAt']
  have hBqo : ρ.arrs qo = σ.arrs qo := by
    obtain ⟨e1, e2, e3⟩ := hemW qo (by simp [emWr])
    rw [hkeepB qo e1 e2 e3, hAqo]
  have hBqt : ρ.arrs qt = σ.arrs qt := by
    obtain ⟨e1, e2, e3⟩ := hemW qt (by simp [emWr])
    rw [hkeepB qt e1 e2 e3, hAqt]
  have hBad : ρ.arrs ad = σ.arrs ad := by
    obtain ⟨e1, e2, e3⟩ := hemW ad (by simp [emWr])
    rw [hkeepB ad e1 e2 e3, hAad]
  have hBsd : ρ.arrs sd = σ.arrs sd := by
    obtain ⟨e1, e2, e3⟩ := hemW sd (by simp [emWr])
    rw [hkeepB sd e1 e2 e3, hAsd]
  have hBdgE : ρ.arrs dgE = σ.arrs dgE := by
    obtain ⟨e1, e2, e3⟩ := hemW dgE (by simp [emWr])
    rw [hkeepB dgE e1 e2 e3, hAdgE]
  -- the fraternity CSR, the ranking and the fraternal mark region
  -- cross phase B too: `AugRdSep` keeps them off `(ro, rt, mkT)`
  have hBfo : ρ.arrs fo = τ.arrs fo :=
    hkeepB fo (hsep.sep fo (by simp) ro (by simp))
      (hsep.sep fo (by simp) rt (by simp)) (hsep.sep fo (by simp) mkT (by simp))
  have hBft : ρ.arrs ft = τ.arrs ft :=
    hkeepB ft (hsep.sep ft (by simp) ro (by simp))
      (hsep.sep ft (by simp) rt (by simp)) (hsep.sep ft (by simp) mkT (by simp))
  have hBsg : ρ.arrs sg = τ.arrs sg :=
    hkeepB sg (hsep.sep sg (by simp) ro (by simp))
      (hsep.sep sg (by simp) rt (by simp)) (hsep.sep sg (by simp) mkT (by simp))
  have hBmkF : ρ.arrs mkF = τ.arrs mkF :=
    hkeepB mkF (hsep.sep mkF (by simp) ro (by simp))
      (hsep.sep mkF (by simp) rt (by simp))
      (hsep.sep mkF (by simp) mkT (by simp))
  have hnvB : ρ.vars nN = n := by
    rw [hfvB nN (augRd_not_mem_wvars_trCom hnNtr hnNT)]; exact hnvA
  have hnfvB : ρ.vars nF = nf := by
    rw [hfvB nF (augRd_not_mem_wvars_trCom hnFtr hnFT)]; exact hnfvA
  -- phase C: the emit
  obtain ⟨σ', hrunC, ⟨-, htrC, -, -, hfaC, off', tgt', hemC, hnOC⟩, hfvC, -, -, -⟩ :=
    ((stepEmitIn_emCom_emK (B := B) (nF := nF) (nO := nO) hem hnNem hnNtp D
      (selRank (bucketSel n) (fratGraph D)) (arcCount D) nf off tgt ttF).frame).run
      ⟨hcsrB, htrB,
        csrPrefix_of_eq hfratA hem.fo_ft hBfo hBft,
        ⟨by rw [hBsg]; exact hrankA.1, by rw [hBsg]; exact hrankA.2⟩,
        hnvB, hnfvB, hnfleA, by omega,
        (fun v => lt_of_lt_of_le (Lax3Proofs.CoverRoutine.selRank_lt _ _ v)
          (by omega)),
        by rw [hBo']; exact ho'L, by rw [hBt']; exact ht'L,
        by rw [hBqo]; exact hqoL, by rw [hBqt]; exact hqtL,
        by rw [hBad]; exact hadL, by rw [hBsd]; exact hsdL,
        by rw [hBdgE]; exact hdgEL,
        by rw [hBad]; exact had0, by rw [hBsd]; exact hsd0,
        by rw [hBdgE]; exact hdgE0⟩
  -- the fraternal mark region crosses the emit as well
  have hCmkF : σ'.arrs mkF = ρ.arrs mkF := by
    refine hfaC mkF ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      first
        | exact hsep.sep mkF (by simp) o' (by simp)
        | exact hsep.sep mkF (by simp) t' (by simp)
        | exact hsep.sep mkF (by simp) qo (by simp)
        | exact hsep.sep mkF (by simp) qt (by simp)
        | exact hsep.sep mkF (by simp) ad (by simp)
        | exact hsep.sep mkF (by simp) sd (by simp)
        | exact hsep.sep mkF (by simp) dgE (by simp)
  have hrun : Run B _ σ σ' _ := hrunA.seq (hrunB.seq hrunC)
  refine ⟨σ', _, hrun, ?_, ⟨off', tgt', hemC⟩, hnOC, ?_, ?_, ⟨ttF, htrC⟩, ?_, ?_,
    ?_, ?_⟩
  · simp only [augRdBodyK]; omega
  · rw [hCmkF, hBmkF]; exact hmkFlA
  · rw [hCmkF, hBmkF]; exact hmkF0A
  · rw [hfvC nN (augRd_not_mem_wvars_emCom hnNem hnNtp hnNO)]; exact hnvB
  · intro b; exact run_arrs_length_eq hrun b
  · intro y hy1 hy2 hy3 hy4 hy5 hy6 hy7 hy8
    rw [hfvC y (augRd_not_mem_wvars_emCom hy4 hy5 hy8),
      hfvB y (augRd_not_mem_wvars_trCom hy3 hy7), hfvA y hy1 hy2 hy6]
  · intro b hbmk hballoc
    simp only [augRdAllocs, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hballoc
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15,
      q16, q17, q18, q19, q20⟩ := hballoc
    rw [hfaC b q14 q15 q16 q17 q18 q19 q20, hkeepB b q11 q12 q13,
      hfrA b q1 q2 q3 hbmk q4 q5 q6 q7 q8 q9 q10]

/-! ### §4c Anti-vacuity: the body's precondition is inhabited

A descriptor left as a parameter constrained only through implications
is satisfied by `fun _ _ => False`, and `Srd j σ` sits in
`AugRoundIn`'s *pre*condition as well as its post — so a discharge at
an unsatisfiable descriptor would be true and empty.  Here the round's
twenty-one working regions are exhibited **concretely** and the whole
precondition of `augRdBody_spec` is proved inhabited from any state
holding the orientation region: allocate, and nothing else. -/

private theorem augRd_getD_replicate (m i : ℕ) :
    (List.replicate m (0 : ℕ)).getD i 0 = 0 := by
  rcases Nat.lt_or_ge i m with h | h
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
    rfl

/-- **Every allocation the round's body asks for is establishable, from
any state, by allocating and nothing else.**  Twenty regions at one
generous common length and the fraternal mark matrix at **exactly**
`n·n`; memory starts zeroed, so the four zeroing clauses come free with
the allocation (`Imp.lean:20-44`).

The only name condition is the one the exact length forces: `mkF` is
none of the other twenty.  Everything else may collide without making
the *allocation* unmeetable — distinctness is what the passes need, not
what the memory does. -/
theorem exists_augRdAllocs {fo ft dgF mkF ao aj dgP mt sg tp sk
    ro rt mkT o' t' qo qt ad sd dgE : String}
    (hmk : mkF ∉ augRdAllocs fo ft dgF ao aj dgP mt sg tp sk ro rt mkT o' t'
      qo qt ad sd dgE)
    (n a f T : ℕ) (σ : Env) :
    ∃ σ' : Env, σ'.vars = σ.vars ∧
      (∀ b, b ≠ mkF →
        b ∉ augRdAllocs fo ft dgF ao aj dgP mt sg tp sk ro rt mkT o' t' qo qt
          ad sd dgE → σ'.arrs b = σ.arrs b) ∧
      n + 1 ≤ (σ'.arrs fo).length ∧ f ≤ (σ'.arrs ft).length ∧
      n ≤ (σ'.arrs dgF).length ∧ (σ'.arrs mkF).length = n * n ∧
      (∀ i, (σ'.arrs mkF).getD i 0 = 0) ∧
      n + 1 ≤ (σ'.arrs ao).length ∧ f ≤ (σ'.arrs aj).length ∧
      n ≤ (σ'.arrs dgP).length ∧ f ≤ (σ'.arrs mt).length ∧
      n ≤ (σ'.arrs sg).length ∧ n ≤ (σ'.arrs tp).length ∧
      n * n + n ≤ (σ'.arrs sk).length ∧
      n + 1 ≤ (σ'.arrs ro).length ∧ T ≤ (σ'.arrs rt).length ∧
      n * n ≤ (σ'.arrs mkT).length ∧
      (∀ i, i < n * n → (σ'.arrs mkT).getD i 0 = 0) ∧
      n + 1 ≤ (σ'.arrs o').length ∧ a + f + T ≤ (σ'.arrs t').length ∧
      n + 1 ≤ (σ'.arrs qo).length ∧ a ≤ (σ'.arrs qt).length ∧
      n ≤ (σ'.arrs ad).length ∧ n ≤ (σ'.arrs sd).length ∧
      n ≤ (σ'.arrs dgE).length ∧
      (∀ i, i < n → (σ'.arrs ad).getD i 0 = 0) ∧
      (∀ i, i < n → (σ'.arrs sd).getD i 0 = 0) ∧
      (∀ i, i < n → (σ'.arrs dgE).getD i 0 = 0) := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : List String, L = augRdAllocs fo ft dgF ao aj dgP mt sg
      tp sk ro rt mkT o' t' qo qt ad sd dgE := ⟨_, rfl⟩
  rw [← hL] at hmk ⊢
  obtain ⟨F, hF⟩ : ∃ F : String → List ℕ, F = fun b =>
      if b = mkF then List.replicate (n * n) 0
      else if b ∈ L then List.replicate (n * n + n + a + f + T + 1) 0
      else σ.arrs b := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Env, τ = { σ with arrs := F } := ⟨_, rfl⟩
  have hFa : ∀ b, τ.arrs b = F b := fun b => by rw [hτ]
  have hmkF : F mkF = List.replicate (n * n) 0 := by rw [hF]; simp
  have hmem : ∀ x, x ∈ L →
      F x = List.replicate (n * n + n + a + f + T + 1) 0 := by
    intro x hx
    have hxm : x ≠ mkF := fun h => hmk (h ▸ hx)
    rw [hF]; simp [hxm, hx]
  refine ⟨τ, by rw [hτ], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b h1 h2; rw [hFa, hF]; simp [h1, h2]
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmkF]; simp
  · intro i; rw [hFa, hmkF]; exact augRd_getD_replicate _ _
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · intro i _
    rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    exact augRd_getD_replicate _ _
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    simp only [List.length_replicate]; omega
  · intro i _
    rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    exact augRd_getD_replicate _ _
  · intro i _
    rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    exact augRd_getD_replicate _ _
  · intro i _
    rw [hFa, hmem _ (by simp [hL, augRdAllocs])]
    exact augRd_getD_replicate _ _

/-- **The body's precondition is inhabited in full.**  From any state
holding the round's orientation region and the carrier cell — the state
the base pass leaves — reallocating the twenty-one working regions
gives one satisfying `augRdBody_spec`'s precondition entire.  The
orientation region survives because it is none of the twenty-one, and
every scalar is the original's, so the two figure cells still read the
same `n`. -/
theorem exists_augRdBodyPre {B : ℕ} {nN o t fo ft dgF mkF ao aj dgP mt sg tp sk
    ro rt mkT o' t' qo qt ad sd dgE : String}
    (hmk : mkF ∉ augRdAllocs fo ft dgF ao aj dgP mt sg tp sk ro rt mkT o' t'
      qo qt ad sd dgE)
    (hoa : o ≠ mkF) (hob : o ∉ augRdAllocs fo ft dgF ao aj dgP mt sg tp sk
      ro rt mkT o' t' qo qt ad sd dgE)
    (hta : t ≠ mkF) (htb : t ∉ augRdAllocs fo ft dgF ao aj dgP mt sg tp sk
      ro rt mkT o' t' qo qt ad sd dgE)
    {n : ℕ} {D : Orientation n} {off tgt : ℕ → ℕ} {σ : Env}
    (hcsr : TrInCsr o t D (arcCount D) off tgt σ) (hnv : σ.vars nN = n)
    (hB1 : n + n * n + 1 < B)
    (hB2 : n + n * n + arcCount D + fratPairCount D + transPairCount D < B) :
    ∃ σ' : Env, TrInCsr o t D (arcCount D) off tgt σ' ∧ σ'.vars nN = n ∧
      n + n * n + 1 < B ∧
      n + n * n + arcCount D + fratPairCount D + transPairCount D < B ∧
      n + 1 ≤ (σ'.arrs fo).length ∧
      fratPairCount D ≤ (σ'.arrs ft).length ∧
      n ≤ (σ'.arrs dgF).length ∧ (σ'.arrs mkF).length = n * n ∧
      (∀ i, (σ'.arrs mkF).getD i 0 = 0) ∧
      n + 1 ≤ (σ'.arrs ao).length ∧
      fratPairCount D ≤ (σ'.arrs aj).length ∧
      n ≤ (σ'.arrs dgP).length ∧ fratPairCount D ≤ (σ'.arrs mt).length ∧
      n ≤ (σ'.arrs sg).length ∧ n ≤ (σ'.arrs tp).length ∧
      n * n + n ≤ (σ'.arrs sk).length ∧
      n + 1 ≤ (σ'.arrs ro).length ∧
      transPairCount D ≤ (σ'.arrs rt).length ∧
      n * n ≤ (σ'.arrs mkT).length ∧
      (∀ i, i < n * n → (σ'.arrs mkT).getD i 0 = 0) ∧
      n + 1 ≤ (σ'.arrs o').length ∧
      arcCount D + fratPairCount D + transPairCount D ≤ (σ'.arrs t').length ∧
      n + 1 ≤ (σ'.arrs qo).length ∧ arcCount D ≤ (σ'.arrs qt).length ∧
      n ≤ (σ'.arrs ad).length ∧ n ≤ (σ'.arrs sd).length ∧
      n ≤ (σ'.arrs dgE).length ∧
      (∀ i, i < n → (σ'.arrs ad).getD i 0 = 0) ∧
      (∀ i, i < n → (σ'.arrs sd).getD i 0 = 0) ∧
      (∀ i, i < n → (σ'.arrs dgE).getD i 0 = 0) := by
  obtain ⟨σ', hvars, hframe, hrest⟩ :=
    exists_augRdAllocs hmk n (arcCount D) (fratPairCount D) (transPairCount D) σ
  exact ⟨σ', augRd_trInCsr_of_eq hcsr (hframe o hoa hob) (hframe t hta htb),
    by rw [hvars]; exact hnv, hB1, hB2, hrest⟩

/-- **The body's hypothesis bundle is satisfiable**, so nothing above is
vacuous: twenty-three distinct region names and four figure cells
outside all five scratch pools (`frScalars`, `fpScalars`, `trScalars`,
`emScalars`, `tpScalars`). -/
theorem augRdBody_names_std :
    AugRdFhNames "rd.io" "rd.it" "rd.fo" "rd.ft" "rd.dgF" "rd.mkF" "rd.ao"
        "rd.aj" "rd.dgP" "rd.mt" "rd.sg" "rd.tp" "rd.sk" ∧
      TrNames "rd.io" "rd.it" "rd.ro" "rd.rt" "rd.mkT" ∧
      EmNames "rd.io" "rd.it" "rd.ro" "rd.rt" "rd.mkT" "rd.fo" "rd.ft" "rd.sg"
        "rd.oo" "rd.ot" "rd.qo" "rd.qt" "rd.ad" "rd.sd" "rd.dgE" ∧
      AugRdSep "rd.fo" "rd.ft" "rd.dgF" "rd.mkF" "rd.ao" "rd.aj" "rd.dgP"
        "rd.mt" "rd.sg" "rd.tp" "rd.sk" "rd.ro" "rd.rt" "rd.mkT" "rd.oo"
        "rd.ot" "rd.qo" "rd.qt" "rd.ad" "rd.sd" "rd.dgE" ∧
      ("rd.it" : String) ≠ "rd.io" ∧
      ("rd.nN" : String) ∉ frScalars ∧ ("rd.nF" : String) ∉ frScalars ∧
      ("rd.nF" : String) ≠ "rd.nN" ∧ FpCells "rd.nN" "rd.nF" ∧
      ("rd.nN" : String) ∉ trScalars ∧ ("rd.nF" : String) ∉ trScalars ∧
      ("rd.nN" : String) ≠ "rd.nT" ∧ ("rd.nF" : String) ≠ "rd.nT" ∧
      ("rd.nN" : String) ∉ emScalars ∧ ("rd.nN" : String) ∉ tpScalars ∧
      ("rd.nN" : String) ≠ "rd.nO" ∧
      ("rd.mkF" : String) ∉ augRdAllocs "rd.fo" "rd.ft" "rd.dgF" "rd.ao"
        "rd.aj" "rd.dgP" "rd.mt" "rd.sg" "rd.tp" "rd.sk" "rd.ro" "rd.rt"
        "rd.mkT" "rd.oo" "rd.ot" "rd.qo" "rd.qt" "rd.ad" "rd.sd" "rd.dgE" :=
  ⟨{ fr := ⟨by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, by decide, by decide,
        by decide, by decide⟩
     fp := ⟨by decide⟩
     o_wr := by decide
     t_wr := by decide
     mk_wr := by decide
     dgF_wr := by decide },
   ⟨by decide, by decide, by decide, by decide, by decide, by decide,
     by decide, by decide, by decide⟩,
   { wrRd := by decide, wrNd := by decide, fo_ft := by decide },
   ⟨by decide⟩,
   by decide, by decide, by decide, by decide, ⟨by decide, by decide⟩,
   by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide⟩

/-- **The body's budget is `augRoundBudget`'s shape at `961, 443, 576,
270, 217`** — an *equality*, so nothing is estimated in the conversion.
Term by term: `961·n` (`240` fraternal CSR, `394` peel, `27`
transitive, `300` emit), `443·a` (`120 + 23 + 300`), `576·f`
(`200 + 176 + 200`, the peel's read at `nf ≤ f`), `270·T` (`30 + 240`),
`217` of setup.  Every figure is `n`, `arcCount D`, `fratPairCount D`
or `transPairCount D` and nothing else — `levelCharge`'s own
currency. -/
theorem augRdBodyK_eq {n : ℕ} (D : Orientation n) :
    augRdBodyK n (arcCount D) (fratPairCount D) (transPairCount D)
      = augRoundBudget 961 443 576 270 217 D := by
  simp only [augRdBodyK, augRdFratHalfK, augRoundBudget, fratKStd, fratK,
    fratPeelK, trK, emK]
  ring

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

/-- The three stages `augRdBody` **does** run leave §5's five
coefficients `73, 20, 20, 40, 48` of room, which is exactly what the
three carrier sweeps, the transitive re-zero and the copy-back are
priced at. -/
theorem augRdBodyK_le_augRdRoundK {n a f T : ℕ} :
    augRdBodyK n a f T ≤ augRdRoundK n a f T := by
  simp only [augRdBodyK, augRdRoundK, augRdFratHalfK]
  omega

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
      = augRoundBudget 1025 455 588 305 287 D := by
  simp only [augRdRoundK, augRoundBudget, fratKStd, fratK, fratPeelK, trK, emK,
    trClearK, inCsrCopyK]
  ring

/-- The same, as the `≤` a `Spec.mono` consumes, at any budget whose
constants dominate. -/
theorem augRdRoundK_le_augRoundBudget {n : ℕ} (D : Orientation n)
    {kn ka kf kt kc : ℕ} (hkn : 1025 ≤ kn) (hka : 455 ≤ ka) (hkf : 588 ≤ kf)
    (hkt : 305 ≤ kt) (hkc : 287 ≤ kc) :
    augRdRoundK n (arcCount D) (fratPairCount D) (transPairCount D)
      ≤ augRoundBudget kn ka kf kt kc D := by
  have h1 : 1025 * n ≤ kn * n := Nat.mul_le_mul_right n hkn
  have h2 : 455 * arcCount D ≤ ka * arcCount D := Nat.mul_le_mul_right _ hka
  have h3 : 588 * fratPairCount D ≤ kf * fratPairCount D :=
    Nat.mul_le_mul_right _ hkf
  have h4 : 305 * transPairCount D ≤ kt * transPairCount D :=
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
      ≤ 345 * levelCharge D + 287 := by
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
      ≤ n * (1025 + 455 * d + 893 * (d * d)) + 287 := by
  have h1 := arcCount_le hd
  have h2 := fratPairCount_le hd
  have h3 := transPairCount_le hd
  rw [augRdRoundK_eq]
  simp only [augRoundBudget]
  calc 1025 * n + 455 * arcCount D + 588 * fratPairCount D
        + 305 * transPairCount D + 287
      ≤ 1025 * n + 455 * (n * d) + 588 * (n * (d * d)) + 305 * (n * (d * d))
        + 287 := by omega
    _ = n * (1025 + 455 * d + 893 * (d * d)) + 287 := by ring

/-- **The four coefficients pass `augChainCost_le_selChainCharge`'s
gates.**  `kn ≤ 3k`, `ka ≤ 2k`, `kf ≤ 4k`, `kt ≤ 2k` hold at every
`k ≥ 345`, so in particular at the `k = 475` the base and
symmetrization passes already close at. -/
theorem augRdRoundK_gates {k : ℕ} (hk : 342 ≤ k) :
    1025 ≤ 3 * k ∧ 455 ≤ 2 * k ∧ 588 ≤ 4 * k ∧ 305 ≤ 2 * k := by
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
        (augChainCost bn ba bc 1025 455 588 305 287 sn sa sc (sel m) G R : ℝ)
          ≤ f * (m : ℝ) ^ (1 + δ) + (bc + sc + 1 + R * 287 : ℕ) :=
  exists_augChainCost_le sel C hC R δ hδ bn ba bc 1025 455 588 305 287 sn sa sc
    475 hbn hba (by omega) (by omega) (by omega) (by omega) hsn hsa

/-! ## §6 Axiom audit -/

#print axioms augRd_inNCsr_tgt_length
#print axioms augRd_trInCsr_of_eq
#print axioms augRdStTr_of_augStInNW
#print axioms augRd_fratComW_spec
#print axioms augRdFratHalf_spec
#print axioms augRdBody_spec
#print axioms augRdBodyK_eq
#print axioms augRdBodyK_le_augRdRoundK
#print axioms exists_augRdAllocs
#print axioms exists_augRdBodyPre
#print axioms augRdBody_names_std
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
