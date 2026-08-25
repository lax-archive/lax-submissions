import Lax3Proofs.SolveSweepClose
import Lax3Proofs.SolveAugRoundIn
import Lax3Proofs.SolveAugSeamFix

set_option autoImplicit false

/-!
# F6c10b (join) — `CoverAllIn` from the ordering residual, and the three
seams of the augmentation that do **not** close

`SolveSweepClose` §10 lists what separates the landed material from
`CoverAllIn`.  This file does two things and is honest about which is
which.

## §1–§3 What closes

`CoverAllIn` is discharged **verbatim** at a concrete program, a
concrete name family and an explicit budget, from **one** residual:

    CovAugAdjSelIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf
      Adm sweepCloseCa sweepCloseCo covAllAoO covAllAjO covAllDgO
      covAllMtO Sag covAllSmp covAllSsw agC Kag

together with `1 ≤ q`.  Nothing else survives: every name hypothesis of
`covOrderIn_bucketPeel` and of `sweepClose_covSweepIn` is discharged at
the fourteen `"sc.*"` bases of `SolveSweepClose` §9 and six fresh
`"oc.*"` bases, and the sweep's descriptor is transported across the
bucket peel by the length-stability that IMP+ gives for free
(`covAllJoin_hSsw`).  This is the whole peel/sweep side of the cover
stage plus the ordering pass's peel half: the *only* thing left on the
route from `CovSweepIn` to `CoverAllIn` is the augmentation.

§3 sums the budget.  The ordering pass's two halves fold into **one**
`augChainCost` — the bucket peel's `313·A.N + 118·slotCount(…) + 40` is
`augSymBudget`'s own shape once `slotCount (D.toGraph) = 2·arcCount D`
is used — so

    Kcov j A = augChainCost 545 554 113 1025 455 588 305 287 484 432 124
                 (bucketSel A.N) A.G R
             + peelK (12·S.R + 362) 154 192 S A ((ord A.N A.G).order)

with the first summand `≤ 545·selChainCharge (bucketSel A.N) A.G R +
(238 + 287·R)` (`coverAllJoin_Kord_le`), hence `≤ f·m^{1+δ} + O(R)` on a
nowhere dense class (`coverAllJoin_exists_Kord_le`), and the second
`≤ (12·S.R + 708)·chargeTotal (coverCFSel …)` at the ledger's own `cf`
(`coverAllJoin_Ksw_le`).  Every figure is `A.N`, `arcCount`,
`fratPairCount`, `transPairCount`, a cluster mass or the peel's edge
work.  **No term is quadratic in the carrier.**

## §4a What is *checked* to close inside the augmentation

`augRoundIn_ardRoundCom_std` states the round at `Smp = Ssw = True`,
which the composition cannot use.  `covAllJoin_augRoundIn` restates it
at the cover stage's own two descriptors — `covAllSmp` and `covAllSsw`,
the very ones §1 needs — with `ArdWord` the only surviving hypothesis.
So the round's `Smp`/`Ssw` seams are **not** where the composition
fails, and the three below are the whole of the failure.

## §4b–§4d What does not close: three seams inside the augmentation

The remaining residual `CovAugAdjSelIn` is supposed to be reached by
`covAugAdjSelIn_of_base_rounds_sym` (`SolveAugCompose.lean:493`) from
`AugBaseIn`, `AugRoundIn`, `AugSymIn`, all three of which have landed
discharges.  **They cannot be composed.**  Three of the shared
parameters are over-determined, and each failure is proved below rather
than asserted.

1. **`coverAllBase_hSbd_unsatisfiable`.**
   `augBaseIn_of_adj_peel_orient` takes one `Sbd` for its three passes.
   `augBasePeelIn_bucketPeelBuild` (`SolveAugBaseFrame.lean:174`)
   *pins* it to

       fun j σ => n ≤ (σ.arrs (bra j)).length ∧ n ≤ (σ.arrs (tpO j)).length
                ∧ n * n + n ≤ (σ.arrs (skO j)).length

   — three length clauses, all against the **root** carrier `n`, none
   of them against `σ.vars (arenaNames j).nN`.  `augBaseOrientIn_orCom`
   (`SolveAugOrient.lean:1961`) asks of the same `Sbd`

       hSbd : ∀ j σ, Sbd j σ →
         σ.vars (arenaNames j).nN + 1 ≤ (σ.arrs (io j)).length ∧ …

   and `Sbd` does not bound `σ.vars (arenaNames j).nN` at all, so the
   implication fails at a state whose carrier cell is larger than every
   array — **for every choice of the six names**, not merely for
   generic ones.  The theorem below is that statement.

2. **`coverAllBase_hSrd_not_ardSrd`.**
   `augBaseOrientIn_orCom` hands its `hSrd` duty only

       (∀ b, b ≠ io j → b ≠ it j → b ≠ cn j → σ'.arrs b = σ.arrs b)

   and no length clause, while its own proof has
   `hlen : ∀ b, (σ'.arrs b).length = (σ.arrs b).length` in scope (from
   `specArrsLength`) and uses it two lines later for `ca j` and `co j`.
   The rounds' descriptor `ardSrd` (`SolveAugRoundIn.lean:1146`)
   constrains the *orientation pair itself* — `io j` and `it j` head
   `ardRegions` — at `ardCap (σ.vars (arenaNames j).nN)`.  Those are
   exactly the two names the frame says nothing about, so no `Sbd`
   whatever (satisfiable at even one state) discharges `hSrd` at
   `Srd := ardSrd …`.  This is the `it j` over-allocation, and it is
   **not** a free choice of `Sbd`: it is a missing conjunct in a landed
   interface.  `augBasePeelIn_bucketPeelBuild`'s own `hSmp`/`hSsw` do
   carry `(∀ b, (σ'.arrs b).length = (σ.arrs b).length)`, so the
   convention exists and `augBaseOrientIn_orCom` simply omits it; adding
   it there is a one-line repair to a landed file.

3. **`coverAllSym_srd_forces_constant`.**
   `augSymCsrIn_symComW` (`SolveAugSymMerge.lean:1619`) asks

       hSrd : ∀ j σ, Srd j σ → symCsrSizes nA soO stO j σ ∧ …

   whose second clause is
   `(σ.arrs (stO j)).length = 2 * σ.vars (nA j)`.  In
   `covAugAdjSelIn_of_base_rounds_sym` that same `Srd` is the **round
   invariant**, and the round advances `nA j` from `arcCount D` to
   `arcCount (greedyStep … D)` (`ardCopyCom` assigns `nA := nO`,
   `ardCopy_spec`), while `store` is `List.set` and no run changes an
   array's length.  So `AugRoundIn` at `augStInNW` together with that
   `hSrd` *proves* that every round of every admissible arena adds no
   arc.  The augmentation exists to add arcs; this is a no-go of
   exactly the shape of `augRd_augStInN_forces_constant`
   (`SolveAugRoundSeams.lean:265`), one level up.

   The trap underneath it is `AugSymCsrIn`'s own postcondition
   (`SolveAugCompose.lean:685`): a bare `GraphCsr`, whose two clauses
   are array *equalities*, so the exact allocation
   `2·arcCount (selChain sel A.G R)` has to hold **before the pass
   runs** (`graphCsr_pre_lengths`) and therefore before the rounds run.
   The repair is the one `augStInNW` already made for the region: state
   `AugSymCsrIn`'s output as a *windowed* CSR, or give the merge an
   allocation sized by the carrier alone (`ardCap`), so that the figure
   the caller must supply stops moving from round to round.

## §5 What closes after the repairs

None of the three seams is repaired *in this file* — all three live in
landed files, and all three have now been repaired there
(`augBasePeelInS_bucketPeelBuild`, `augBaseOrientIn_orCom`'s length
clause, `symComW_spec`).  §4b–§4d are left exactly as they were pinned:
they remain true statements about the *landed* forms, and they are the
specification the repairs were written against.  §5 composes the
repaired forms — through `SolveAugSeamFix`'s `augSeamCovAugAdjSelIn` —
and closes `CoverAllIn` outright, on `1 ≤ q` and `ArdWord` alone
(`covAllJoin_coverAllIn_closed`).
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ColoringNumbers
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.Augmentation (Orientation fratGraph)
open Lax3Proofs.CoverRoutine (MinDegSel selRank selChain greedyStep
  selOrderingRoutine)

/-! ## §1 The ordering side's six fresh names, and the two descriptors -/

/-- The augmented region's offsets. -/
abbrev covAllAoO : ℕ → String := lv "oc.p"
/-- The augmented region's targets. -/
abbrev covAllAjO : ℕ → String := lv "oc.j"
/-- The augmented region's live degrees. -/
abbrev covAllDgO : ℕ → String := lv "oc.d"
/-- The augmented region's mate pointers. -/
abbrev covAllMtO : ℕ → String := lv "oc.m"
/-- The bucket peel's tops. -/
abbrev covAllTpO : ℕ → String := lv "oc.t"
/-- The bucket peel's cells. -/
abbrev covAllSkO : ℕ → String := lv "oc.k"

/-- **The sweep's scratch descriptor**, at `SolveSweepClose` §9's own
fourteen names — the `Ssw` both the ordering pass and the sweep must
speak. -/
def covAllSsw (n : ℕ) : ℕ → Env → Prop := fun j σ =>
  sweepCloseBldSc sweepCloseAo sweepCloseAj sweepCloseDg sweepCloseMt
      sweepCloseOd j σ ∧
    sweepClosePeelSc sweepCloseCo sweepCloseCm sweepCloseCnt sweepCloseCur
      sweepCloseLo sweepCloseLm sweepCloseSb n j σ

/-- **The ordering peel's scratch descriptor** — `covOrderIn_bucketPeel`'s
`Smp`, at the rank array the sweep reads and the peel's own two
regions. -/
def covAllSmp (n : ℕ) : ℕ → Env → Prop := fun j σ =>
  n ≤ (σ.arrs (sweepCloseRa j)).length ∧
    n ≤ (σ.arrs (covAllTpO j)).length ∧
    n * n + n ≤ (σ.arrs (covAllSkO j)).length

/-- Two distinct four-character bases stay distinct at every level —
`SolveSweepClose` §9's `sweepCloseNe4`, restated so this file's own
bases can use it. -/
theorem covAllNe4 {s t : String} (hs : s.length = 4) (ht : t.length = 4)
    (hst : s ≠ t) (j : ℕ) : lv s j ≠ lv t j :=
  lv_ne_of_base_ne (by rw [hs, ht]) hst j j

/-! ## §2 The join: `CoverAllIn` from `CovAugAdjSelIn` -/

/-- **The sweep's descriptor rides through the bucket peel.**  Every
clause of `covAllSsw` is either a length — and IMP+ has no allocation,
so `hlen` carries it — or `BfsClean` at `sweepCloseCo`, which is none of
the five arrays the peel writes.  The two figure cells `nN`/`nS` are
level-tagged four-character names and so are none of the twelve `"bk.*"`
scalars. -/
theorem covAllJoin_hSsw (n : ℕ) (j : ℕ) (σ σ' : Env)
    (harr : ∀ b : String, b ≠ sweepCloseRa j → b ≠ covAllMtO j →
      b ≠ covAllDgO j → b ≠ covAllTpO j → b ≠ covAllSkO j →
      σ'.arrs b = σ.arrs b)
    (hlen : ∀ b : String, (σ'.arrs b).length = (σ.arrs b).length)
    (hvars : ∀ y : String, y ≠ "bk.n" → y ≠ "bk.i" → y ≠ "bk.u" → y ≠ "bk.m" →
      y ≠ "bk.t" → y ≠ "bk.z" → y ≠ "bk.c" → y ≠ "bk.r" → y ≠ "bk.f" →
      y ≠ "bk.v" → y ≠ "bk.w" → y ≠ "bk.d" → σ'.vars y = σ.vars y)
    (h : covAllSsw n j σ) : covAllSsw n j σ' := by
  obtain ⟨⟨hb1, hb2, hb3, hb4, hb5⟩, ⟨hp1, hp2, hp3⟩, hgr⟩ := h
  have hnN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN := by
    refine hvars _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      exact lv_ne_len4 (by decide) (by decide) (by decide) j
  have hnS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS := by
    refine hvars _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      exact lv_ne_len4 (by decide) (by decide) (by decide) j
  have hco : σ'.arrs (sweepCloseCo j) = σ.arrs (sweepCloseCo j) := by
    refine harr _ ?_ ?_ ?_ ?_ ?_ <;>
      exact covAllNe4 (by decide) (by decide) (by decide) j
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, bfsClean_of_eq hp3 hco⟩,
    sweepCloseGrpSc_of_len hlen hgr⟩
  · rw [hnN, hlen]; exact hb1
  · rw [hnS, hlen]; exact hb2
  · rw [hnN, hlen]; exact hb3
  · rw [hnS, hlen]; exact hb4
  · rw [hnN, hlen]; exact hb5
  · rw [hlen]; exact hp1
  · rw [hlen]; exact hp2

open Classical in
/-- **`CovOrderIn` at the concrete family**, from the augmentation
residual and nothing else: every name hypothesis of
`covOrderIn_bucketPeel` is discharged, and `Ssw` is the sweep's own
descriptor. -/
theorem covAllJoin_covOrderIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Sag : ℕ → Env → Prop) (agC : ℕ → Com)
    (Kag : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hq : 1 ≤ q)
    (hag : CovAugAdjSelIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf
      Adm sweepCloseCa sweepCloseCo covAllAoO covAllAjO covAllDgO covAllMtO
      Sag (covAllSmp n) (covAllSsw n) agC Kag) :
    CovOrderIn C hC φ (selOrderingRoutine (fun m => bucketSel m) R) G c w q ℓp
      htabF hbf Adm sweepCloseCa sweepCloseCo sweepCloseRa
      (fun j σ => Sag j σ ∧ covAllSmp n j σ) (covAllSsw n)
      (fun j => .seq (agC j)
        (bucketPeelCom (covAllAoO j) (covAllAjO j) (covAllDgO j) (covAllMtO j)
          (sweepCloseRa j) (covAllTpO j) (covAllSkO j) (arenaNames j).nN))
      (fun j A => Kag j A + linearPeelBudget R 313 118 40 A) := by
  refine covOrderIn_bucketPeel C hC φ R G c w q ℓp htabF hbf Adm
    sweepCloseCa sweepCloseCo sweepCloseRa covAllAoO covAllAjO covAllDgO
    covAllMtO covAllTpO covAllSkO Sag (covAllSsw n) agC Kag hq ?_ ?_ ?_ ?_ hag
  · exact fun j => ⟨covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j⟩
  · exact fun j => ⟨covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j,
      covAllNe4 (by decide) (by decide) (by decide) j⟩
  · rintro j b (rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨covAllNe4 (by decide) (by decide) (by decide) j,
        covAllNe4 (by decide) (by decide) (by decide) j,
        covAllNe4 (by decide) (by decide) (by decide) j,
        covAllNe4 (by decide) (by decide) (by decide) j,
        covAllNe4 (by decide) (by decide) (by decide) j⟩
  · exact fun j σ σ' harr hlen hvars h =>
      covAllJoin_hSsw n j σ σ' harr hlen hvars h

open Classical in
/-- **`CoverAllIn`, discharged from one residual.**  The cover stage is
`agC j ; bucketPeelCom … ; bldCom … ; sweepCom … ; grCom …` — the
augmentation, the bucket peel that turns it into the rank array, the
deletable-adjacency build, the peeled BFS sweep and the grouping — at
the summed budget, and the only hypotheses are `1 ≤ q` and the
augmentation residual `CovAugAdjSelIn`. -/
theorem covAllJoin_coverAllIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Sag : ℕ → Env → Prop) (agC : ℕ → Com)
    (Kag : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hq : 1 ≤ q)
    (hag : CovAugAdjSelIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf
      Adm sweepCloseCa sweepCloseCo covAllAoO covAllAjO covAllDgO covAllMtO
      Sag (covAllSmp n) (covAllSsw n) agC Kag) :
    CoverAllIn C hC φ (selOrderingRoutine (fun m => bucketSel m) R) G c w q ℓp
      htabF hbf Adm sweepCloseCa sweepCloseCo sweepCloseCm
      (fun j σ => (Sag j σ ∧ covAllSmp n j σ) ∧ covAllSsw n j σ)
      (fun j => .seq
        (.seq (agC j)
          (bucketPeelCom (covAllAoO j) (covAllAjO j) (covAllDgO j)
            (covAllMtO j) (sweepCloseRa j) (covAllTpO j) (covAllSkO j)
            (arenaNames j).nN))
        (.seq
          (bldCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
            (arenaNames j).tgt (sweepCloseRa j) (sweepCloseAo j)
            (sweepCloseAj j) (sweepCloseDg j) (sweepCloseMt j) (sweepCloseOd j))
          (.seq
            (sweepCom
              (bfsTurnCom (Headline.headlineSetup C hC φ).R (sweepCloseCa j)
                (sweepCloseCo j) (sweepCloseAo j) (sweepCloseAj j)
                (sweepCloseDg j) (sweepCloseLo j) (sweepCloseLm j)
                (arenaNames j).nN)
              (sweepCloseCa j) (sweepCloseLo j) (sweepCloseAo j)
              (sweepCloseAj j) (sweepCloseDg j) (sweepCloseMt j)
              (sweepCloseOd j) (arenaNames j).nN)
            (grCom (arenaNames j).nN (sweepCloseLo j) (sweepCloseLm j)
              (sweepCloseOd j) (sweepCloseCo j) (sweepCloseCm j)
              (sweepCloseCnt j) (sweepCloseCur j) (sweepCloseSb j)))))
      (fun j A => (Kag j A + linearPeelBudget R 313 118 40 A)
        + peelK (12 * (Headline.headlineSetup C hC φ).R + 362) 154 192
            (Headline.headlineSetup C hC φ) A
            ((selOrderingRoutine (fun m => bucketSel m) R A.N A.G).order)) :=
  coverAllIn_of_order_sweep C hC φ (selOrderingRoutine (fun m => bucketSel m) R)
    G c w q ℓp htabF hbf Adm sweepCloseCa sweepCloseCo sweepCloseCm
    sweepCloseRa _ _ _ _ _ _
    (covAllJoin_covOrderIn C hC φ R G c w q ℓp htabF hbf Adm Sag agC Kag hq hag)
    (sweepClose_covSweepIn_names C hC φ
      (selOrderingRoutine (fun m => bucketSel m) R) G c w q ℓp htabF hbf Adm hq)

/-- **Nothing in §2 is a statement about an empty precondition.**  The
two descriptors §1 introduces are concrete formulas, not parameters
constrained through implications, so they owe a witness: here is one
state satisfying both at once, at every `n` and every level.  (The
sweep's half is `sweepClose_sc_inhabited`'s witness; the ordering peel's
three allocations are the same three lengths.) -/
theorem covAllJoin_sc_inhabited (n j : ℕ) :
    ∃ σ : Env, covAllSsw n j σ ∧ covAllSmp n j σ := by
  classical
  refine ⟨⟨fun _ => 0, fun _ => List.replicate (n * n + n + 1) 0, [], []⟩,
    ⟨?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [List.length_replicate] <;> omega
  · refine ⟨⟨?_, ?_, ?_⟩, le_rfl, le_rfl, le_rfl, le_rfl⟩
    · simp only [List.length_replicate]; omega
    · simp only [List.length_replicate]; omega
    · intro v _; simp
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [List.length_replicate] <;> omega

/-! ## §3 The budget of the whole cover stage

Nothing new is measured.  The bucket peel's own budget is
`augSymBudget`'s shape at the same carrier, so the ordering pass folds
into a single `augChainCost`, and the sweep's is the landed `peelK`
column. -/

/-- The base pass's three coefficients, summed:
`augBaseAdjIn_bldAdjCom` `(81, 116, 24)`,
`augBasePeelIn_bucketPeelBuild` `(394, 352, 64)`,
`augBaseOrientIn_orCom` `(70, 86, 25)`. -/
theorem covAllJoin_base_coeffs :
    (81 + 394 + 70, 116 + 352 + 86, 24 + 64 + 25) = ((545 : ℕ), (554 : ℕ), (113 : ℕ)) := by
  norm_num

/-- The symmetrization's three, through `augSymIn_of_symCsr_build`'s
`(tn + 81, ta + 116, tc + 24)` at `augSymCsrIn_symComW`'s `(90, 80, 60)`. -/
theorem covAllJoin_sym_coeffs :
    (90 + 81, 80 + 116, 60 + 24) = ((171 : ℕ), (196 : ℕ), (84 : ℕ)) := by
  norm_num

/-- **The ordering pass is one `augChainCost`.**  The bucket peel's
`313·A.N + 118·slotCount ((selChain … R).toGraph) + 40` is
`augSymBudget 313 236 40` at the final orientation, because a
symmetrised orientation has exactly two slots per arc; adding it to the
symmetrization's own `(171, 196, 84)` gives `(484, 432, 124)`. -/
theorem covAllJoin_Kord_eq {Λ n₀ : ℕ} (A : Arena Λ n₀) (R : ℕ) :
    augChainCost 545 554 113 1025 455 588 305 287 171 196 84
        (bucketSel A.N) A.G R
      + linearPeelBudget R 313 118 40 A
    = augChainCost 545 554 113 1025 455 588 305 287 484 432 124
        (bucketSel A.N) A.G R := by
  have hslot : slotCount ((selChain (bucketSel A.N) A.G R).toGraph)
      = 2 * arcCount (selChain (bucketSel A.N) A.G R) :=
    slotCount_toGraph_eq_two_mul_arcCount _
  simp only [augChainCost, augSymBudget, linearPeelBudget, hslot]
  ring

/-- **The ordering pass's budget, in the campaign's currency.**  Every
coefficient meets `augChainCost_le_selChainCharge`'s gate at `k = 545`
— `bn ≤ k`, `ba ≤ 3k`, `kn ≤ 3k`, `ka ≤ 2k`, `kf ≤ 4k`, `kt ≤ 2k`,
`sn ≤ 3k`, `sa ≤ 5k` — so the whole augmentation *and* the bucket peel
cost at most `545` times the landed `selChainCharge` plus `238 + 287·R`.
Nothing is left in a foreign currency: the only figures are `A.N`,
`arcCount`, `fratPairCount` and `transPairCount` at the chain's own
orientations. -/
theorem covAllJoin_Kord_le {m : ℕ} (G : SimpleGraph (Fin m)) (R : ℕ) :
    augChainCost 545 554 113 1025 455 588 305 287 484 432 124
        (bucketSel m) G R
      ≤ 545 * selChainCharge (bucketSel m) G R + (238 + 287 * R) := by
  have h := augChainCost_le_selChainCharge 545 554 113 1025 455 588 305 287
    484 432 124 545 (bucketSel m) G R (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he : (113 : ℕ) + 124 + 1 + R * 287 = 238 + 287 * R := by ring
  rw [he] at h
  exact h

/-- **… and it closes inside §7's envelope, one δ to spare.**
`exists_augChainCost_le` at `k = 545`: on a nowhere dense class the
ordering pass costs at most `f·m^{1+δ} + (238 + 287·R)` on every
subgraph copy of every member, with `f` fixed before the graph.  The
interface asks for `m^{1+2δ}`. -/
theorem covAllJoin_exists_Kord_le (C : GraphClass) (hC : NowhereDense C)
    (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (augChainCost 545 554 113 1025 455 588 305 287 484 432 124
            (bucketSel m) G R : ℝ)
          ≤ f * (m : ℝ) ^ (1 + δ) + (113 + 124 + 1 + R * 287 : ℕ) :=
  exists_augChainCost_le (fun m => bucketSel m) C hC R δ hδ
    545 554 113 1025 455 588 305 287 484 432 124 545
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **The sweep's budget, in the cover ledger's column.**  `peelK` at
`(12·S.R + 362, 154, 192)` against `peelK_le_coverCFSel_total`, whose
degree hypothesis is the ledger's own `cf` and whose routine is
`selOrderingRoutine sel (3·S.R)` — the depth the ordering pass has to be
instantiated at for the two to be the same routine. -/
theorem covAllJoin_Ksw_le {L n₀ : ℕ} (sel : ∀ m : ℕ, MinDegSel m) (S : Setup L)
    {cf δ : ℝ} (hcf : 1 ≤ cf) (hδ : 0 ≤ δ) (j : ℕ) (A : Arena (S.pal j) n₀)
    (hdeg : ∀ v : Fin A.N,
      (wreach A.G ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order (2 * S.R) v).ncard
        ≤ ⌈cf * (A.N : ℝ) ^ δ⌉₊) :
    peelK (12 * S.R + 362) 154 192 S A
        ((selOrderingRoutine sel (3 * S.R)) A.N A.G).order
      ≤ (12 * S.R + 708) * chargeTotal (coverCFSel sel S cf δ j A) := by
  have h := peelK_le_coverCFSel_total sel S hcf hδ (12 * S.R + 362) 154 192 j A hdeg
  have he : 12 * S.R + 362 + 154 + 192 = 12 * S.R + 708 := by ring
  rw [he] at h
  exact h

/-! ## §4 What is checked to close, and the three seams that do not

§4a first removes two candidate seams from suspicion: the rounds *do*
speak the cover stage's own two descriptors.  §4b–§4d are the three that
do not close, each a theorem about the landed statements rather than a
remark. -/

/-- Any level-tagged name whose base does not start with `'r'` is
outside the round's twenty-three written arrays — the `ard*` family is
twenty-seven fixed four-character strings on the base letter `'r'`
(`SolveAugRoundIn` §6). -/
private theorem covAllJoin_ardArr {j : ℕ} {σ σ' : Env} {s : String} {ch : Char}
    (hs : s.toList.head? = some ch) (hch : ch ≠ 'r')
    (harr : ∀ b : String, b ≠ ardMkF j →
      b ∉ augRdAllocs (ardFo j) (ardFt j) (ardDgF j) (ardAo j) (ardAj j)
        (ardDgP j) (ardMt j) (ardSg j) (ardTp j) (ardSk j) (ardRo j) (ardRt j)
        (ardMkT j) (ardOo j) (ardOt j) (ardQo j) (ardQt j) (ardAd j) (ardSd j)
        (ardDgE j) →
      b ≠ ardIo j → b ≠ ardIt j → σ'.arrs b = σ.arrs b) :
    σ'.arrs (lv s j) = σ.arrs (lv s j) := by
  have hr : ∀ b : String, b.toList.head? = some 'r' → lv s j ≠ b := by
    intro b hb
    refine ard_lv_ne_head hs ?_ j
    rw [hb]
    exact fun hcon => hch (Option.some.inj hcon).symm
  refine harr _ (hr "rf.m" (by decide)) ?_ (hr "ri.o" (by decide))
    (hr "ri.t" (by decide))
  simp only [augRdAllocs, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨hr "rf.o" (by decide), hr "rf.t" (by decide), hr "rf.d" (by decide),
    hr "rp.o" (by decide), hr "rp.j" (by decide), hr "rp.d" (by decide),
    hr "rp.m" (by decide), hr "rp.s" (by decide), hr "rp.p" (by decide),
    hr "rp.k" (by decide), hr "rt.o" (by decide), hr "rt.t" (by decide),
    hr "rt.m" (by decide), hr "ro.o" (by decide), hr "ro.t" (by decide),
    hr "rq.o" (by decide), hr "rq.t" (by decide), hr "rz.a" (by decide),
    hr "rz.s" (by decide), hr "rz.d" (by decide)⟩

/-- … and the same for the arena's two figure cells against the round's
scalars. -/
private theorem covAllJoin_ardVar {j : ℕ} {σ σ' : Env} {s : String}
    (hs : s.toList.head? = some 's') (hnot : lv s j ∉ ardScalars)
    (hvar : ∀ y : String, y ∉ ardScalars → y ≠ ardNF j → y ≠ ardNT j →
      y ≠ ardNO j → y ≠ ardNA j → σ'.vars y = σ.vars y) :
    σ'.vars (lv s j) = σ.vars (lv s j) := by
  have h4 : ∀ b : String, b.toList.head? ≠ some 's' → lv s j ≠ b :=
    fun b hb => ard_lv_ne_head hs hb j
  exact hvar _ hnot (h4 "rc.f" (by decide)) (h4 "rc.t" (by decide))
    (h4 "rc.o" (by decide)) (h4 "rc.a" (by decide))

open Classical in
/-- **§4a: `AugRoundIn` at the cover stage's own two descriptors.**
`augRoundIn_ardRoundCom_std` states the round at `Smp = Ssw = True`; the
composition needs it at the ordering peel's `covAllSmp` and the sweep's
`covAllSsw`, and both transports go through on the base letters alone —
the round's twenty-seven names all start with `'r'`, the cover stage's
with `'s'` or `'o'`.  So neither `Smp` nor `Ssw` is a seam, and only
`ArdWord` survives (which `SolveF7CloseQ`'s `f7q` supplies from
`q ≥ 3K + 2`). -/
theorem covAllJoin_augRoundIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (hword : ArdWord C hC φ (fun m => bucketSel m) R G c w q Adm) :
    AugRoundIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm
      sweepCloseCa sweepCloseCo
      (fun j A => augStInNW ardIo ardIt ardNA j A)
      (ardSrd ardMkF ardMkT (ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo
        ardAj ardDgP ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt
        ardQo ardQt ardAd ardSd ardDgE))
      (covAllSmp n) (covAllSsw n)
      (fun j => ardRoundCom (arenaNames j).nN (ardNF j) (ardNT j) (ardNO j)
        (ardNA j) (ardIo j) (ardIt j) (ardFo j) (ardFt j) (ardDgF j)
        (ardMkF j) (ardAo j) (ardAj j) (ardDgP j) (ardMt j) (ardSg j)
        (ardTp j) (ardSk j) (ardRo j) (ardRt j) (ardMkT j) (ardOo j)
        (ardOt j) (ardQo j) (ardQt j) (ardAd j) (ardSd j) (ardDgE j))
      1025 455 588 305 287 := by
  refine augRoundIn_ardRoundCom C hC φ R G c w q ℓp htabF hbf Adm
    sweepCloseCa sweepCloseCo ardNF ardNT ardNO ardNA ardIo ardIt ardFo ardFt
    ardDgF ardMkF ardAo ardAj ardDgP ardMt ardSg ardTp ardSk ardRo ardRt
    ardMkT ardOo ardOt ardQo ardQt ardAd ardSd ardDgE _ _ hword ardNames_std
    ardCells_std ?_ ?_
  · rintro j σ σ' ⟨h1, h2, h3⟩ harr -
    have hra : σ'.arrs (sweepCloseRa j) = σ.arrs (sweepCloseRa j) :=
      covAllJoin_ardArr (s := "sc.r") rfl (by decide) harr
    have htp : σ'.arrs (covAllTpO j) = σ.arrs (covAllTpO j) :=
      covAllJoin_ardArr (s := "oc.t") rfl (by decide) harr
    have hsk : σ'.arrs (covAllSkO j) = σ.arrs (covAllSkO j) :=
      covAllJoin_ardArr (s := "oc.k") rfl (by decide) harr
    exact ⟨by rw [hra]; exact h1, by rw [htp]; exact h2, by rw [hsk]; exact h3⟩
  · rintro j σ σ' ⟨⟨hb1, hb2, hb3, hb4, hb5⟩, ⟨hp1, hp2, hp3⟩, hgr⟩ harr hvar
    have hN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN :=
      covAllJoin_ardVar (s := "sv.n") rfl (ard_nN_notMem_ardScalars j) hvar
    have hS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS :=
      covAllJoin_ardVar (s := "sv.m") rfl (ard_nS_notMem_ardScalars j) hvar
    have hao : σ'.arrs (sweepCloseAo j) = σ.arrs (sweepCloseAo j) :=
      covAllJoin_ardArr (s := "sc.p") rfl (by decide) harr
    have haj : σ'.arrs (sweepCloseAj j) = σ.arrs (sweepCloseAj j) :=
      covAllJoin_ardArr (s := "sc.j") rfl (by decide) harr
    have hdg : σ'.arrs (sweepCloseDg j) = σ.arrs (sweepCloseDg j) :=
      covAllJoin_ardArr (s := "sc.d") rfl (by decide) harr
    have hmt : σ'.arrs (sweepCloseMt j) = σ.arrs (sweepCloseMt j) :=
      covAllJoin_ardArr (s := "sc.t") rfl (by decide) harr
    have hod : σ'.arrs (sweepCloseOd j) = σ.arrs (sweepCloseOd j) :=
      covAllJoin_ardArr (s := "sc.q") rfl (by decide) harr
    have hlo : σ'.arrs (sweepCloseLo j) = σ.arrs (sweepCloseLo j) :=
      covAllJoin_ardArr (s := "sc.l") rfl (by decide) harr
    have hlm : σ'.arrs (sweepCloseLm j) = σ.arrs (sweepCloseLm j) :=
      covAllJoin_ardArr (s := "sc.g") rfl (by decide) harr
    have hco : σ'.arrs (sweepCloseCo j) = σ.arrs (sweepCloseCo j) :=
      covAllJoin_ardArr (s := "sc.o") rfl (by decide) harr
    have hcm : σ'.arrs (sweepCloseCm j) = σ.arrs (sweepCloseCm j) :=
      covAllJoin_ardArr (s := "sc.m") rfl (by decide) harr
    have hsb : σ'.arrs (sweepCloseSb j) = σ.arrs (sweepCloseSb j) :=
      covAllJoin_ardArr (s := "sc.b") rfl (by decide) harr
    have hcnt : σ'.arrs (sweepCloseCnt j) = σ.arrs (sweepCloseCnt j) :=
      covAllJoin_ardArr (s := "sc.n") rfl (by decide) harr
    have hcur : σ'.arrs (sweepCloseCur j) = σ.arrs (sweepCloseCur j) :=
      covAllJoin_ardArr (s := "sc.u") rfl (by decide) harr
    obtain ⟨g1, g2, g3, g4⟩ := hgr
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, bfsClean_of_eq hp3 hco⟩, ?_, ?_, ?_, ?_⟩
    · rw [hN, hao]; exact hb1
    · rw [hS, haj]; exact hb2
    · rw [hN, hdg]; exact hb3
    · rw [hS, hmt]; exact hb4
    · rw [hN, hod]; exact hb5
    · rw [hlo]; exact hp1
    · rw [hlm]; exact hp2
    · rw [hlm, hcm]; exact g1
    · rw [hlm, hsb]; exact g2
    · rw [hco, hcnt]; exact g3
    · rw [hco, hcur]; exact g4

/-- **The round's descriptor and the cover stage's two are jointly
inhabited.**  `covAllJoin_augRoundIn` would say nothing if `ardSrd`,
`covAllSmp` and `covAllSsw` could not hold at once; they can, and the
witness is one state — every array long except the fraternal mark
window, which `ardSrd` pins at *exactly* `nN·nN` and which is therefore
empty at a zero carrier cell.  The three name families are disjoint on
their base letters (`'r'`, `'s'`, `'o'`), so nothing has to be
reconciled. -/
theorem covAllJoin_ardSrd_inhabited (n j : ℕ) :
    ∃ σ : Env,
      ardSrd ardMkF ardMkT (ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo
        ardAj ardDgP ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt
        ardQo ardQt ardAd ardSd ardDgE) j σ ∧
      covAllSmp n j σ ∧ covAllSsw n j σ := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : Env, σ = (⟨fun _ => 0,
      fun b => if b = "rf.m" then [] else List.replicate (n * n + n + 1) 0,
      [], []⟩ : Env) := ⟨_, rfl⟩
  have hv : ∀ y : String, σ.vars y = 0 := fun y => by rw [hσ]
  have hmk : σ.arrs (ardMkF j) = [] := by rw [hσ]; simp
  have hlen : ∀ b : String, b ≠ "rf.m" → (σ.arrs b).length = n * n + n + 1 := by
    intro b hb; rw [hσ]; simp only [if_neg hb]; exact List.length_replicate
  have hzero : ∀ b : String, b ≠ "rf.m" → ∀ i, (σ.arrs b).getD i 0 = 0 := by
    intro b hb i; rw [hσ]; simp only [if_neg hb]; simp
  have hS : ∀ s : String, s.toList.head? = some 's' → lv s j ≠ "rf.m" :=
    fun s hs => ard_lv_ne_head hs (by decide) j
  have hO : ∀ s : String, s.toList.head? = some 'o' → lv s j ≠ "rf.m" :=
    fun s hs => ard_lv_ne_head hs (by decide) j
  have hreg0 : ∀ b ∈ ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo ardAj
      ardDgP ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt ardQo
      ardQt ardAd ardSd ardDgE 0, b ≠ "rf.m" := by
    intro b hb
    simp only [ardRegions, augRdAllocs, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  have hreg : ∀ b ∈ ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo ardAj
      ardDgP ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt ardQo
      ardQt ardAd ardSd ardDgE j, b ≠ "rf.m" := hreg0
  refine ⟨σ, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · intro b hb
    rw [hv, hlen b (hreg b hb)]
    simp only [ardCap]; omega
  · rw [hv, hmk]; simp
  · intro i; rw [hmk]; simp
  · intro i hi; rw [hv] at hi; omega
  · rw [hlen (sweepCloseRa j) (hS "sc.r" rfl)]; omega
  · rw [hlen (covAllTpO j) (hO "oc.t" rfl)]; omega
  · rw [hlen (covAllSkO j) (hO "oc.k" rfl)]; omega
  · rw [hv, hlen (sweepCloseAo j) (hS "sc.p" rfl)]; omega
  · rw [hv, hlen (sweepCloseAj j) (hS "sc.j" rfl)]; omega
  · rw [hv, hlen (sweepCloseDg j) (hS "sc.d" rfl)]; omega
  · rw [hv, hlen (sweepCloseMt j) (hS "sc.t" rfl)]; omega
  · rw [hv, hlen (sweepCloseOd j) (hS "sc.q" rfl)]; omega
  · rw [hlen (sweepCloseLo j) (hS "sc.l" rfl)]; omega
  · rw [hlen (sweepCloseLm j) (hS "sc.g" rfl)]; omega
  · exact fun v _ => hzero (sweepCloseCo j) (hS "sc.o" rfl) v
  · rw [hlen (sweepCloseLm j) (hS "sc.g" rfl),
      hlen (sweepCloseCm j) (hS "sc.m" rfl)]
  · rw [hlen (sweepCloseLm j) (hS "sc.g" rfl),
      hlen (sweepCloseSb j) (hS "sc.b" rfl)]
  · rw [hlen (sweepCloseCo j) (hS "sc.o" rfl),
      hlen (sweepCloseCnt j) (hS "sc.n" rfl)]
  · rw [hlen (sweepCloseCo j) (hS "sc.o" rfl),
      hlen (sweepCloseCur j) (hS "sc.u" rfl)]

/-- **Seam 1.**  `augBasePeelIn_bucketPeelBuild` pins the base pass's
`Sbd` to three length clauses against the **root** carrier `n`, and
`augBaseOrientIn_orCom`'s `hSbd` asks that `Sbd` bound three arrays
against `σ.vars (arenaNames j).nN`.  No `Sbd` of the first shape does:
a state whose carrier cell exceeds every array's length satisfies the
peel's descriptor and refutes the orientation's demand.  The failure is
**unconditional in the six names** — no disequality bundle can repair
it — so `augBaseIn_of_adj_peel_orient` cannot be instantiated with both
landed leaves. -/
theorem coverAllBase_hSbd_unsatisfiable (n : ℕ)
    (bra tpO skO io it cn : ℕ → String) (j : ℕ) :
    ¬ (∀ (jj : ℕ) (σ : Env),
        (n ≤ (σ.arrs (bra jj)).length ∧ n ≤ (σ.arrs (tpO jj)).length ∧
          n * n + n ≤ (σ.arrs (skO jj)).length) →
        σ.vars (arenaNames jj).nN + 1 ≤ (σ.arrs (io jj)).length ∧
          σ.vars (arenaNames jj).nS ≤ (σ.arrs (it jj)).length ∧
          σ.vars (arenaNames jj).nN ≤ (σ.arrs (cn jj)).length) := by
  intro h
  obtain ⟨σ, hσ⟩ : ∃ σ : Env, σ = (⟨fun _ => n * n + n + 1,
      fun _ => List.replicate (n * n + n) 0, [], []⟩ : Env) := ⟨_, rfl⟩
  have hlen : ∀ b : String, (σ.arrs b).length = n * n + n := by
    intro b; rw [hσ]; exact List.length_replicate
  have hvar : ∀ y : String, σ.vars y = n * n + n + 1 := by intro y; rw [hσ]
  have hn : n ≤ n * n + n := Nat.le_add_left n _
  obtain ⟨h1, -, -⟩ := h j σ ⟨by rw [hlen]; exact hn, by rw [hlen]; exact hn,
    by rw [hlen]⟩
  rw [hvar, hlen] at h1
  omega

/-- **Seam 2.**  `augBaseOrientIn_orCom`'s `hSrd` duty is handed a frame
that says nothing at all about the two arrays the pass writes — the
orientation pair `(io j, it j)` — and no length clause.  The rounds'
descriptor `ardSrd` constrains exactly those two arrays (they head
`ardRegions`) at `ardCap` of the carrier cell.  So for **every** `Sbd`
that holds at even one state, the duty is unsatisfiable: shortening
`io j` to nothing preserves the whole frame and destroys `ardSrd`.

The repair is one conjunct — `(∀ b, (σ'.arrs b).length = (σ.arrs b).length)`,
which `augBaseOrientIn_orCom`'s own proof already has in scope and which
its sibling `augBasePeelIn_bucketPeelBuild` already passes to its
`hSmp`/`hSsw`. -/
theorem coverAllBase_hSrd_not_ardSrd
    {io it cn nA mkF mkT fo ft dgF ao aj dgP mt sg tp sk ro rt o' t' qo qt
      ad sd dgE : ℕ → String}
    {Sbd : ℕ → Env → Prop} {j : ℕ} {σ₀ : Env} (h0 : Sbd j σ₀) :
    ¬ (∀ (jj : ℕ) (σ σ' : Env), Sbd jj σ →
        (∀ b, b ≠ io jj → b ≠ it jj → b ≠ cn jj → σ'.arrs b = σ.arrs b) →
        (∀ y, y ∉ nA jj :: orScalars → σ'.vars y = σ.vars y) →
        ardSrd mkF mkT (ardRegions io it fo ft dgF ao aj dgP mt sg tp sk
          ro rt mkT o' t' qo qt ad sd dgE) jj σ') := by
  intro h
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Env, σ' = { σ₀ with
      arrs := fun b => if b = io j then [] else σ₀.arrs b } := ⟨_, rfl⟩
  have harr : ∀ b, b ≠ io j → b ≠ it j → b ≠ cn j → σ'.arrs b = σ₀.arrs b := by
    intro b hb _ _; rw [hσ']; exact if_neg hb
  have hvar : ∀ y, y ∉ nA j :: orScalars → σ'.vars y = σ₀.vars y := by
    intro y _; rw [hσ']
  have hio : σ'.arrs (io j) = [] := by rw [hσ']; exact if_pos rfl
  obtain ⟨hreg, -, -, -⟩ := h j σ₀ σ' h0 harr hvar
  have hmem : io j ∈ ardRegions io it fo ft dgF ao aj dgP mt sg tp sk
      ro rt mkT o' t' qo qt ad sd dgE j := by
    simp [ardRegions]
  have := hreg (io j) hmem
  rw [hio] at this
  simp only [List.length_nil, ardCap] at this
  omega

/-- **Seam 3.**  `augSymCsrIn_symComW`'s `hSrd` asks the rounds'
descriptor for `(σ.arrs (stO j)).length = 2 * σ.vars (nA j)` — an
equality, because `AugSymCsrIn`'s postcondition is a bare `GraphCsr`.
But `Srd` is `covAugAdjSelIn_of_base_rounds_sym`'s round *invariant*,
`nA j` holds the current orientation's arc count (`augStInNW`), and no
run changes an array's length.  So the two together **prove that every
round adds no arc**, at every input, every level, every admissible
non-edgeless arena, and every round with an inhabited precondition.

Only the second clause of `symCsrSizes` is used; the first
(`(σ.arrs (soO j)).length = σ.vars (arenaNames j).nN + 1`) is against
the carrier cell, which the rounds do preserve, and is harmless. -/
theorem coverAllSym_srd_forces_constant (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co io it nA soO stO : ℕ → String) (Srd Smp Ssw : ℕ → Env → Prop)
    (rdC : ℕ → Com) (kn ka kf kt kc : ℕ)
    (hrd : AugRoundIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      (fun j A => augStInNW io it nA j A) Srd Smp Ssw rdC kn ka kf kt kc)
    (hsz : ∀ j σ, Srd j σ → symCsrSizes nA soO stO j σ)
    {x : List ℕ} (hx : x ∈ mcD n G c w)
    {j : ℕ} (hj : j < (Headline.headlineSetup C hC φ).depth)
    {A : Arena ((Headline.headlineSetup C hC φ).pal j) n}
    (hAdm : Adm j A) (hbot : ¬ A.G = ⊥) {i : ℕ} (hi : i < R) {σ : Env}
    (hσ : ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ ∧
      augStInNW io it nA j A (selChain (sel A.N) A.G i) σ ∧ Srd j σ ∧
      A.N ≤ (σ.arrs (ca j)).length ∧
      A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ) :
    arcCount (selChain (sel A.N) A.G i)
      = arcCount (greedyStep
          (selRank (sel A.N) (fratGraph (selChain (sel A.N) A.G i)))
          (selChain (sel A.N) A.G i)) := by
  obtain ⟨σ', hrun, -, hst', hSrd', -⟩ := hrd x hx j hj A hAdm hbot i hi σ hσ
  have hσL := (hsz j σ hσ.2.2.1).2
  have hσ'L := (hsz j σ' hSrd').2
  rw [hσ.2.1.2.2] at hσL
  rw [hst'.2.2] at hσ'L
  have hlen := run_arrs_length_eq hrun (stO j)
  omega

/-- **Seam 3, in the form that shows it is a no-go and not a curiosity.**
`arcCount_greedyStep` (`SolveAugEmit.lean:477`) makes a round's arc count
the old one plus the two phases' picks, *exactly*.  So the equality the
previous theorem forces says that the round emits **no fraternal edge
and no transitive edge at all** — at every input, every level, every
admissible non-edgeless arena and every round.  A tight
transitive–fraternal augmentation that emits nothing is not the
augmentation; the composition therefore cannot be carried out at these
two landed statements. -/
theorem coverAllSym_srd_forces_no_emission (C : GraphClass)
    (hC : NowhereDense C) (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co io it nA soO stO : ℕ → String) (Srd Smp Ssw : ℕ → Env → Prop)
    (rdC : ℕ → Com) (kn ka kf kt kc : ℕ)
    (hrd : AugRoundIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      (fun j A => augStInNW io it nA j A) Srd Smp Ssw rdC kn ka kf kt kc)
    (hsz : ∀ j σ, Srd j σ → symCsrSizes nA soO stO j σ)
    {x : List ℕ} (hx : x ∈ mcD n G c w)
    {j : ℕ} (hj : j < (Headline.headlineSetup C hC φ).depth)
    {A : Arena ((Headline.headlineSetup C hC φ).pal j) n}
    (hAdm : Adm j A) (hbot : ¬ A.G = ⊥) {i : ℕ} (hi : i < R) {σ : Env}
    (hσ : ArenaStW (arenaNames j) (hbf j) (Impl.ofArena A (htabF j A)) σ ∧
      augStInNW io it nA j A (selChain (sel A.N) A.G i) σ ∧ Srd j σ ∧
      A.N ≤ (σ.arrs (ca j)).length ∧
      A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ) :
    (∑ v, (emFrat (selChain (sel A.N) A.G i)
        (selRank (sel A.N) (fratGraph (selChain (sel A.N) A.G i))) v).card)
      + (∑ v, (emTrans (selChain (sel A.N) A.G i)
        (selRank (sel A.N) (fratGraph (selChain (sel A.N) A.G i))) v).card)
      = 0 := by
  have h := coverAllSym_srd_forces_constant C hC φ sel R G c w q ℓp htabF hbf
    Adm ca co io it nA soO stO Srd Smp Ssw rdC kn ka kf kt kc hrd hsz hx hj
    hAdm hbot hi hσ
  rw [arcCount_greedyStep] at h
  omega

/-! ## §5 `CoverAllIn`, closed

`SolveAugSeamFix` repairs the three seams §4b–§4d pinned and discharges
`CovAugAdjSelIn` at a concrete family.  What is left for this file is
what §2 always said was left: feed it to `covAllJoin_coverAllIn`.  The
two descriptors the augmentation must carry are §1's own `covAllSmp` and
`covAllSsw`, and both ride through on the same fact §4a used — the
augmentation's forty written arrays are the round's `'r'` names, the
base's and merge's `'y'` names and the four `"oc.*"` output regions, and
none of those is one of the sweep's `"sc.*"` or the ordering peel's two.

The residual hypotheses are exactly two: `1 ≤ q` and `ArdWord`. -/

/-- Every name the sweep and the ordering peel speak about is outside the
augmentation's write set: one line per name, and the line is `decide`. -/
theorem covAllJoin_notWrite {s : String} (h1 : s.length = 4)
    (h2 : ∀ b ∈ augSeamArdNames, s ≠ b)
    (h3 : ∀ t ∈ augSeamBaseBases, s ≠ t)
    (h4 : ∀ t ∈ augSeamRegBases, s ≠ t) (j : ℕ) :
    lv s j ∉ augSeamWrites j := augSeamNotWrite h1 h2 h3 h4 j

/-- **The ordering peel's scratch rides through the augmentation.** -/
theorem covAllJoin_hSmpW (n j : ℕ) (σ σ' : Env)
    (harr : ∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b)
    (h : covAllSmp n j σ) : covAllSmp n j σ' := by
  have hA : ∀ s : String, s.length = 4 → (∀ b ∈ augSeamArdNames, s ≠ b) →
      (∀ t ∈ augSeamBaseBases, s ≠ t) → (∀ t ∈ augSeamRegBases, s ≠ t) →
      σ'.arrs (lv s j) = σ.arrs (lv s j) :=
    fun s k1 k2 k3 k4 => harr _ (covAllJoin_notWrite k1 k2 k3 k4 j)
  have hra : σ'.arrs (sweepCloseRa j) = σ.arrs (sweepCloseRa j) :=
    hA "sc.r" (by decide) (by decide) (by decide) (by decide)
  have htp : σ'.arrs (covAllTpO j) = σ.arrs (covAllTpO j) :=
    hA "oc.t" (by decide) (by decide) (by decide) (by decide)
  have hsk : σ'.arrs (covAllSkO j) = σ.arrs (covAllSkO j) :=
    hA "oc.k" (by decide) (by decide) (by decide) (by decide)
  exact ⟨by rw [hra]; exact h.1, by rw [htp]; exact h.2.1,
    by rw [hsk]; exact h.2.2⟩

/-- **The sweep's scratch rides through the augmentation.** -/
theorem covAllJoin_hSswW (n j : ℕ) (σ σ' : Env)
    (harr : ∀ b : String, b ∉ augSeamWrites j → σ'.arrs b = σ.arrs b)
    (hvar : ∀ y : String, y ∉ augSeamCells j → σ'.vars y = σ.vars y)
    (h : covAllSsw n j σ) : covAllSsw n j σ' := by
  obtain ⟨⟨hb1, hb2, hb3, hb4, hb5⟩, ⟨hp1, hp2, hp3⟩, hgr⟩ := h
  have hA : ∀ s : String, s.length = 4 → (∀ b ∈ augSeamArdNames, s ≠ b) →
      (∀ t ∈ augSeamBaseBases, s ≠ t) → (∀ t ∈ augSeamRegBases, s ≠ t) →
      σ'.arrs (lv s j) = σ.arrs (lv s j) :=
    fun s k1 k2 k3 k4 => harr _ (covAllJoin_notWrite k1 k2 k3 k4 j)
  have hN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN :=
    hvar _ (augSeam_nN_notMem_cells j)
  have hS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS :=
    hvar _ (augSeam_nS_notMem_cells j)
  have hao : σ'.arrs (sweepCloseAo j) = σ.arrs (sweepCloseAo j) :=
    hA "sc.p" (by decide) (by decide) (by decide) (by decide)
  have haj : σ'.arrs (sweepCloseAj j) = σ.arrs (sweepCloseAj j) :=
    hA "sc.j" (by decide) (by decide) (by decide) (by decide)
  have hdg : σ'.arrs (sweepCloseDg j) = σ.arrs (sweepCloseDg j) :=
    hA "sc.d" (by decide) (by decide) (by decide) (by decide)
  have hmt : σ'.arrs (sweepCloseMt j) = σ.arrs (sweepCloseMt j) :=
    hA "sc.t" (by decide) (by decide) (by decide) (by decide)
  have hod : σ'.arrs (sweepCloseOd j) = σ.arrs (sweepCloseOd j) :=
    hA "sc.q" (by decide) (by decide) (by decide) (by decide)
  have hlo : σ'.arrs (sweepCloseLo j) = σ.arrs (sweepCloseLo j) :=
    hA "sc.l" (by decide) (by decide) (by decide) (by decide)
  have hlm : σ'.arrs (sweepCloseLm j) = σ.arrs (sweepCloseLm j) :=
    hA "sc.g" (by decide) (by decide) (by decide) (by decide)
  have hco : σ'.arrs (sweepCloseCo j) = σ.arrs (sweepCloseCo j) :=
    hA "sc.o" (by decide) (by decide) (by decide) (by decide)
  have hcm : σ'.arrs (sweepCloseCm j) = σ.arrs (sweepCloseCm j) :=
    hA "sc.m" (by decide) (by decide) (by decide) (by decide)
  have hsb : σ'.arrs (sweepCloseSb j) = σ.arrs (sweepCloseSb j) :=
    hA "sc.b" (by decide) (by decide) (by decide) (by decide)
  have hcnt : σ'.arrs (sweepCloseCnt j) = σ.arrs (sweepCloseCnt j) :=
    hA "sc.n" (by decide) (by decide) (by decide) (by decide)
  have hcur : σ'.arrs (sweepCloseCur j) = σ.arrs (sweepCloseCur j) :=
    hA "sc.u" (by decide) (by decide) (by decide) (by decide)
  obtain ⟨g1, g2, g3, g4⟩ := hgr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, bfsClean_of_eq hp3 hco⟩, ?_, ?_, ?_, ?_⟩
  · rw [hN, hao]; exact hb1
  · rw [hS, haj]; exact hb2
  · rw [hN, hdg]; exact hb3
  · rw [hS, hmt]; exact hb4
  · rw [hN, hod]; exact hb5
  · rw [hlo]; exact hp1
  · rw [hlm]; exact hp2
  · rw [hlm, hcm]; exact g1
  · rw [hlm, hsb]; exact g2
  · rw [hco, hcnt]; exact g3
  · rw [hco, hcur]; exact g4

open Classical in
/-- **`CoverAllIn`, closed.**  The whole cover stage — the augmentation
(base, `R` rounds, symmetrization), the bucket peel that turns its output
into the rank array, the deletable-adjacency build, the peeled BFS sweep
and the grouping — at the summed budget, from **`1 ≤ q` and `ArdWord`
alone**.

`ArdWord` is the round's own word obligation (`SolveAugRoundIn` §4), which
`SolveF7CloseQ`'s `f7q` supplies from `q ≥ 3·K + 2`; it is not a seam of
this composition.  The budget is `covAllJoin_Kord_eq`'s single
`augChainCost` plus the sweep's `peelK` column, so `covAllJoin_Kord_le`
and `covAllJoin_Ksw_le` apply to it unchanged. -/
theorem covAllJoin_coverAllIn_closed (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (hq : 1 ≤ q)
    (hword : ArdWord C hC φ (fun m => bucketSel m) R G c w q Adm) :
    CoverAllIn C hC φ (selOrderingRoutine (fun m => bucketSel m) R) G c w q ℓp
      htabF hbf Adm sweepCloseCa sweepCloseCo sweepCloseCm
      (fun j σ => (augSeamSag n j σ ∧ covAllSmp n j σ) ∧ covAllSsw n j σ)
      (fun j => .seq
        (.seq
          (.seq (.seq (augSeamBaseCom j) (comIter (augSeamRoundComStd j) R))
            (augSeamSymCom j))
          (bucketPeelCom (covAllAoO j) (covAllAjO j) (covAllDgO j)
            (covAllMtO j) (sweepCloseRa j) (covAllTpO j) (covAllSkO j)
            (arenaNames j).nN))
        (.seq
          (bldCom (arenaNames j).nN (arenaNames j).nS (arenaNames j).off
            (arenaNames j).tgt (sweepCloseRa j) (sweepCloseAo j)
            (sweepCloseAj j) (sweepCloseDg j) (sweepCloseMt j) (sweepCloseOd j))
          (.seq
            (sweepCom
              (bfsTurnCom (Headline.headlineSetup C hC φ).R (sweepCloseCa j)
                (sweepCloseCo j) (sweepCloseAo j) (sweepCloseAj j)
                (sweepCloseDg j) (sweepCloseLo j) (sweepCloseLm j)
                (arenaNames j).nN)
              (sweepCloseCa j) (sweepCloseLo j) (sweepCloseAo j)
              (sweepCloseAj j) (sweepCloseDg j) (sweepCloseMt j)
              (sweepCloseOd j) (arenaNames j).nN)
            (grCom (arenaNames j).nN (sweepCloseLo j) (sweepCloseLm j)
              (sweepCloseOd j) (sweepCloseCo j) (sweepCloseCm j)
              (sweepCloseCnt j) (sweepCloseCur j) (sweepCloseSb j)))))
      (fun _j A => (augChainCost 545 554 113 1025 455 588 305 287 171 196 84
            (bucketSel A.N) A.G R + linearPeelBudget R 313 118 40 A)
        + peelK (12 * (Headline.headlineSetup C hC φ).R + 362) 154 192
            (Headline.headlineSetup C hC φ) A
            ((selOrderingRoutine (fun m => bucketSel m) R A.N A.G).order)) :=
  covAllJoin_coverAllIn C hC φ R G c w q ℓp htabF hbf Adm (augSeamSag n) _ _ hq
    (augSeamCovAugAdjSelIn C hC φ R G c w q ℓp htabF hbf Adm sweepCloseCa
      sweepCloseCo (covAllSmp n) (covAllSsw n) hq hword
      (fun j σ σ' h harr _ => covAllJoin_hSmpW n j σ σ' harr h)
      (fun j σ σ' h harr hvar => covAllJoin_hSswW n j σ σ' harr hvar h))

/-- **… and the budget is the one §3 already measured.**  The ordering
pass folds into one `augChainCost` (`covAllJoin_Kord_eq`), so the closed
statement's `Kag + linearPeelBudget` is `covAllJoin_Kord_le`'s subject
verbatim. -/
theorem covAllJoin_closed_Kord {Λ n₀ : ℕ} (A : Arena Λ n₀) (R : ℕ) :
    augChainCost 545 554 113 1025 455 588 305 287 171 196 84
        (bucketSel A.N) A.G R
      + linearPeelBudget R 313 118 40 A
    = augChainCost 545 554 113 1025 455 588 305 287 484 432 124
        (bucketSel A.N) A.G R :=
  covAllJoin_Kord_eq A R

/-- **§5 is not a statement about an empty precondition.**  The
augmentation's descriptor `augSeamSag` sits in `CovAugAdjSelIn`'s
*precondition*, so it owes a witness — and it owes one **jointly with**
the two descriptors §1 introduces, since all three must hold of the same
state.  Here is that state, at every `n` and every level: every array
long except the fraternal mark window, which `ardSrd` pins at exactly
`nN·nN` and which is therefore empty at a zero carrier cell.  The three
name families are disjoint (`'r'`, `'y'`, `'s'`, `'o'`), so nothing has
to be reconciled. -/
theorem covAllJoin_sag_inhabited (n j : ℕ) :
    ∃ σ : Env, augSeamSag n j σ ∧ covAllSmp n j σ ∧ covAllSsw n j σ := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : Env, σ = (⟨fun _ => 0,
      fun b => if b = "rf.m" then [] else List.replicate (n * n + n + 1) 0,
      [], []⟩ : Env) := ⟨_, rfl⟩
  have hv : ∀ y : String, σ.vars y = 0 := fun y => by rw [hσ]
  have hmk : σ.arrs "rf.m" = [] := by rw [hσ]; simp
  have hlen : ∀ b : String, b ≠ "rf.m" → (σ.arrs b).length = n * n + n + 1 := by
    intro b hb; rw [hσ]; simp only [if_neg hb]; exact List.length_replicate
  have hzero : ∀ b : String, b ≠ "rf.m" → ∀ i, (σ.arrs b).getD i 0 = 0 := by
    intro b hb i; rw [hσ]; simp only [if_neg hb]; simp
  have hLv : ∀ s : String, s.length = 4 → s ≠ "rf.m" → lv s j ≠ "rf.m" :=
    fun s h1 h2 => lv_ne_len4 h1 (by decide) h2 j
  have hreg : ∀ b ∈ augSeamRegsAll j, b ≠ "rf.m" := by
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
      exact lv_ne_len4 (augSeamRegBases_len t ht) (by decide)
        (augSeamRegBases_ne_ard t ht "rf.m" (by decide)) j
    · exact (show ∀ b ∈ ardRegionsStd 0, b ≠ "rf.m" by decide) b h
  refine ⟨σ, ⟨⟨⟨fun b hb => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hv, hlen b (hreg b hb)]; simp only [ardCap]; omega
  · rw [hv, hmk]; simp
  · intro i; rw [hmk]; simp
  · intro i hi; rw [hv] at hi; omega
  · rw [hv, hlen (ardIt j) (show ("ri.t" : String) ≠ "rf.m" by decide)]; omega
  · rw [hv, hlen (augSeamCn j) (hLv "yc.n" (by decide) (by decide))]; omega
  · rw [hlen (augSeamRa j) (hLv "yr.a" (by decide) (by decide))]; omega
  · rw [hlen (augSeamTp j) (hLv "yt.p" (by decide) (by decide))]; omega
  · rw [hlen (augSeamSk j) (hLv "yk.c" (by decide) (by decide))]; omega
  · rw [hv, hlen (augSeamAo j) (hLv "ya.o" (by decide) (by decide))]; omega
  · rw [hv, hlen (augSeamAj j) (hLv "ya.j" (by decide) (by decide))]; omega
  · rw [hv, hlen (augSeamDg j) (hLv "ya.d" (by decide) (by decide))]; omega
  · rw [hv, hlen (augSeamMt j) (hLv "ya.m" (by decide) (by decide))]; omega
  · rw [hlen (sweepCloseRa j) (hLv "sc.r" (by decide) (by decide))]; omega
  · rw [hlen (covAllTpO j) (hLv "oc.t" (by decide) (by decide))]; omega
  · rw [hlen (covAllSkO j) (hLv "oc.k" (by decide) (by decide))]; omega
  · rw [hv, hlen (sweepCloseAo j) (hLv "sc.p" (by decide) (by decide))]; omega
  · rw [hv, hlen (sweepCloseAj j) (hLv "sc.j" (by decide) (by decide))]; omega
  · rw [hv, hlen (sweepCloseDg j) (hLv "sc.d" (by decide) (by decide))]; omega
  · rw [hv, hlen (sweepCloseMt j) (hLv "sc.t" (by decide) (by decide))]; omega
  · rw [hv, hlen (sweepCloseOd j) (hLv "sc.q" (by decide) (by decide))]; omega
  · rw [hlen (sweepCloseLo j) (hLv "sc.l" (by decide) (by decide))]; omega
  · rw [hlen (sweepCloseLm j) (hLv "sc.g" (by decide) (by decide))]; omega
  · exact fun v _ => hzero (sweepCloseCo j) (hLv "sc.o" (by decide) (by decide)) v
  · rw [hlen (sweepCloseLm j) (hLv "sc.g" (by decide) (by decide)),
      hlen (sweepCloseCm j) (hLv "sc.m" (by decide) (by decide))]
  · rw [hlen (sweepCloseLm j) (hLv "sc.g" (by decide) (by decide)),
      hlen (sweepCloseSb j) (hLv "sc.b" (by decide) (by decide))]
  · rw [hlen (sweepCloseCo j) (hLv "sc.o" (by decide) (by decide)),
      hlen (sweepCloseCnt j) (hLv "sc.n" (by decide) (by decide))]
  · rw [hlen (sweepCloseCo j) (hLv "sc.o" (by decide) (by decide)),
      hlen (sweepCloseCur j) (hLv "sc.u" (by decide) (by decide))]

/-! ## §6 Axiom audit

§1–§3 quote `Headline.headlineSetup` and therefore carry Lax12's
endorsed `uniformlyQuasiWide_of_nowhereDense`, exactly like the landed
`covOrderIn_bucketPeel` and `sweepClose_covSweepIn_names` they compose.
§4's first two seams are pure statements about `Env` and rest on the
three standard axioms alone. -/

#print axioms covAllJoin_hSsw

#print axioms covAllJoin_covOrderIn

#print axioms covAllJoin_coverAllIn

#print axioms covAllJoin_sc_inhabited

#print axioms covAllJoin_Kord_eq

#print axioms covAllJoin_Kord_le

#print axioms covAllJoin_exists_Kord_le

#print axioms covAllJoin_Ksw_le

#print axioms covAllJoin_augRoundIn

#print axioms covAllJoin_ardSrd_inhabited

#print axioms coverAllBase_hSbd_unsatisfiable

#print axioms coverAllBase_hSrd_not_ardSrd

#print axioms coverAllSym_srd_forces_constant

#print axioms coverAllSym_srd_forces_no_emission

#print axioms covAllJoin_hSmpW

#print axioms covAllJoin_hSswW

#print axioms covAllJoin_coverAllIn_closed

#print axioms covAllJoin_sag_inhabited

end Lax3Proofs.Prog
