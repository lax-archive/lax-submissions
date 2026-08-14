import Lax3Proofs.Refine.CoverActiveStreamRoot
import Lax3Proofs.Refine.G2CostProbe

/-!
# Cost closure for the streamed active driver

The streamed root exposes three size-indexed charges: the dead-aware
scatter, the reusable centre lifecycle, and search followed by radix sort.
This file proves that each is affine in the block weight and feeds those
bounds to the canonical sigma recurrence.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamCost

open Finset
open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.Refine.CoverActiveStreamLifecycle
open Lax3Proofs.Refine.CoverActiveStreamRoot
open Lax3Proofs.Refine.OrderActiveBudget
open Lax3Proofs.Refine.ScatterDeadTurn

/-! ## Scatter -/

/-- A carrier-free affine coefficient for one dead-aware atom. -/
noncomputable def streamDeadAtomCoeff {L : ℕ} (β : DistFO L 1) (mb t : ℕ) : ℕ :=
  154 * t + 122 + (140 * t + 14 * mb +
    Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β + 104)

theorem deadAtomKX_le_streamDeadAtomCoeff {L : ℕ} (β : DistFO L 1)
    (n a mb z t : ℕ) (ha : a ≤ z) :
    deadAtomKX β n a mb z z t ≤ streamDeadAtomCoeff β mb t * (z + 1) := by
  refine le_trans (deadAtomKX_le_blk β n a mb z z t) ?_
  rw [deadAtomKBlk_closed]
  simp only [streamDeadAtomCoeff]
  nlinarith [Nat.zero_le z, Nat.zero_le t,
    Nat.zero_le (Lax3Proofs.Refine.ScatterDeadPass.atomBitCost β)]

/-- The sum of all atom coefficients appearing at one driver depth. -/
noncomputable def streamLevelAtomCoeff (q_top cap mb : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (j : ℕ) : ℕ :=
  ((tablesAt q_top cap mb φ j).map fun β =>
      ((bcAtomsOf q_top (stepFml cap mb j β)).2.map fun sa =>
        streamDeadAtomCoeff sa.β mb sa.t).sum).sum

/-- One coefficient simultaneously pays every atom at every recursive depth. -/
noncomputable def streamAtomCoeff (q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  ∑ j ∈ range ell, streamLevelAtomCoeff q_top cap mb φ j

theorem streamDeadAtomCoeff_le_global
    {q_top cap mb ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hj : j < ell) {β : DistFO (sigL cap mb j) 1}
    (hβ : β ∈ tablesAt q_top cap mb φ j)
    {sa : Lax3.ScatterSentences.ScatterSentence (sigL cap mb (j + 1))}
    (hsa : sa ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2) :
    streamDeadAtomCoeff sa.β mb sa.t ≤ streamAtomCoeff q_top cap mb ell φ := by
  have hsaMem : streamDeadAtomCoeff sa.β mb sa.t ∈
      ((bcAtomsOf q_top (stepFml cap mb j β)).2.map fun s =>
        streamDeadAtomCoeff s.β mb s.t) := by
    exact List.mem_map.mpr ⟨sa, hsa, rfl⟩
  have hsaSum : streamDeadAtomCoeff sa.β mb sa.t ≤
      ((bcAtomsOf q_top (stepFml cap mb j β)).2.map fun s =>
        streamDeadAtomCoeff s.β mb s.t).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hsaMem
  have hβMem :
      ((bcAtomsOf q_top (stepFml cap mb j β)).2.map fun s =>
        streamDeadAtomCoeff s.β mb s.t).sum ∈
      ((tablesAt q_top cap mb φ j).map fun γ =>
        ((bcAtomsOf q_top (stepFml cap mb j γ)).2.map fun s =>
          streamDeadAtomCoeff s.β mb s.t).sum) := by
    exact List.mem_map.mpr ⟨β, hβ, rfl⟩
  have hlevel :
      ((bcAtomsOf q_top (stepFml cap mb j β)).2.map fun s =>
        streamDeadAtomCoeff s.β mb s.t).sum ≤
      streamLevelAtomCoeff q_top cap mb φ j := by
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ hβMem
  have hglobal : streamLevelAtomCoeff q_top cap mb φ j ≤
      streamAtomCoeff q_top cap mb ell φ := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (mem_range.mpr hj)
  exact hsaSum.trans (hlevel.trans hglobal)

/-- The total atom count is used only to turn the two finite scatter folds
into one formula-dependent coefficient. -/
noncomputable def streamAtomCount (q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  ∑ j ∈ range ell,
    ((tablesAt q_top cap mb φ j).map fun β =>
      (bcAtomsOf q_top (stepFml cap mb j β)).2.length).sum

noncomputable def streamTableCount (q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  ∑ j ∈ range ell, (tablesAt q_top cap mb φ j).length

theorem atom_length_le_streamAtomCount
    {q_top cap mb ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hj : j < ell) {β : DistFO (sigL cap mb j) 1}
    (hβ : β ∈ tablesAt q_top cap mb φ j) :
    (bcAtomsOf q_top (stepFml cap mb j β)).2.length ≤
      streamAtomCount q_top cap mb ell φ := by
  have hmem : (bcAtomsOf q_top (stepFml cap mb j β)).2.length ∈
      ((tablesAt q_top cap mb φ j).map fun γ =>
        (bcAtomsOf q_top (stepFml cap mb j γ)).2.length) :=
    List.mem_map.mpr ⟨β, hβ, rfl⟩
  have hlevel := List.single_le_sum (fun _ _ => Nat.zero_le _)
    _ hmem
  have hout :
      ((tablesAt q_top cap mb φ j).map fun γ =>
        (bcAtomsOf q_top (stepFml cap mb j γ)).2.length).sum ≤
        streamAtomCount q_top cap mb ell φ := by
    exact Finset.single_le_sum
      (f := fun i => ((tablesAt q_top cap mb φ i).map fun γ =>
        (bcAtomsOf q_top (stepFml cap mb i γ)).2.length).sum)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr hj)
  exact hlevel.trans hout

theorem table_length_le_streamTableCount
    {q_top cap mb ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hj : j < ell) :
    (tablesAt q_top cap mb φ j).length ≤
      streamTableCount q_top cap mb ell φ :=
  Finset.single_le_sum
    (f := fun i => (tablesAt q_top cap mb φ i).length)
    (fun _ _ => Nat.zero_le _) (mem_range.mpr hj)

noncomputable def streamKatom (q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (z : ℕ) : ℕ :=
  streamAtomCoeff q_top cap mb ell φ * (z + 1)

noncomputable def streamKi (q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (_j z : ℕ) : ℕ :=
  streamKatom q_top cap mb ell φ z * streamAtomCount q_top cap mb ell φ + 1

noncomputable def streamKsc (q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (_j z : ℕ) : ℕ :=
  streamKi q_top cap mb ell φ 0 z * streamTableCount q_top cap mb ell φ + 1

/-- Affine coefficient of the complete two-fold scatter budget. -/
noncomputable def streamScatterCoeff (q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  (streamAtomCoeff q_top cap mb ell φ *
      streamAtomCount q_top cap mb ell φ + 1) *
    streamTableCount q_top cap mb ell φ + 1

theorem streamKsc_le_coeff (q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (j z : ℕ) :
    streamKsc q_top cap mb ell φ j z ≤
      streamScatterCoeff q_top cap mb ell φ * (z + 1) := by
  simp only [streamKsc, streamKi, streamKatom, streamScatterCoeff]
  nlinarith [Nat.zero_le z,
    Nat.zero_le (streamAtomCoeff q_top cap mb ell φ),
    Nat.zero_le (streamAtomCount q_top cap mb ell φ),
    Nat.zero_le (streamTableCount q_top cap mb ell φ)]

/-! ## Search, sorting, and the centre lifecycle -/

theorem nat_affine_le_unit (A C z : ℕ) :
    A * z + C ≤ (A + C) * (z + 1) := by
  nlinarith [Nat.zero_le A, Nat.zero_le C, Nat.zero_le z]

def streamSearchCoeff (bits : ℕ) : ℕ :=
  streamSearchSortCost bits 1 1

theorem streamSearchSortCost_le_coeff (bits z : ℕ) :
    streamSearchSortCost bits z z ≤ streamSearchCoeff bits * (z + 1) := by
  simp only [streamSearchCoeff, streamSearchSortCost,
    Lax3Proofs.Refine.CoverActiveStreamTurn.activeStreamTurnK,
    Lax3Proofs.Refine.BfsBlock.bfsBlockK,
    Lax3Proofs.Refine.CoverActiveStreamSort.activeStreamSortK,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixBlockCost,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixPassCost,
    Lax3Proofs.Refine.CoverActiveRadixPass.stableScatterCost,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitCost,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitSlotK,
    Lax3Proofs.Refine.CoverActiveRadixPass.copyBackSlotK]
  nlinarith [Nat.zero_le bits, Nat.zero_le z]

/-- Unit-block coefficients for the two size-sensitive halves of centre
preparation. -/
def streamPlayCoeff (cap j : ℕ) : ℕ :=
  254 + Lax3Proofs.Refine.CoverActiveStreamPlay.streamPlayCost 0 0 cap j

def streamEnumColourSlope (cap mb L : ℕ) : ℕ :=
  30 + 18 * L + 18 + (14 + 75 * cap) * mb +
    (18 + 75 * cap) * (L + 1)

def streamEnumColourCoeff (cap mb j : ℕ) : ℕ :=
  streamEnumColourSlope cap mb (sigL cap mb j) +
    Lax3Proofs.Refine.CoverActiveStreamColour.streamEnumColourCost
      0 0 cap mb (sigL cap mb j)

noncomputable def streamPrepareCoeff (q_top cap mb j : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  streamPlayCoeff cap j + streamEnumColourCoeff cap mb j +
    Lax3Proofs.Refine.CoverActiveStreamKill.streamKillListCost q_top cap mb j φ

theorem streamPlayCost_le_coeff (cap j z : ℕ) :
    Lax3Proofs.Refine.CoverActiveStreamPlay.streamPlayCost z z cap j ≤
      streamPlayCoeff cap j * (z + 1) := by
  have heq : Lax3Proofs.Refine.CoverActiveStreamPlay.streamPlayCost z z cap j =
      254 * z + Lax3Proofs.Refine.CoverActiveStreamPlay.streamPlayCost 0 0 cap j := by
    simp only [Lax3Proofs.Refine.CoverActiveStreamPlay.streamPlayCost,
      Lax3Proofs.Refine.CoverActiveStreamLoad.streamClusterLoadCost,
      Lax3Proofs.Refine.CoverActiveStreamMask.streamBlockAndCost,
      Lax3Proofs.RamDriverDescend.cacheRoundCost,
      Lax3Proofs.Refine.BfsBlockPar.bfsBlockParK,
      Lax3Proofs.Refine.CoverActiveStreamBatch.streamBatchCachedCost,
      Lax3Proofs.Refine.CoverActiveStreamChild.streamChildFilterCost,
      Lax3Proofs.Refine.ScatterDeadPass.memFillAtCost,
      Lax3Proofs.Refine.CoverActiveStreamBatch.streamChildGameCost]
    ring
  rw [heq, streamPlayCoeff]
  exact nat_affine_le_unit 254
    (Lax3Proofs.Refine.CoverActiveStreamPlay.streamPlayCost 0 0 cap j) z

theorem streamEnumColourCost_le_coeff (cap mb j z : ℕ) :
    Lax3Proofs.Refine.CoverActiveStreamColour.streamEnumColourCost
        z z cap mb (sigL cap mb j) ≤ streamEnumColourCoeff cap mb j * (z + 1) := by
  have heq :
      Lax3Proofs.Refine.CoverActiveStreamColour.streamEnumColourCost
          z z cap mb (sigL cap mb j) =
        streamEnumColourSlope cap mb (sigL cap mb j) * z +
          Lax3Proofs.Refine.CoverActiveStreamColour.streamEnumColourCost
            0 0 cap mb (sigL cap mb j) := by
    simp only [streamEnumColourSlope,
      Lax3Proofs.Refine.CoverActiveStreamColour.streamEnumColourCost,
      Lax3Proofs.Refine.CoverActiveStreamEnum.enumStreamCost,
      Lax3Proofs.Refine.CoverActiveStreamColour.streamColourCost,
      Lax3Proofs.Refine.CoverActiveStreamColour.streamOldCost,
      Lax3Proofs.Refine.CoverActiveStreamColour.streamPdCost,
      Lax3Proofs.Refine.CoverActiveStreamColour.streamPdBodyCost,
      Lax3Proofs.Refine.CoverActiveStreamColour.streamPuCost,
      Lax3Proofs.Refine.CoverActiveStreamColour.streamPuBodyCost,
      Lax3Proofs.Refine.CoverActiveStreamColour.streamExpandCost,
      Lax3Proofs.Refine.CoverActiveStreamMask.streamBlockAndCost,
      Lax3Proofs.Refine.CoverActiveStreamMask.streamBlockClearCost]
    ring
  rw [heq, streamEnumColourCoeff]
  exact nat_affine_le_unit (streamEnumColourSlope cap mb (sigL cap mb j))
    (Lax3Proofs.Refine.CoverActiveStreamColour.streamEnumColourCost
      0 0 cap mb (sigL cap mb j)) z

theorem streamPrepareCost_le_coeff (q_top cap mb j z : ℕ)
    (φ : Lax3.FirstOrder.FO 0) :
    Lax3Proofs.Refine.CoverActiveStreamPrepare.streamPrepareCost
        q_top cap mb j z z z φ ≤ streamPrepareCoeff q_top cap mb j φ * (z + 1) := by
  have hp := streamPlayCost_le_coeff cap j z
  have hc := streamEnumColourCost_le_coeff cap mb j z
  have hk : Lax3Proofs.Refine.CoverActiveStreamKill.streamKillListCost
        q_top cap mb j φ ≤
      Lax3Proofs.Refine.CoverActiveStreamKill.streamKillListCost
        q_top cap mb j φ * (z + 1) := by
    nlinarith [Nat.zero_le z,
      Nat.zero_le (Lax3Proofs.Refine.CoverActiveStreamKill.streamKillListCost
        q_top cap mb j φ)]
  simp only [Lax3Proofs.Refine.CoverActiveStreamPrepare.streamPrepareCost,
    streamPrepareCoeff]
  calc
    Lax3Proofs.Refine.CoverActiveStreamPlay.streamPlayCost z z cap j +
        (Lax3Proofs.Refine.CoverActiveStreamColour.streamEnumColourCost
          z z cap mb (sigL cap mb j) +
          Lax3Proofs.Refine.CoverActiveStreamKill.streamKillListCost q_top cap mb j φ)
      ≤ streamPlayCoeff cap j * (z + 1) +
          (streamEnumColourCoeff cap mb j * (z + 1) +
            Lax3Proofs.Refine.CoverActiveStreamKill.streamKillListCost
              q_top cap mb j φ * (z + 1)) :=
        Nat.add_le_add hp (Nat.add_le_add hc hk)
    _ = (streamPlayCoeff cap j + streamEnumColourCoeff cap mb j +
          Lax3Proofs.Refine.CoverActiveStreamKill.streamKillListCost q_top cap mb j φ) *
        (z + 1) := by ring

/-- Unit-block coefficient for recursion, scatter, and readback, excluding
the recursive charge itself. -/
noncomputable def streamFinishCoeff (q_top cap mb ell j : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  Lax3Proofs.Refine.CoverActiveStreamCentre.streamCentreFinishCost
    q_top cap mb j 1 0 (2 * streamScatterCoeff q_top cap mb ell φ) φ

theorem streamFinishCost_le_coeff
    (q_top cap mb ell j z Kin Kscatter : ℕ)
    (φ : Lax3.FirstOrder.FO 0)
    (hscatter : Kscatter ≤ streamScatterCoeff q_top cap mb ell φ * (z + 1)) :
    Lax3Proofs.Refine.CoverActiveStreamCentre.streamCentreFinishCost
        q_top cap mb j z Kin Kscatter φ ≤
      streamFinishCoeff q_top cap mb ell j φ * (z + 1) + Kin := by
  simp only [streamFinishCoeff,
    Lax3Proofs.Refine.CoverActiveStreamCentre.streamCentreFinishCost,
    Lax3Proofs.RamDriverBase.rbCost]
  nlinarith [Nat.zero_le z, Nat.zero_le Kin,
    Nat.zero_le (streamScatterCoeff q_top cap mb ell φ),
    Nat.zero_le (Lax3Proofs.RamDriverBase.blockCost q_top cap mb φ j 0
      (tablesAt q_top cap mb φ j))]

def streamReleaseCoeff (cap mb j : ℕ) : ℕ :=
  Lax3Proofs.Refine.CoverActiveStreamRelease.streamReleaseCost 1
      (sigL cap mb (j + 1)) + 4

theorem streamReleaseCost_le_coeff (cap mb j z : ℕ) :
    Lax3Proofs.Refine.CoverActiveStreamRelease.streamReleaseCost z
        (sigL cap mb (j + 1)) + 4 ≤ streamReleaseCoeff cap mb j * (z + 1) := by
  simp only [streamReleaseCoeff,
    Lax3Proofs.Refine.CoverActiveStreamRelease.streamReleaseCost,
    Lax3Proofs.Refine.CoverActiveStreamMask.streamBlockClearCost,
    Lax3Proofs.Refine.CoverActiveStreamColour.streamPaletteClearCost]
  nlinarith [Nat.zero_le z, Nat.zero_le (sigL cap mb (j + 1))]

/-- Formula-dependent affine coefficient of a complete non-recursive
centre lifecycle. -/
noncomputable def streamLifecycleCoeff (q_top cap mb ell j : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  streamPrepareCoeff q_top cap mb j φ +
    streamFinishCoeff q_top cap mb ell j φ + streamReleaseCoeff cap mb j

theorem streamCentreLifecycleCost_le_coeff
    (q_top cap mb ell j z Kin Kscatter : ℕ)
    (φ : Lax3.FirstOrder.FO 0)
    (hscatter : Kscatter ≤ streamScatterCoeff q_top cap mb ell φ * (z + 1)) :
    streamCentreLifecycleCost q_top cap mb j z z z Kin Kscatter φ ≤
      streamLifecycleCoeff q_top cap mb ell j φ * (z + 1) + Kin := by
  have hp := streamPrepareCost_le_coeff q_top cap mb j z φ
  have hf := streamFinishCost_le_coeff q_top cap mb ell j z Kin Kscatter φ hscatter
  have hr := streamReleaseCost_le_coeff cap mb j z
  simp only [streamCentreLifecycleCost,
    Lax3Proofs.Refine.CoverActiveStreamCentre.streamCentreCost,
    streamLifecycleCoeff]
  calc
    Lax3Proofs.Refine.CoverActiveStreamPrepare.streamPrepareCost
          q_top cap mb j z z z φ +
        Lax3Proofs.Refine.CoverActiveStreamCentre.streamCentreFinishCost
          q_top cap mb j z Kin Kscatter φ +
        (Lax3Proofs.Refine.CoverActiveStreamRelease.streamReleaseCost z
          (sigL cap mb (j + 1)) + 4)
      ≤ streamPrepareCoeff q_top cap mb j φ * (z + 1) +
          (streamFinishCoeff q_top cap mb ell j φ * (z + 1) + Kin) +
          streamReleaseCoeff cap mb j * (z + 1) :=
        Nat.add_le_add (Nat.add_le_add hp hf) hr
    _ = (streamPrepareCoeff q_top cap mb j φ +
          streamFinishCoeff q_top cap mb ell j φ + streamReleaseCoeff cap mb j) *
          (z + 1) + Kin := by ring

/-! ## The sigma witness -/

/-- The per-level non-recursive coefficient: search/sort plus one complete
streamed centre lifecycle. -/
noncomputable def streamTurnCoeff (n q_top cap mb ell j : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  streamSearchCoeff (Nat.clog 2 n) + streamLifecycleCoeff q_top cap mb ell j φ

/-- The canonical recurrence specialized to the concrete streamed costs. -/
theorem exists_streamDriverCosts
    (n q_top cap mb ell Kmass d D₁ R : ℕ)
    (φ : Lax3.FirstOrder.FO 0) :
    ∃ Ks Kl : ℕ → ℕ → ℕ,
      (∀ j, Monotone (Kl j)) ∧
      (∀ j < ell, ∀ z,
        streamCentreLifecycleCost q_top cap mb j z z z (Kl (j + 1) z)
            (streamKsc q_top cap mb ell φ j z) φ ≤ Ks j z) ∧
      (∀ m, Lax3Proofs.RamDriverBot.baseCost q_top cap mb ell m φ ≤ Kl ell m) ∧
      (∀ j < ell, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
        (∑ k ∈ range t, bs k) ≤ Kmass * (m + 1) →
        activeOrderCost d D₁ R m +
            (Lax3Proofs.Refine.CoverActiveInit.activeInitCost t +
              ((∑ k ∈ range t,
                (streamSearchSortCost (Nat.clog 2 n) (bs k) (bs k) +
                  Ks j (bs k) + 4)) + 6)) ≤ Kl j m) ∧
      (∀ m, Kl 0 m =
        ((∑ j ∈ range ell,
            Lax3Proofs.CostRecurrence.driverASigma
              (fun _ => activeOrderCostCoeff d D₁ R) (fun _ => 42)
              (fun j => streamTurnCoeff n q_top cap mb ell j φ) Kmass j *
                (Kmass + 1) ^ j) +
          Lax3Proofs.Refine.G2CostProbe.sweepCoeffA q_top cap mb ell φ *
            (Kmass + 1) ^ ell) * (m + 1)) := by
  classical
  let Cb := Lax3Proofs.Refine.G2CostProbe.sweepCoeffA q_top cap mb ell φ
  obtain ⟨Kl, Kt, hbase, hmono, hKt, hlevel, hroot, -⟩ :=
    Lax3Proofs.CostRecurrence.exists_driverCostsSigma ell Kmass Cb
      (fun _ => activeOrderCostCoeff d D₁ R) (fun _ => 42)
      (fun j => streamTurnCoeff n q_top cap mb ell j φ)
      (fun _ m => activeOrderCost d D₁ R m)
      (fun _ m => Lax3Proofs.Refine.CoverActiveInit.activeInitCost m)
      (fun j z => streamTurnCoeff n q_top cap mb ell j φ * (z + 1))
      (fun j z Kin =>
        streamSearchSortCost (Nat.clog 2 n) z z +
          (streamLifecycleCoeff q_top cap mb ell j φ * (z + 1) + Kin))
      (fun _ _ => le_rfl)
      (fun _ m => by
        dsimp
        rw [Lax3Proofs.Refine.CoverActiveBudget.activeInitCost_eq]
        nlinarith)
      (fun _ _ => le_rfl)
      (fun j z Kin => by
        have hs := streamSearchSortCost_le_coeff (Nat.clog 2 n) z
        calc
          streamSearchSortCost (Nat.clog 2 n) z z +
                (streamLifecycleCoeff q_top cap mb ell j φ * (z + 1) + Kin)
              ≤ streamSearchCoeff (Nat.clog 2 n) * (z + 1) +
                (streamLifecycleCoeff q_top cap mb ell j φ * (z + 1) + Kin) :=
            Nat.add_le_add_right hs _
          _ = streamTurnCoeff n q_top cap mb ell j φ * (z + 1) + Kin := by
            simp only [streamTurnCoeff]
            ring)
  let Ks : ℕ → ℕ → ℕ := fun j z =>
    streamLifecycleCoeff q_top cap mb ell j φ * (z + 1) + Kl (j + 1) z
  refine ⟨Ks, Kl, hmono, ?_, ?_, ?_, ?_⟩
  · intro j hj z
    exact streamCentreLifecycleCost_le_coeff q_top cap mb ell j z
      (Kl (j + 1) z) (streamKsc q_top cap mb ell φ j z) φ
      (streamKsc_le_coeff q_top cap mb ell φ j z)
  · intro m
    exact (Lax3Proofs.Refine.G2CostProbe.hKbase_paid q_top cap mb ell m φ).trans
      (hbase m)
  · intro j hj m t htm bs hmass
    have hinit : Lax3Proofs.Refine.CoverActiveInit.activeInitCost t ≤
        Lax3Proofs.Refine.CoverActiveInit.activeInitCost m := by
      rw [Lax3Proofs.Refine.CoverActiveBudget.activeInitCost_eq,
        Lax3Proofs.Refine.CoverActiveBudget.activeInitCost_eq]
      omega
    have hterm : ∀ k ∈ range t,
        streamSearchSortCost (Nat.clog 2 n) (bs k) (bs k) + Ks j (bs k) + 4 ≤
          Kt j (bs k) + 8 := by
      intro k hk
      have hk' := hKt j (bs k)
      simp only [Ks] at hk' ⊢
      omega
    exact le_trans
      (Nat.add_le_add le_rfl (Nat.add_le_add hinit
        (Nat.add_le_add (Finset.sum_le_sum hterm) le_rfl)))
      (hlevel j hj m t htm bs hmass)
  · intro m
    simpa [Cb] using hroot m

/-! ## Concrete root plug -/

open Lax3.Locality Lax3.ScatterSentences Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning

open Classical in
/-- All streamed execution costs of the concrete root are discharged here.
The remaining hypotheses are graph-parameter producers, word bounds, and the
two finite root I/O charges. -/
theorem stream_root_cost_plug
    {n : ℕ} {B q_top cap mb ns W ell s R d D₁ Kmass : ℕ}
    {N : ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {Katom₀ Kdec Ksent : ℕ}
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hxB : ∀ v ∈ x, v < B)
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top)
    (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ell * (2 * cap + 1)) (hell : ell = N (2 * s + 2))
    (hB : WordBoundK B n 1 ns cap mb) (hWB : W < B) (hnsW : ns ≤ W)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧
        2 * s + 2 ≤ Bd.ncard ∧
          DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hlimits : ∀ j < ell, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ sa ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        sa.r + 1 < B ∧ sa.t + n + mb < B)
    (hwidthB : n + activeOrderWidth d D₁ R (n + ns) + 1 < B)
    (hwidthW : activeOrderWidth d D₁ R (n + ns) ≤ W)
    (hdeg : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M)),
      Lax3Proofs.Augmentation.LowDegreeVertices
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) d)
    (hdens : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M))
        (A : ℕ → Lax3Proofs.Augmentation.Orientation mm) (i : ℕ), i ≤ R →
      Lax3Proofs.Augmentation.IsAugChain
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) A i →
      (∀ l < i, Lax3Proofs.Augmentation.GreedyFratRound (A l) (A (l + 1))) →
      Lax3Proofs.Augmentation.AugmentedDepthOneDensity A i D₁)
    (hKmass : 1 ≤ Kmass)
    (hdegree : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M))
        {A : ℕ → Lax3Proofs.Augmentation.Orientation mm}
        {d₀ k : ℕ} {pi : Equiv.Perm (Fin mm)},
      Lax3Proofs.CoverDegree.AugChainData
          (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) A pi R d₀ k →
        ∀ v : Fin mm,
          (Lax12.ColoringNumbers.wreach
            (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) pi
              (2 * cap) v).ncard ≤ Kmass)
    (hKdec : Lax3Proofs.RamDriverIO.decodeCost n ns +
      Lax3Proofs.RamDriverDedup.dedupCost n ns + 4 ≤ Kdec)
    (hatoms : ∀ sa ∈
      (bcAtomsOf₀ q_top (Lax3Proofs.Reduction.toDistFO
        (L := sigL cap mb 0) φ)).2,
      sa.r + 1 < B ∧ sa.t < B ∧
        Lax3Proofs.RamDriverIO.atomCost n
          (Lax3Proofs.RamDriverDedup.dedupNs x) sa.t ≤ Katom₀)
    (hKsent : Katom₀ *
        (bcAtomsOf₀ q_top (Lax3Proofs.Reduction.toDistFO
          (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (Lax3Proofs.RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent) :
    ∃ Kl : ℕ → ℕ → ℕ,
      (∀ j, Monotone (Kl j)) ∧
      (∀ m, Kl 0 m =
        ((∑ j ∈ range ell,
            Lax3Proofs.CostRecurrence.driverASigma
              (fun _ => activeOrderCostCoeff d D₁ R) (fun _ => 42)
              (fun j => streamTurnCoeff n q_top cap mb ell j φ) Kmass j *
                (Kmass + 1) ^ j) +
          Lax3Proofs.Refine.G2CostProbe.sweepCoeffA q_top cap mb ell φ *
            (Kmass + 1) ^ ell) * (m + 1)) ∧
      Spec B (StreamRootPreD B n ns W q_top cap mb ell φ x)
        (driverRootStream q_top cap mb R ell φ)
        (fun _ σ' => σ'.out =
          [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
        (Kdec + (Lax3Proofs.Refine.CoverActiveRadixWidth.radixWidthCost n +
          (Kl 0 (n + Lax3Proofs.RamDriverDedup.dedupNs x) + Ksent))) := by
  obtain ⟨Ks, Kl, hmono, hlife, hbase, hlevel, hclosed⟩ :=
    exists_streamDriverCosts n q_top cap mb ell Kmass d D₁ R φ
  refine ⟨Kl, hmono, hclosed, ?_⟩
  apply driverRootStream_decides_sentence hx hns hxB hrank hcap hmb hell hB hWB hnsW hQ
    (Katom := streamKatom q_top cap mb ell φ)
    (Ki := streamKi q_top cap mb ell φ)
    (Ksc := streamKsc q_top cap mb ell φ)
    (Ks := Ks) (Kl := Kl)
  · intro j hj β hβ sa hsa
    obtain ⟨hr, ht⟩ := hlimits j hj β hβ sa hsa
    refine ⟨hr, ht, ?_⟩
    intro a z ha
    exact (deadAtomKX_le_streamDeadAtomCoeff sa.β n a mb z sa.t ha).trans
      (Nat.mul_le_mul_right (z + 1)
        (streamDeadAtomCoeff_le_global hj hβ hsa))
  · intro j hj β hβ z
    simp only [streamKi]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left (streamKatom q_top cap mb ell φ z)
        (atom_length_le_streamAtomCount hj hβ)) 1
  · intro j hj z
    simp only [streamKsc]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left (streamKi q_top cap mb ell φ 0 z)
        (table_length_le_streamTableCount hj)) 1
  · exact hmono
  · exact hlife
  · exact hbase
  · exact hwidthB
  · exact hwidthW
  · exact hdeg
  · exact hdens
  · exact hKmass
  · exact hdegree
  · exact hlevel
  · exact hKdec
  · exact hatoms
  · exact hKsent

/-! ## Axiom audit -/

#print axioms deadAtomKX_le_streamDeadAtomCoeff
#print axioms exists_streamDriverCosts
#print axioms stream_root_cost_plug

end Lax3Proofs.Refine.CoverActiveStreamCost
