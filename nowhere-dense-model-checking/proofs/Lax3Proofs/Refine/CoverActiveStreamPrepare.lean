import Lax3Proofs.Refine.CoverActiveStreamKill
import Lax3Proofs.Refine.CoverActiveStreamDepth
import Lax3Proofs.Refine.CoverActiveStreamInner

/-!
# Preparing one streamed centre for its recursive call

This module composes the row-local descent, sparse colouring, and kill walks.
It stops at the physical depth-owned interface consumed by
`CoverActiveStreamCentre`.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamPrepare

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamCover Lax3Proofs.RamCoverActive
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBase
open Lax3Proofs.RamDriverBot
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.CoverActiveStreamLoad
open Lax3Proofs.Refine.CoverActiveStreamMask
open Lax3Proofs.Refine.CoverActiveStreamBatch
open Lax3Proofs.Refine.CoverActiveStreamChild
open Lax3Proofs.Refine.CoverActiveStreamEnum
open Lax3Proofs.Refine.CoverActiveStreamPlay
open Lax3Proofs.Refine.CoverActiveStreamColour
open Lax3Proofs.Refine.CoverActiveStreamKill
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.CoverActiveStreamInner
open Lax3Proofs.Refine.CoverActiveStreamScratch
open Lax3Proofs.Refine.CoverActiveBudget
open Lax3Proofs.Refine.KillPass
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {n : ℕ}

noncomputable def streamPrepareCom
    (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) : Com :=
  .seq (streamPlayCom cap j)
    (.seq (streamEnumColourCom cap mb j)
      (streamKillListCom q_top cap mb j φ))

noncomputable def streamPrepareCost
    (q_top cap mb j tail rowMass bw : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  streamPlayCost tail bw cap j +
    (streamEnumColourCost tail rowMass cap mb (sigL cap mb j) +
      streamKillListCost q_top cap mb j φ)

/-! ## Frames of the new preparation program -/

theorem notMem_warrs_streamPlayCom {cap j : ℕ} {a : String}
    (hclu : a ≠ cluName j) (hmem : a ≠ memName (j + 1))
    (hres : a ≠ resName j) (hba : a ≠ balAltName j)
    (hbl : a ≠ balName j) (hq : a ≠ "q") (hqd : a ≠ "qd")
    (hbat : a ≠ batName j) (halv : a ≠ alvName (j + 1))
    (hgam : a ≠ gamName (j + 1)) :
    a ∉ (streamPlayCom cap j).warrs := by
  intro h
  simp only [streamPlayCom, streamConnectorCom, streamRestoreTailCom,
    Com.warrs, List.mem_append, List.not_mem_nil, false_or] at h
  rcases h with h | h | h | h | h
  · simpa [streamClusterLoadCom, streamLoadSlot, Com.warrs, hclu, hmem] using h
  · simpa [streamRetainCom, streamBlockAndCom, streamBlockMapCom,
      Lax3Proofs.Refine.BlockLeaves.blockMapRangeCom, Com.warrs, hres] using h
  · rcases mem_warrs_cacheRoundCom h with h | h | h | h
    exacts [hba h, hbl h, hq h, hqd h]
  · exact streamBatch_frame_arr hbat h
  · simpa [streamChildFilterCom, streamChildGameCom, streamBlockSubCom,
      streamBlockAndSubCom, streamBlockMapCom,
      Lax3Proofs.Refine.BlockLeaves.blockMapRangeCom, Com.warrs,
      Lax3Proofs.RamDriverFrames.warrs_memFilterCom, halv, hgam, hmem] using h

theorem notMem_wvars_streamPlayCom {cap j : ℕ} {y : String}
    (hctr : y ≠ ctrName j) (hmm : y ≠ mnumName (j + 1))
    (hcw : y ≠ "cw") (hs : y ∉ descendScalars) :
    y ∉ (streamPlayCom cap j).wvars := by
  intro h
  simp only [streamPlayCom, streamConnectorCom, streamRestoreTailCom,
    Com.wvars, List.mem_append] at h
  rcases h with h | h | h | h | h | h | h
  · simpa [Com.wvars, hctr] using h
  · apply hs
    simp [streamClusterLoadCom, streamLoadSlot, Com.wvars] at h
    rcases h with rfl | rfl <;> decide
  · simp [streamRetainCom, streamBlockAndCom, streamBlockMapCom,
      Lax3Proofs.Refine.BlockLeaves.blockMapRangeCom, Com.wvars] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact hs (by decide)
    · exact hs (by decide)
    · exact hcw rfl
    · exact hs (by decide)
  · rcases mem_wvars_cacheRoundCom h with h | h
    · exact hmm h
    · exact hs h
  · exact hs (streamBatch_wvars h)
  · apply hs
    simp [Com.wvars] at h
    subst y
    decide
  · have hp : y ≠ "p" := fun he => hs (he.symm ▸ (by decide))
    have hpend : y ≠ "pend" := fun he => hs (he.symm ▸ (by decide))
    have hmk : y ≠ "mk" := fun he => hs (he.symm ▸ (by decide))
    have hmv : y ≠ "mv" := fun he => hs (he.symm ▸ (by decide))
    simpa [streamChildFilterCom, streamChildGameCom, streamBlockSubCom,
      streamBlockAndSubCom, streamBlockMapCom,
      Lax3Proofs.Refine.BlockLeaves.blockMapRangeCom, Com.wvars,
      Lax3Proofs.RamDriverFrames.wvars_memFilterCom,
      hp, hpend, hcw, hmk, hmm, hmv] using h

theorem levelPre_run_streamPlayCom
    {B cap mb ns nt j K : ℕ} {O T A₀ Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B (streamPlayCom cap j) σ σ' K) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  have hfa (a : String)
      (hclu : a ≠ cluName j) (hmem : a ≠ memName (j + 1))
      (hres : a ≠ resName j) (hba : a ≠ balAltName j)
      (hbl : a ≠ balName j) (hq : a ≠ "q") (hqd : a ≠ "qd")
      (hbat : a ≠ batName j) (halv : a ≠ alvName (j + 1))
      (hgam : a ≠ gamName (j + 1)) :
      a ∉ (streamPlayCom cap j).warrs :=
    notMem_warrs_streamPlayCom (cap := cap) hclu hmem hres hba hbl hq hqd
      hbat halv hgam
  have hfv (y : String) (hctr : y ≠ ctrName j)
      (hmm : y ≠ mnumName (j + 1)) (hcw : y ≠ "cw")
      (hs : y ∉ descendScalars) : y ∉ (streamPlayCom cap j).wvars :=
    notMem_wvars_streamPlayCom (cap := cap) hctr hmm hcw hs
  apply Lax3Proofs.RamDriverCompose.levelPre_run hp hr
  · exact hfv "n" (by simp [ctrName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by decide) (by decide)
  · exact hfv "m" (by simp [ctrName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by decide) (by decide)
  · exact hfv "lw" (by simp [ctrName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by decide) (by decide)
  · exact hfa "off" (by simp [cluName, String.ext_iff])
      (by simp [memName, String.ext_iff]) (by simp [resName, String.ext_iff])
      (by simp [balAltName, String.ext_iff]) (by simp [balName, String.ext_iff])
      (by decide) (by decide) (by simp [batName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
  · exact hfa "tgt" (by simp [cluName, String.ext_iff])
      (by simp [memName, String.ext_iff]) (by simp [resName, String.ext_iff])
      (by simp [balAltName, String.ext_iff]) (by simp [balName, String.ext_iff])
      (by decide) (by decide) (by simp [batName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
  · exact hfa _ (by simp [alvName, cluName, String.ext_iff])
      (by simp [alvName, memName, String.ext_iff])
      (by simp [alvName, resName, String.ext_iff])
      (by simp [alvName, balAltName, String.ext_iff])
      (by simp [alvName, balName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [alvName, String.ext_iff])
      (by simp [alvName, batName, String.ext_iff])
      (alvName_ne_succ j) (by simp [alvName, gamName, String.ext_iff])
  · exact hfa _ (by simp [gamName, cluName, String.ext_iff])
      (by simp [gamName, memName, String.ext_iff])
      (by simp [gamName, resName, String.ext_iff])
      (by simp [gamName, balAltName, String.ext_iff])
      (by simp [gamName, balName, String.ext_iff])
      (by simp [gamName, String.ext_iff]) (by simp [gamName, String.ext_iff])
      (by simp [gamName, batName, String.ext_iff])
      (by simp [gamName, alvName, String.ext_iff])
      (gamName_ne_succ (le_refl j))
  · intro s
    exact hfa _ (by simp [colName, cluName, String.ext_iff])
      (by simp [colName, memName, String.ext_iff])
      (by simp [colName, resName, String.ext_iff])
      (by simp [colName, balAltName, String.ext_iff])
      (by simp [colName, balName, String.ext_iff])
      (by simp [colName, String.ext_iff]) (by simp [colName, String.ext_iff])
      (by simp [colName, batName, String.ext_iff])
      (by simp [colName, alvName, String.ext_iff])
      (by simp [colName, gamName, String.ext_iff])
  · intro a ha
    simp only [Lax3Proofs.RamDriverCompose.zeroArrs, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfa _ (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff]) (by simp [resName, String.ext_iff])
        (by simp [balAltName, String.ext_iff]) (by simp [balName, String.ext_iff])
        (by decide) (by decide) (by simp [batName, String.ext_iff])
        (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
  · exact hfa _ (by simp [memName, cluName, String.ext_iff])
      (memName_ne_succ j)
      (by simp [memName, resName, String.ext_iff])
      (by simp [memName, balAltName, String.ext_iff])
      (by simp [memName, balName, String.ext_iff])
      (by simp [memName, String.ext_iff]) (by simp [memName, String.ext_iff])
      (by simp [memName, batName, String.ext_iff])
      (by simp [memName, alvName, String.ext_iff])
      (by simp [memName, gamName, String.ext_iff])
  · exact hfv _ (by simp [mnumName, ctrName, String.ext_iff])
      (mnumName_ne_succ j)
      (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, descendScalars, String.ext_iff])

theorem notMem_warrs_streamEnumColourCom
    {cap mb j : ℕ} {a : String}
    (hwa : a ≠ "wa")
    (hcol : ∀ s, s < sigL cap mb (j + 1) → a ≠ colName (j + 1) s) :
    a ∉ (streamEnumColourCom cap mb j).warrs := by
  intro h
  simp only [streamEnumColourCom, Com.warrs, List.mem_append] at h
  rcases h with h | h
  · exact not_mem_warrs_enumStreamCom hwa h
  · obtain ⟨s, hs, he⟩ := mem_warrs_streamColourCom h
    exact hcol s hs he

theorem notMem_wvars_streamEnumColourCom
    {cap mb j : ℕ} {y : String}
    (hbc : y ≠ "bc") (hp : y ≠ "p") (hpend : y ≠ "pend")
    (hz : y ≠ "z") (hk : y ≠ "k")
    (hcolour : y ∉ (["p", "pend", "cw", "z", "hit", "w", "j", "jend"] :
      List String)) :
    y ∉ (streamEnumColourCom cap mb j).wvars := by
  intro h
  simp only [streamEnumColourCom, Com.wvars, List.mem_append] at h
  rcases h with h | h
  · exact not_mem_wvars_enumStreamCom hbc hp hpend hz hk h
  · exact hcolour (mem_wvars_streamColourCom h)

theorem levelPre_run_streamEnumColourCom
    {B cap mb ns nt j K : ℕ} {O T A₀ Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B (streamEnumColourCom cap mb j) σ σ' K) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  have hfa (a : String) (hwa : a ≠ "wa")
      (hcol : ∀ s, s < sigL cap mb (j + 1) → a ≠ colName (j + 1) s) :
      a ∉ (streamEnumColourCom cap mb j).warrs :=
    notMem_warrs_streamEnumColourCom hwa hcol
  have hfv (y : String) (hbc : y ≠ "bc") (hp : y ≠ "p")
      (hpend : y ≠ "pend") (hz : y ≠ "z") (hk : y ≠ "k")
      (hc : y ∉ (["p", "pend", "cw", "z", "hit", "w", "j", "jend"] :
        List String)) : y ∉ (streamEnumColourCom cap mb j).wvars :=
    notMem_wvars_streamEnumColourCom hbc hp hpend hz hk hc
  apply Lax3Proofs.RamDriverCompose.levelPre_run hp hr
  · exact hfv "n" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hfv "m" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hfv "lw" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hfa "off" (by decide)
      (fun s _ => by simp [colName, String.ext_iff])
  · exact hfa "tgt" (by decide)
      (fun s _ => by simp [colName, String.ext_iff])
  · exact hfa _ (by simp [alvName, String.ext_iff])
      (fun s _ => by simp [alvName, colName, String.ext_iff])
  · exact hfa _ (by simp [gamName, String.ext_iff])
      (fun s _ => by simp [gamName, colName, String.ext_iff])
  · intro c
    exact hfa _ (by simp [colName, String.ext_iff]) (fun s _ he => by
      have := (colName_inj he).1
      omega)
  · intro a ha
    simp only [Lax3Proofs.RamDriverCompose.zeroArrs, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfa _ (by decide) (fun s _ => by simp [colName, String.ext_iff])
  · exact hfa _ (by simp [memName, String.ext_iff])
      (fun s _ => by simp [memName, colName, String.ext_iff])
  · exact hfv _ (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff])

theorem notMem_warrs_streamKillListCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {a : String}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β)
    (htab : ∀ i, a ≠ tabName (j + 1) i)
    (hext : ¬ Lax3Proofs.RamDriverBot.Ext "bb" a)
    (hkl : a ≠ klName j) :
    a ∉ (streamKillListCom q_top cap mb j φ).warrs := by
  intro h
  simp only [streamKillListCom, Com.warrs, List.mem_append] at h
  rcases h with h | h
  · exact notMem_warrs_killCom hlocal htab hext h
  · exact RamDriverWrites.notMem_warrs_killListCom hkl h

theorem notMem_wvars_streamKillListCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {y : String}
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β)
    (hkk : y ≠ "kk") (hkv : y ≠ "kv")
    (henv : ∀ i, y ≠ envName i)
    (hext : ¬ Lax3Proofs.RamDriverBot.Ext "bb" y)
    (hkkj : y ≠ kkName j) (hkf : y ≠ "kf") (hkt : y ≠ "kt") :
    y ∉ (streamKillListCom q_top cap mb j φ).wvars := by
  intro h
  simp only [streamKillListCom, Com.wvars, List.mem_append] at h
  rcases h with h | h
  · exact notMem_wvars_killCom hlocal hkk hkv henv hext h
  · exact RamDriverWrites.notMem_wvars_killListCom hkkj hkk hkv hkf hkt h

theorem belowArr_notMem_warrs_streamKillListCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamKillListCom q_top cap mb j phi).warrs := by
  intro hm
  simp only [streamKillListCom, Com.warrs, List.mem_append] at hm
  rcases hm with hm | hm
  · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_killCom
      q_top cap mb j phi h hm
  · exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_killListCom
      mb j h hm

theorem belowVar_notMem_wvars_streamKillListCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {y : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamKillListCom q_top cap mb j phi).wvars := by
  intro hm
  simp only [streamKillListCom, Com.wvars, List.mem_append] at hm
  rcases hm with hm | hm
  · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_killCom
      q_top cap mb j phi h hm
  · exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_killListCom
      mb j h hm

theorem levelPre_run_streamKillListCom
    {B q_top cap mb ns nt j K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {O T A₀ Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B (streamKillListCom q_top cap mb j φ) σ σ' K) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1
  have hfa (a : String) (htab : ∀ i, a ≠ tabName (j + 1) i)
      (hext : ¬ Lax3Proofs.RamDriverBot.Ext "bb" a) (hkl : a ≠ klName j) :
      a ∉ (streamKillListCom q_top cap mb j φ).warrs :=
    notMem_warrs_streamKillListCom hlocal htab hext hkl
  have hfv (y : String) (hkk : y ≠ "kk") (hkv : y ≠ "kv")
      (henv : ∀ i, y ≠ envName i)
      (hext : ¬ Lax3Proofs.RamDriverBot.Ext "bb" y)
      (hkkj : y ≠ kkName j) (hkf : y ≠ "kf") (hkt : y ≠ "kt") :
      y ∉ (streamKillListCom q_top cap mb j φ).wvars :=
    notMem_wvars_streamKillListCom hlocal hkk hkv henv hext hkkj hkf hkt
  have hnev : ∀ (p : String) (ch : Char), (∃ t, p.toList = ch :: t) → ch ≠ 'e' →
      ∀ i, p ≠ envName i :=
    fun p ch hhead hch i => ne_of_head_ne hhead (head_envName i) hch
  apply Lax3Proofs.RamDriverCompose.levelPre_run hp hr
  · exact hfv "n" (by decide) (by decide)
      (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
      (not_ext_of_not_prefix (by decide))
      (by simp [kkName, String.ext_iff]) (by decide) (by decide)
  · exact hfv "m" (by decide) (by decide)
      (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
      (not_ext_of_not_prefix (by decide))
      (by simp [kkName, String.ext_iff]) (by decide) (by decide)
  · exact hfv "lw" (by decide) (by decide)
      (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
      (not_ext_of_not_prefix (by decide))
      (by simp [kkName, String.ext_iff]) (by decide) (by decide)
  · exact hfa "off"
      (fun i => RamDriverBase.lit_ne_tabName (by decide) (j + 1) i)
      (not_ext_of_not_prefix (by decide)) (by simp [klName, String.ext_iff])
  · exact hfa "tgt"
      (fun i => RamDriverBase.lit_ne_tabName (by decide) (j + 1) i)
      (not_ext_of_not_prefix (by decide)) (by simp [klName, String.ext_iff])
  · exact hfa _ (fun i => alvName_ne_tabName j (j + 1) i)
      (fun h => not_ext_b_alvName j
        (Lax3Proofs.RamDriverCompose.ext_b_of_ext_bb h))
      (by simp [alvName, klName, String.ext_iff])
  · exact hfa _ (fun i => gamName_ne_tabName j (j + 1) i)
      (fun h => not_ext_b_gamName j
        (Lax3Proofs.RamDriverCompose.ext_b_of_ext_bb h))
      (by simp [gamName, klName, String.ext_iff])
  · intro c
    exact hfa _ (fun i => colName_ne_tabName j c (j + 1) i)
      (fun h => not_ext_b_colName j c
        (Lax3Proofs.RamDriverCompose.ext_b_of_ext_bb h))
      (by simp [colName, klName, String.ext_iff])
  · intro a ha
    simp only [Lax3Proofs.RamDriverCompose.zeroArrs, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfa _
        (fun i => RamDriverBase.lit_ne_tabName (by decide) (j + 1) i)
        (not_ext_of_not_prefix (by decide)) (by simp [klName, String.ext_iff])
  · exact hfa _
      (fun i => ne_of_head_ne (Lax3Proofs.RamDriverCompose.head_memName j)
        (head_tabName (j + 1) i) (by decide))
      (Lax3Proofs.RamDriverCompose.not_ext_bb_memName j)
      (by simp [memName, klName, String.ext_iff])
  · exact hfv _ (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff])
      (hnev _ 'm' ⟨_, by rw [mnumName, String.toList_append]; rfl⟩ (by decide))
      (Lax3Proofs.RamDriverCompose.not_ext_bb_mnumName j)
      (by simp [mnumName, kkName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])

/-! ## The complete pre-recursive preparation -/

theorem noWrite_streamBatchCachedCom (cap j : ℕ) :
    (streamBatchCachedCom cap j).NoWrite := by
  have hmark : ∀ a, (streamMarkParentsCom cap j a).NoWrite := by
    intro a
    simp [streamMarkParentsCom, streamMarkParentStep, Com.NoWrite]
  exact ⟨trivial,
    Lax3Proofs.RamDriverBot.noWrite_foldRange _ hmark j⟩

theorem noWrite_streamChildFilterCom (j : ℕ) :
    (streamChildFilterCom j).NoWrite := by
  refine ⟨⟨noWrite_streamBlockMapCom _ _ _,
    noWrite_streamBlockAndSubCom _ _ _ _ _⟩,
    Lax3Proofs.RamDriverDescend.noWrite_memFilterCom (j + 1)⟩

theorem noWrite_streamPlayCom (cap j : ℕ) :
    (streamPlayCom cap j).NoWrite := by
  exact ⟨trivial, noWrite_streamClusterLoadCom "xmem" j,
    noWrite_streamBlockMapCom _ _ _,
    Lax3Proofs.RamDriverDescend.noWrite_cacheRoundCom cap j,
    noWrite_streamBatchCachedCom cap j, trivial,
    noWrite_streamChildFilterCom j⟩

/-- State of one sorted streamed row before descent.  The zero clauses are
the reusable row-local buffers; all allocation-only premises needed by the
descent are already contained in the parent `LevelPre`. -/
structure StreamPreparePre {n : ℕ}
    (B q_top cap mb ns nt na q j c tail bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (σ : Env) : Prop where
  sorted : StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
    Xmem asg M σ
  level : LevelPre B n cap mb ns nt O T j A₀ Gm C σ
  play : PlayRec B cap G j A₀ Gm σ
  cluster_zero : σ.arrs (cluName j) = arrOf n (fun _ => 0)
  retained_zero : σ.arrs (resName j) = arrOf n (fun _ => 0)
  batch_zero : σ.arrs (batName j) = arrOf n (fun _ => 0)
  child_zero : σ.arrs (alvName (j + 1)) = arrOf n (fun _ => 0)
  game_zero : σ.arrs (gamName (j + 1)) = arrOf n (fun _ => 0)
  next_colours_zero : ∀ s, s < sigL cap mb (j + 1) →
    σ.arrs (colName (j + 1) s) = arrOf n (fun _ => 0)
  tables : TablesSized q_top cap mb φ n σ
  base_arrs : BaseArrs B q_top cap mb ell φ σ

open Classical in
/-- **A sorted streamed row reaches the physical-recursion payload.**
This is the complete load/cache/batch/child/enumerate/colour/kill chain.
Every executed row walk is charged to `tail`; the only graph-support charge
is the active cluster's CSR weight. -/
theorem streamPrepareStep
    {B n q_top cap mb ns nt na q j c tail bits ell d : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ}
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : Lax3Proofs.RamBfs.CsrGraph G ns O T) (hnt : ns ≤ nt)
    (hB : WordBoundK B n d ns cap mb)
    (hmb : mb = ell * (2 * cap + 1)) (hjl : j < ell) :
    Spec B
      (StreamPreparePre B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
        centre O T Xmem asg M Gm C)
      (streamPrepareCom q_top cap mb j φ)
      (fun σ σ' => ∃ (Xa Mm Ra Wa Alv Gam Mem : ℕ → ℕ) (mm : ℕ)
          (w : Fin mb → Fin n) (C' : ℕ → ℕ → ℕ),
        StreamKillOut B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
          centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ' ∧
        PlayRec B cap G j A₀ Gm σ' ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ' ∧
        TablesSized q_top cap mb φ n σ' ∧
        BaseArrs B q_top cap mb ell φ σ' ∧
        σ'.out = σ.out)
      (streamPrepareCost q_top cap mb j tail
        (expandRowSum O Xmem 0 tail)
        (activeBallWeight n G A₀ π centre O cap c) φ) := by
  refine Spec.of_exists fun σ hpre => ?_
  have hlevel₀ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ := hpre.level
  obtain ⟨hn, hoff, htgt, halv, hgam, hcol, hA₀B, hGmB, hCbit,
    hlevelMem, hdepthMem, hm, horderMem, hpad, htB, hmember⟩ := hlevel₀
  have hmemAlloc : ∃ g, σ.arrs (memName (j + 1)) = arrOf n g :=
    hdepthMem.get (j + 1) (p := (memName (j + 1), n)) (by simp)
  have hpdsAlloc : ∃ g, σ.arrs (pdsName j) = arrOf n g :=
    hdepthMem.get j (p := (pdsName j, n)) (by simp [pdsName])
  have hparjAlloc : ∃ g, σ.arrs (parName j) = arrOf n g :=
    hdepthMem.get j (p := (parName j, n)) (by simp [parName])
  have hparAlloc : ∃ g, σ.arrs "par" = arrOf n g :=
    hlevelMem.1 ("par", n) (by simp)
  have hpathAlloc : ∃ g, σ.arrs "path" = arrOf (2 * cap + 1) g :=
    hlevelMem.1 ("path", 2 * cap + 1) (by simp)
  have hwaAlloc : ∃ g, σ.arrs "wa" = arrOf mb g :=
    hlevelMem.1 ("wa", mb) (by simp)
  obtain ⟨σ₁, hr₁, ⟨Xa, Mm, Ra, Wa, Alv, Gam, Mem, mm, hplayed₁⟩,
      -, hfa₁, -, hout₁⟩ :=
    ((streamPlayStep hcentres hcsr hnt hB hmb hjl hA₀B hGmB).frame).run
      ⟨hpre.sorted, hpre.play, halv, hgam, hpre.cluster_zero,
        hpre.retained_zero, hpre.batch_zero, hpre.child_zero, hpre.game_zero,
        hmemAlloc, hpdsAlloc, hparjAlloc, hparAlloc, hpathAlloc, hwaAlloc⟩
  have hlevel₁ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₁ :=
    levelPre_run_streamPlayCom hpre.level hr₁
  have hnext₁ : ∀ s, s < sigL cap mb (j + 1) →
      σ₁.arrs (colName (j + 1) s) = arrOf n (fun _ => 0) := by
    intro s hs
    rw [hfa₁ _ (notMem_warrs_streamPlayCom
      (by simp [colName, cluName, String.ext_iff])
      (by simp [colName, memName, String.ext_iff])
      (by simp [colName, resName, String.ext_iff])
      (by simp [colName, balAltName, String.ext_iff])
      (by simp [colName, balName, String.ext_iff])
      (by simp [colName, String.ext_iff])
      (by simp [colName, String.ext_iff])
      (by simp [colName, batName, String.ext_iff])
      (by simp [colName, alvName, String.ext_iff])
      (by simp [colName, gamName, String.ext_iff]))]
    exact hpre.next_colours_zero s hs
  have hlevel₁keep := hlevel₁
  obtain ⟨-, -, -, -, -, hcol₁, -, -, hCbit₁, -, -, -, -, -, -, -⟩ := hlevel₁
  obtain ⟨σ₂, hr₂, hpost₂⟩ :=
    (streamEnumColourStep hcsr hnt hB hCbit₁).run
      ⟨hplayed₁, hcol₁, hnext₁⟩
  obtain ⟨w, C', hpost₂⟩ := hpost₂
  have hsorted₂ := hpost₂.1
  have hcluster₂ := hpost₂.2.1
  have hdata₂ := hpost₂.2.2.1
  have hwa₂ := hpost₂.2.2.2.1
  have hplay₂ := hpost₂.2.2.2.2.1
  have hparent₂ := hpost₂.2.2.2.2.2.1
  have hcolour₂ := hpost₂.2.2.2.2.2.2.1
  have hambient₂ := hpost₂.2.2.2.2.2.2.2.1
  have hA₀B₂ := hpost₂.2.2.2.2.2.2.2.2.1
  have hout₂ := hpost₂.2.2.2.2.2.2.2.2.2.1
  have hcols₂ := hpost₂.2.2.2.2.2.2.2.2.2.2.1
  have hbits₂ := hpost₂.2.2.2.2.2.2.2.2.2.2.2.1
  have hread₂ := hpost₂.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsupports₂ := hpost₂.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbatch₂ := hpost₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hlevel₂ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₂ :=
    levelPre_run_streamEnumColourCom hlevel₁keep hr₂
  have htables₂ : TablesSized q_top cap mb φ n σ₂ :=
    (hpre.tables.run hr₁).run hr₂
  have hbase₂ : BaseArrs B q_top cap mb ell φ σ₂ :=
    (hpre.base_arrs.run hr₁).run hr₂
  have hkillAlloc : ∃ g, σ₂.arrs (klName j) = arrOf mb g :=
    (hdepthMem.run (hr₁.seq hr₂)).kl j
  obtain ⟨σ₃, hr₃, ⟨hkill₃, hout₃⟩⟩ :=
    (streamKillListStep hB).run
      { sorted := hsorted₂
        cluster_set := hcluster₂
        data := hdata₂
        supports := hsupports₂
        batch_arr := hbatch₂
        wa := hwa₂
        play := hplay₂
        colour_state := hcolour₂
        ambient_arr := hambient₂
        ambient_bound := hA₀B₂
        colour_arr := hcols₂
        colour_bit := hbits₂
        colour_read := hread₂
        tables := htables₂
        base_arrs := hbase₂
        kill_alloc := hkillAlloc }
  have hlevel₃ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₃ :=
    levelPre_run_streamKillListCom hlevel₂ hr₃
  have hparent₃ : PlayRec B cap G j A₀ Gm σ₃ :=
    hparent₂.congr
      (fun a ha => hr₃.frame_var _
        (belowVar_notMem_wvars_streamKillListCom q_top cap mb j φ
          ⟨a, ha, Or.inl rfl⟩))
      (fun a ha => hr₃.frame_arr _
        (belowArr_notMem_warrs_streamKillListCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))
      (fun a ha => hr₃.frame_arr _
        (belowArr_notMem_warrs_streamKillListCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inl rfl)⟩))
      (fun a ha => hr₃.frame_arr _
        (belowArr_notMem_warrs_streamKillListCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))
  refine ⟨σ₃, _, ?_, le_rfl, Xa, Mm, Ra, Wa, Alv, Gam, Mem, mm, w, C',
    hkill₃, hparent₃, hlevel₃, hkill₃.tables, hkill₃.base_arrs, ?_⟩
  · simpa [streamPrepareCom, streamPrepareCost] using hr₁.seq (hr₂.seq hr₃)
  · exact hout₃.trans (hout₂.trans (hout₁ (noWrite_streamPlayCom cap j)))

/-! ## Depth-owned execution -/

noncomputable def streamPrepareAtDepthCom
    (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) : Com :=
  streamAtDepthCom j (streamPrepareCom q_top cap mb j φ)

private theorem notMem_warrs_streamPrepareCom_of_parts
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {a : String}
    (hplay : a ∉ (streamPlayCom cap j).warrs)
    (henum : a ∉ (streamEnumColourCom cap mb j).warrs)
    (hkill : a ∉ (streamKillListCom q_top cap mb j φ).warrs) :
    a ∉ (streamPrepareCom q_top cap mb j φ).warrs := by
  intro h
  simp only [streamPrepareCom, Com.warrs, List.mem_append] at h
  rcases h with h | h | h
  exacts [hplay h, henum h, hkill h]

theorem belowArr_notMem_warrs_streamPrepareAtDepthCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamPrepareAtDepthCom q_top cap mb j phi).warrs := by
  have hd := Lax3Proofs.RamDriverWrites.hasDigit_of_belowArr h
  have hplay : a ∉ (streamPlayCom cap j).warrs := by
    apply notMem_warrs_streamPlayCom
    · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
    · exact Lax3Proofs.RamDriverWrites.belowArr_ne_memName h (Nat.le_succ j)
    · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
    · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
    · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
    · exact fun hq =>
        (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "q") (hq ▸ hd)
    · exact fun hq =>
        (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "qd") (hq ▸ hd)
    · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
    · exact Lax3Proofs.RamDriverWrites.belowArr_ne h (Nat.le_succ j) (by tauto)
    · exact Lax3Proofs.RamDriverWrites.belowArr_ne h (Nat.le_succ j) (by tauto)
  have henum : a ∉ (streamEnumColourCom cap mb j).warrs := by
    apply notMem_warrs_streamEnumColourCom
    · exact fun hq =>
        (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "wa") (hq ▸ hd)
    · intro s hs
      exact Lax3Proofs.RamDriverWrites.belowArr_ne h (Nat.le_succ j) (by tauto)
  have hkill : a ∉ (streamKillListCom q_top cap mb j phi).warrs :=
    belowArr_notMem_warrs_streamKillListCom q_top cap mb j phi h
  intro hw
  have hpull := Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
    (streamDepthSwap_invol j) (streamPrepareCom q_top cap mb j phi) hw
  rw [streamDepthSwap_of_belowArr h] at hpull
  exact (notMem_warrs_streamPrepareCom_of_parts hplay henum hkill) hpull

theorem belowVar_notMem_wvars_streamPrepareAtDepthCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {y : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamPrepareAtDepthCom q_top cap mb j phi).wvars := by
  have hd := Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h
  have hplay : y ∉ (streamPlayCom cap j).wvars := by
    apply notMem_wvars_streamPlayCom
    · exact Lax3Proofs.RamDriverWrites.belowVar_ne h le_rfl (by tauto)
    · exact Lax3Proofs.RamDriverWrites.belowVar_ne_mnumName h (Nat.le_succ j)
    · exact fun hq =>
        (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "cw") (hq ▸ hd)
    · intro hm
      exact (Lax3Proofs.RamDriverWrites.notHasDigit_mem (by decide) hm) hd
  have henum : y ∉ (streamEnumColourCom cap mb j).wvars := by
    apply notMem_wvars_streamEnumColourCom <;>
      first
      | exact fun hq =>
          (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit _) (hq ▸ hd)
      | (intro hm;
          exact (Lax3Proofs.RamDriverWrites.notHasDigit_mem (by decide) hm) hd)
  have hkill : y ∉ (streamKillListCom q_top cap mb j phi).wvars :=
    belowVar_notMem_wvars_streamKillListCom q_top cap mb j phi h
  simpa [streamPrepareAtDepthCom, streamAtDepthCom,
    Lax3Proofs.Refine.ScatterBlock.renCom_wvars, streamPrepareCom, Com.wvars]
    using And.intro hplay (And.intro henum hkill)

theorem tabName_notMem_streamPrepareCom
    {q_top cap mb j i : ℕ} {φ : Lax3.FirstOrder.FO 0} :
    tabName j i ∉ (streamPrepareCom q_top cap mb j φ).warrs := by
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1
  intro h
  simp only [streamPrepareCom, Com.warrs, List.mem_append] at h
  rcases h with h | h | h
  · exact notMem_warrs_streamPlayCom
      (by simp [tabName, cluName, String.ext_iff])
      (by simp [tabName, memName, String.ext_iff])
      (by simp [tabName, resName, String.ext_iff])
      (by simp [tabName, balAltName, String.ext_iff])
      (by simp [tabName, balName, String.ext_iff])
      (RamDriverBase.tabName_ne_lit j i (by decide))
      (RamDriverBase.tabName_ne_lit j i (by decide))
      (by simp [tabName, batName, String.ext_iff])
      (by simp [tabName, alvName, String.ext_iff])
      (by simp [tabName, gamName, String.ext_iff]) h
  · exact notMem_warrs_streamEnumColourCom
      (RamDriverBase.tabName_ne_lit j i (by decide))
      (fun s _ => Lax3Proofs.RamDriverFrames.tabName_ne_colName j i (j + 1) s) h
  · exact notMem_warrs_streamKillListCom hlocal
      (RamDriverBase.tabName_ne_succ j i)
      (Lax3Proofs.Refine.ScatterDeadTurn.not_ext_bb_tabName j i)
      (by simp [tabName, klName, String.ext_iff]) h

theorem tabName_notMem_streamPrepareAtDepthCom
    {q_top cap mb j i : ℕ} {φ : Lax3.FirstOrder.FO 0} :
    tabName j i ∉ (streamPrepareAtDepthCom q_top cap mb j φ).warrs := by
  intro h
  have hpull := Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
    (streamDepthSwap_invol j) (streamPrepareCom q_top cap mb j φ) h
  exact tabName_notMem_streamPrepareCom
    (by simpa only [streamDepthSwap_tabName] using hpull)

/-- Preparation consumes the current level's clean buffers but leaves every
strictly deeper reusable buffer untouched.  The distance-word clause needs no
frame hypothesis: bounded execution itself preserves word-valued arrays. -/
theorem streamScratchFrom_run_streamPrepareAtDepthCom
    {B n q_top cap mb ell j K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {σ σ' : Env}
    (hscratch : StreamScratchFrom B n cap mb ell (j + 1) σ)
    (hr : Run B (streamPrepareAtDepthCom q_top cap mb j φ) σ σ' K) :
    StreamScratchFrom B n cap mb ell (j + 1) σ' := by
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1
  have lift {a : String}
      (hswap : streamDepthSwap j a = a)
      (hlogical : a ∉ (streamPrepareCom q_top cap mb j φ).warrs) :
      a ∉ (streamPrepareAtDepthCom q_top cap mb j φ).warrs := by
    intro h
    have hpull := Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
      (streamDepthSwap_invol j) (streamPrepareCom q_top cap mb j φ) h
    rw [hswap] at hpull
    exact hlogical hpull
  apply hscratch.run hr
  · intro d hd _
    have hdj : d ≠ j := by omega
    apply lift (a := cpsName d)
    · apply streamDepthSwap_of_ne
      · simp [cpsName, String.ext_iff]
      · simp [cpsName, ordName, String.ext_iff]
      · simp [cpsName, String.ext_iff]
      · intro h
        exact hdj (Lax3Proofs.RamDriverWrites.cpsName_inj h)
      · simp [cpsName, String.ext_iff]
      · simp [cpsName, xmmName, String.ext_iff]
      · simp [cpsName, String.ext_iff]
      · simp [cpsName, asgName, String.ext_iff]
      · simp [cpsName, String.ext_iff]
      · simp [cpsName, pdsName, balAltName, String.ext_iff]
    · apply notMem_warrs_streamPrepareCom_of_parts
      · exact notMem_warrs_streamPlayCom
          (by simp [cpsName, cluName, String.ext_iff])
          (by simp [cpsName, memName, String.ext_iff])
          (by simp [cpsName, resName, String.ext_iff])
          (by simp [cpsName, balAltName, String.ext_iff])
          (by simp [cpsName, balName, String.ext_iff])
          (by simp [cpsName, String.ext_iff])
          (by simp [cpsName, String.ext_iff])
          (by simp [cpsName, batName, String.ext_iff])
          (by simp [cpsName, alvName, String.ext_iff])
          (by simp [cpsName, gamName, String.ext_iff])
      · exact notMem_warrs_streamEnumColourCom
          (by simp [cpsName, String.ext_iff])
          (fun s _ => by simp [cpsName, colName, String.ext_iff])
      · exact notMem_warrs_streamKillListCom hlocal
          (fun i => by simp [cpsName, tabName, String.ext_iff])
          (by
            simpa [cpsName] using
              (Lax3Proofs.RamDriverWrites.not_ext_bb_append (p := "cs")
                (by decide) (by decide) (toString d)))
          (by simp [cpsName, klName, String.ext_iff])
  · intro d hd _
    apply lift (a := cluName d) (by simp)
    apply notMem_warrs_streamPrepareCom_of_parts
    · exact notMem_warrs_streamPlayCom
        (fun h => by
          have := Lax3Proofs.RamDriverWrites.cluName_inj h
          omega)
        (by simp [cluName, memName, String.ext_iff])
        (by simp [cluName, resName, String.ext_iff])
        (by simp [cluName, balAltName, String.ext_iff])
        (by simp [cluName, balName, String.ext_iff])
        (by simp [cluName, String.ext_iff])
        (by simp [cluName, String.ext_iff])
        (by simp [cluName, batName, String.ext_iff])
        (by simp [cluName, alvName, String.ext_iff])
        (by simp [cluName, gamName, String.ext_iff])
    · exact notMem_warrs_streamEnumColourCom
        (by simp [cluName, String.ext_iff])
        (fun s _ => by simp [cluName, colName, String.ext_iff])
    · exact notMem_warrs_streamKillListCom hlocal
        (fun i => by simp [cluName, tabName, String.ext_iff])
        (by
          simpa [cluName] using
            (Lax3Proofs.RamDriverWrites.not_ext_bb_append (p := "clu")
              (by decide) (by decide) (toString d)))
        (by simp [cluName, klName, String.ext_iff])
  · intro d hd _
    apply lift (a := resName d) (by simp)
    apply notMem_warrs_streamPrepareCom_of_parts
    · exact notMem_warrs_streamPlayCom
        (by simp [resName, cluName, String.ext_iff])
        (by simp [resName, memName, String.ext_iff])
        (fun h => by
          have := Lax3Proofs.RamDriverWrites.resName_inj h
          omega)
        (by simp [resName, balAltName, String.ext_iff])
        (by simp [resName, balName, String.ext_iff])
        (by simp [resName, String.ext_iff])
        (by simp [resName, String.ext_iff])
        (by simp [resName, batName, String.ext_iff])
        (by simp [resName, alvName, String.ext_iff])
        (by simp [resName, gamName, String.ext_iff])
    · exact notMem_warrs_streamEnumColourCom
        (by simp [resName, String.ext_iff])
        (fun s _ => by simp [resName, colName, String.ext_iff])
    · exact notMem_warrs_streamKillListCom hlocal
        (fun i => by simp [resName, tabName, String.ext_iff])
        (by
          simpa [resName] using
            (Lax3Proofs.RamDriverWrites.not_ext_bb_append (p := "res")
              (by decide) (by decide) (toString d)))
        (by simp [resName, klName, String.ext_iff])
  · intro d hd _
    apply lift (a := batName d) (by simp)
    apply notMem_warrs_streamPrepareCom_of_parts
    · exact notMem_warrs_streamPlayCom
        (by simp [batName, cluName, String.ext_iff])
        (by simp [batName, memName, String.ext_iff])
        (by simp [batName, resName, String.ext_iff])
        (by simp [batName, balAltName, String.ext_iff])
        (by simp [batName, balName, String.ext_iff])
        (by simp [batName, String.ext_iff])
        (by simp [batName, String.ext_iff])
        (fun h => by
          have := Lax3Proofs.RamDriverWrites.batName_inj h
          omega)
        (by simp [batName, alvName, String.ext_iff])
        (by simp [batName, gamName, String.ext_iff])
    · exact notMem_warrs_streamEnumColourCom
        (by simp [batName, String.ext_iff])
        (fun s _ => by simp [batName, colName, String.ext_iff])
    · exact notMem_warrs_streamKillListCom hlocal
        (fun i => by simp [batName, tabName, String.ext_iff])
        (by
          simpa [batName] using
            (Lax3Proofs.RamDriverWrites.not_ext_bb_append (p := "bat")
              (by decide) (by decide) (toString d)))
        (by simp [batName, klName, String.ext_iff])
  · intro d hd _
    apply lift (a := alvName (d + 1)) (by simp)
    apply notMem_warrs_streamPrepareCom_of_parts
    · exact notMem_warrs_streamPlayCom
        (by simp [alvName, cluName, String.ext_iff])
        (by simp [alvName, memName, String.ext_iff])
        (by simp [alvName, resName, String.ext_iff])
        (by simp [alvName, balAltName, String.ext_iff])
        (by simp [alvName, balName, String.ext_iff])
        (by simp [alvName, String.ext_iff])
        (by simp [alvName, String.ext_iff])
        (by simp [alvName, batName, String.ext_iff])
        (fun h => by
          have := Lax3Proofs.RamDriverWrites.alvName_inj h
          omega)
        (by simp [alvName, gamName, String.ext_iff])
    · exact notMem_warrs_streamEnumColourCom
        (by simp [alvName, String.ext_iff])
        (fun s _ => by simp [alvName, colName, String.ext_iff])
    · exact notMem_warrs_streamKillListCom hlocal
        (fun i => by simp [alvName, tabName, String.ext_iff])
        (by
          simpa [alvName] using
            (Lax3Proofs.RamDriverWrites.not_ext_bb_append (p := "alv")
              (by decide) (by decide) (toString (d + 1))))
        (by simp [alvName, klName, String.ext_iff])
  · intro d hd _
    apply lift (a := gamName (d + 1)) (by simp)
    apply notMem_warrs_streamPrepareCom_of_parts
    · exact notMem_warrs_streamPlayCom
        (by simp [gamName, cluName, String.ext_iff])
        (by simp [gamName, memName, String.ext_iff])
        (by simp [gamName, resName, String.ext_iff])
        (by simp [gamName, balAltName, String.ext_iff])
        (by simp [gamName, balName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [gamName, batName, String.ext_iff])
        (by simp [gamName, alvName, String.ext_iff])
        (fun h => by
          have := Lax3Proofs.RamDriverWrites.gamName_inj h
          omega)
    · exact notMem_warrs_streamEnumColourCom
        (by simp [gamName, String.ext_iff])
        (fun s _ => by simp [gamName, colName, String.ext_iff])
    · exact notMem_warrs_streamKillListCom hlocal
        (fun i => by simp [gamName, tabName, String.ext_iff])
        (by
          simpa [gamName] using
            (Lax3Proofs.RamDriverWrites.not_ext_bb_append (p := "gam")
              (by decide) (by decide) (toString (d + 1))))
        (by simp [gamName, klName, String.ext_iff])
  · intro d hd _ s _
    apply lift (a := colName (d + 1) s) (by simp)
    apply notMem_warrs_streamPrepareCom_of_parts
    · exact notMem_warrs_streamPlayCom
        (by simp [colName, cluName, String.ext_iff])
        (by simp [colName, memName, String.ext_iff])
        (by simp [colName, resName, String.ext_iff])
        (by simp [colName, balAltName, String.ext_iff])
        (by simp [colName, balName, String.ext_iff])
        (by simp [colName, String.ext_iff])
        (by simp [colName, String.ext_iff])
        (by simp [colName, batName, String.ext_iff])
        (by simp [colName, alvName, String.ext_iff])
        (by simp [colName, gamName, String.ext_iff])
    · exact notMem_warrs_streamEnumColourCom
        (by simp [colName, String.ext_iff])
        (fun t _ h => by
          have := (Lax3Proofs.RamDriverWrites.colName_inj h).1
          omega)
    · exact notMem_warrs_streamKillListCom hlocal
        (fun i => Lax3Proofs.RamDriverBot.colName_ne_tabName _ _ _ _)
        (by
          simpa [colName, String.append_assoc] using
            (Lax3Proofs.RamDriverWrites.not_ext_bb_append (p := "co")
              (by decide) (by decide)
              (toString (d + 1) ++ "_" ++ toString s)))
        (by simp [colName, klName, String.ext_iff])

/-- Pulling back the semantic clauses and retaining the physical length
clauses reconstructs the parent level after a renamed run.  The five swapped
arrays are scratch/depth-storage pairs; none of the mathematical parent
arrays (`alvName`, `gamName`, colours, or members) is renamed. -/
theorem levelPre_of_renEnv_streamDepthSwap
    {B n cap mb ns nt j K : ℕ} {O T A₀ Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {cmd : Com} {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B cmd σ σ' K)
    (hlog : LevelPre B n cap mb ns nt O T j A₀ Gm C
      (Lax3Proofs.Refine.ScatterBlock.renEnv (streamDepthSwap j) σ')) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hlevelMem₀, hdepthMem₀,
    -, -, -, -, -⟩ := hp
  obtain ⟨hn, hoff, htgt, halv, hgam, hcol, hA₀B, hGmB, hCbit,
    -, -, hm, horder, hpad, htB, hmember⟩ := hlog
  have horder' : OrderMem B n ns nt σ' := by
    simpa [OrderMem, Sized, Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      Lax3Proofs.Refine.ScatterBlock.renEnv_vars, streamDepthSwap, ordName,
      cpsName, xmmName, asgName, pdsName, balAltName, String.ext_iff] using horder
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, hA₀B, hGmB, hCbit,
    levelMem_run hr hlevelMem₀, hdepthMem₀.run hr, hm, horder', hpad, htB, ?_⟩
  · simpa [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs, streamDepthSwap,
      ordName, cpsName, xmmName, asgName, pdsName, balAltName,
      String.ext_iff] using hoff
  · simpa [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs, streamDepthSwap,
      ordName, cpsName, xmmName, asgName, pdsName, balAltName,
      String.ext_iff] using htgt
  · simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_alvName] using halv
  · simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_gamName] using hgam
  · intro s hs
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_colName] using hcol s hs
  · obtain ⟨Mem, mm, hMem, hmm, henum, hbound⟩ := hmember
    exact ⟨Mem, mm,
      by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
        streamDepthSwap_memName] using hMem,
      by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using hmm,
      henum, hbound⟩

open Classical in
/-- Renaming the complete preparation onto the parent's five depth-owned
arrays is cost-free.  The semantic result is exactly the physical payload
accepted by `streamCentreFinishStep`; length-only memory is retained in the
actual environment independently of the pulled-back logical view. -/
theorem streamPrepareAtDepthStep
    {B n q_top cap mb ns nt na q j c tail bits ell d : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ}
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : Lax3Proofs.RamBfs.CsrGraph G ns O T) (hnt : ns ≤ nt)
    (hB : WordBoundK B n d ns cap mb)
    (hmb : mb = ell * (2 * cap + 1)) (hjl : j < ell) :
    Spec B
      (fun σ =>
        StreamPreparePre B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
          centre O T Xmem asg M Gm C
          (Lax3Proofs.Refine.ScatterBlock.renEnv (streamDepthSwap j) σ) ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ ∧
        TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ell φ σ)
      (streamPrepareAtDepthCom q_top cap mb j φ)
      (fun σ σ' => ∃ (Xa Mm Ra Wa Alv Gam Mem : ℕ → ℕ) (mm : ℕ)
          (w : Fin mb → Fin n) (C' : ℕ → ℕ → ℕ),
        StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
          centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ' ∧
        PlayRec B cap G j A₀ Gm
          (Lax3Proofs.Refine.ScatterBlock.renEnv (streamDepthSwap j) σ') ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ' ∧
        TablesSized q_top cap mb φ n σ' ∧
        BaseArrs B q_top cap mb ell φ σ' ∧
        σ'.out = σ.out)
      (streamPrepareCost q_top cap mb j tail
        (expandRowSum O Xmem 0 tail)
        (activeBallWeight n G A₀ π centre O cap c) φ) := by
  refine Spec.of_exists fun σ hpre => ?_
  obtain ⟨σ', hr, hpost⟩ :=
    (Lax3Proofs.Refine.ScatterBlock.renCom_spec (streamDepthSwap_invol j)
      (streamPrepareStep hcentres hcsr hnt hB hmb hjl)).run hpre.1
  obtain ⟨Xa, Mm, Ra, Wa, Alv, Gam, Mem, mm, w, C', hkill, hparent,
    hlevelLog, -, -, hout⟩ := hpost
  have hlevel : LevelPre B n cap mb ns nt O T j A₀ Gm C σ' :=
    levelPre_of_renEnv_streamDepthSwap hpre.2.1 hr hlevelLog
  refine ⟨σ', _, ?_, le_rfl, Xa, Mm, Ra, Wa, Alv, Gam, Mem, mm, w, C',
    hkill, hparent, hlevel, hpre.2.2.1.run hr, hpre.2.2.2.run hr, ?_⟩
  · simpa [streamPrepareAtDepthCom] using hr
  · simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_out] using hout

end Lax3Proofs.Refine.CoverActiveStreamPrepare
