import Lax3Proofs.Refine.AugCompactScatter
import Lax3Proofs.Refine.CompactPreps

/-!
# Running a compact augmentation at its live allocation width

AugCompact already removes the ambient carrier from every loop, but its
public postcondition uses the physical allocation width. A level owns one
large scratch allocation shared by all arenas; charging every arena at that
global width would therefore lose the mass bound. Here the IMP+ length seam
is used once more: cut a live-width view, run the unchanged compact round at
that width, and put the untouched physical tails back.
-/

namespace Lax3Proofs.Refine.OrderActiveWidth

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamDriver (exists_arrOf)
open Lax3Proofs.Augmentation (Orientation)
open Lax3Proofs.RamAugment (fratSlots)
open Lax3Proofs.RamElim (InCsr)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.Refine.ElimCompact (cutArrs padArrs tailOf cutArrs_arrs cutArrs_vars
  padArrs_arrs padArrs_vars run_of_run_cutArrs run_length take_arrOf getD_padArrs)
open Lax3Proofs.Refine.AugCompact
open Lax3Proofs.Refine.AugCompactScatter (augCompact_specE)

/-- The outer live-width view. augClen at carrier n has exactly the
required physical lengths for every engine array; the two driver-owned
arrays that the compact composite also consumes are added explicitly. -/
def augWClen (n nt w : ℕ) : String → ℕ := fun a =>
  if a = "mem" ∨ a = "ork" then n else augClen n nt w a

@[simp] theorem augWClen_mem (n nt w : ℕ) : augWClen n nt w "mem" = n := by
  simp [augWClen]

@[simp] theorem augWClen_ork (n nt w : ℕ) : augWClen n nt w "ork" = n := by
  simp [augWClen]

private theorem augWClen_of_engine {n nt w : ℕ} {a : String}
    (hmem : a ≠ "mem") (hork : a ≠ "ork") :
    augWClen n nt w a = augClen n nt w a := by
  simp [augWClen, hmem, hork]

/-- A physical-width compact entry restricts to any smaller allocation
that still contains the current compact in-list. -/
theorem augEntryC_cutWidth {n mm nt W w kd : ℕ} {IO IT : ℕ → ℕ} {σ : Env}
    (hwW : w ≤ W) (hkdw : kd ≤ w) (h : AugEntryC n mm nt W kd IO IT σ) :
    AugEntryC n mm nt w kd IO IT (cutArrs σ (augWClen n nt w)) := by
  obtain ⟨hn, hmm, hkd, hmn, -, ⟨io, hio, hioP⟩, ⟨it, hit, hitP⟩,
    ⟨do_, hdo⟩, ⟨dt, hdt⟩, ⟨oo, hoo⟩, ⟨ot, hot⟩, ⟨of_, hof⟩,
    ⟨off_, hoff⟩, ⟨tg, htg⟩, ⟨ff, hff⟩, ⟨al, hal⟩, ⟨dg, hdg⟩,
    ⟨em, hem⟩, ⟨rk, hrk⟩, ⟨id, hid⟩, ⟨bh, hbh⟩, ⟨bv, hbv⟩,
    ⟨bn, hbn⟩, ⟨ifl, hifl⟩, ⟨no, hno⟩, ⟨nf, hnf⟩, ⟨ntg, hntg⟩,
    ⟨sf, hsf⟩, ⟨sa, hsa⟩, ⟨sd, hsd⟩, ⟨se, hse⟩, ⟨ork, hork⟩⟩ := h
  refine ⟨?_, ?_, ?_, hmn, hkdw, ?_⟩
  · simpa only [cutArrs_vars] using hn
  · simpa only [cutArrs_vars] using hmm
  · simpa only [cutArrs_vars] using hkd
  refine ⟨⟨io, ?_, hioP⟩, ⟨it, ?_, hitP⟩, ⟨do_, ?_⟩, ⟨dt, ?_⟩, ⟨oo, ?_⟩,
    ⟨ot, ?_⟩, ⟨of_, ?_⟩, ⟨off_, ?_⟩, ⟨tg, ?_⟩, ⟨ff, ?_⟩, ⟨al, ?_⟩,
    ⟨dg, ?_⟩, ⟨em, ?_⟩, ⟨rk, ?_⟩, ⟨id, ?_⟩, ⟨bh, ?_⟩, ⟨bv, ?_⟩,
    ⟨bn, ?_⟩, ⟨ifl, ?_⟩, ⟨no, ?_⟩, ⟨nf, ?_⟩, ⟨ntg, ?_⟩, ⟨sf, ?_⟩,
    ⟨sa, ?_⟩, ⟨sd, ?_⟩, ⟨se, ?_⟩, ⟨ork, ?_⟩⟩
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_ioff,
      hio, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_itg,
      hit, take_arrOf hwW]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_doff,
      hdo, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_dtg,
      hdt, take_arrOf hwW]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_ooff,
      hoo, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_otg,
      hot, take_arrOf hwW]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_ofl,
      hof, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_off,
      hoff, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_tgt,
      htg, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_ffl,
      hff, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_alv,
      hal, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_deg,
      hdg, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_elm,
      hem, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_rnk,
      hrk, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_idg,
      hid, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_bh,
      hbh, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_bv,
      hbv, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_bn,
      hbn, take_arrOf (by omega)]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_ifl,
      hifl, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_noff,
      hno, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_nfl,
      hnf, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_ntg,
      hntg, take_arrOf hwW]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_stf,
      hsf, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_sta,
      hsa, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_std,
      hsd, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_of_engine (by decide) (by decide), augClen_ste,
      hse, take_arrOf le_rfl]
  · rw [cutArrs_arrs, augWClen_ork, hork, take_arrOf le_rfl]

theorem mem_cutWidth {n nt w : ℕ} {Mem : ℕ → ℕ} {σ : Env}
    (hmem : σ.arrs "mem" = arrOf n Mem) :
    (cutArrs σ (augWClen n nt w)).arrs "mem" = arrOf n Mem := by
  rw [cutArrs_arrs, augWClen_mem, hmem, take_arrOf le_rfl]

/-! ## The live-width round in the physical store -/

/-- Run one compact augmentation at a live allocation width w, inside
physical arrays of width W. The clock is charged at w; the result is
nevertheless a physical-width AugMemPost, so the next round can consume
it without changing interfaces. -/
theorem augCompact_specLive {B n mm nt W w kd d db m : ℕ} {D : Orientation mm}
    {Mem IO IT : ℕ → ℕ} {X : Set (Fin n)} {σ : Env}
    (hml : MemList n mm Mem X) (hin : InCsr D m IO IT) (hd : D.InDegLE d)
    (hmkd : m ≤ kd) (hkdw : kd ≤ w) (hwW : w ≤ W) (hnt : fratSlots D ≤ nt)
    (hdb : 2 * (d * d) + d ≤ db) (hwidth : augWidthE mm kd db ≤ w)
    (hB : mm + w + 1 < B) (hnB : n < B)
    (hIOB : ∀ i ≤ mm, IO i < B) (hITB : ∀ j < kd, IT j < B)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hent : AugEntryC n mm nt W kd IO IT σ) :
    ∃ σ'', Run B augCompactCore σ σ'' (augCompactCost mm kd w) ∧
      AugMemPost mm W Mem D σ'' ∧
      (σ''.arrs "alv").drop mm = (σ.arrs "alv").drop mm ∧
      σ''.vars "kn" = n := by
  classical
  let len := augWClen n nt w
  have hentView : AugEntryC n mm nt w kd IO IT (cutArrs σ len) := by
    exact augEntryC_cutWidth hwW hkdw hent
  have hmemView : (cutArrs σ len).arrs "mem" = arrOf n Mem := by
    exact mem_cutWidth hmem
  obtain ⟨hn, hmm, hkd, hmn, -, ⟨io, hio, hioP⟩, ⟨it, hit, hitP⟩,
    ⟨do_, hdo⟩, ⟨dt, hdt⟩, ⟨oo, hoo⟩, ⟨ot, hot⟩, ⟨of_, hof⟩,
    ⟨off_, hoff⟩, ⟨tg, htg⟩, ⟨ff, hff⟩, ⟨al, hal⟩, ⟨dg, hdg⟩,
    ⟨em, hem⟩, ⟨rk, hrk⟩, ⟨id, hid⟩, ⟨bh, hbh⟩, ⟨bv, hbv⟩,
    ⟨bn, hbn⟩, ⟨ifl, hifl⟩, ⟨no, hno⟩, ⟨nf, hnf⟩, ⟨nt₀, hnt₀⟩,
    ⟨sf, hsf⟩, ⟨sa, hsa⟩, ⟨sd, hsd⟩, ⟨se, hse⟩, ⟨ork₀, hork₀⟩⟩ := hent
  obtain ⟨τ, hrun, hpost, halvt, hkn⟩ :=
    augCompact_specE
      (Lax3Proofs.Refine.CompactPreps.augPreps B n mm nt w kd) hml hin hd hmkd hkdw hnt
      hdb hwidth hB hnB hmn hIOB hITB hmemView hentView
  let σ'' := padArrs τ (tailOf σ len)
  have hrun' : Run B augCompactCore σ σ'' (augCompactCost mm kd w) := by
    exact run_of_run_cutArrs len hrun
  obtain ⟨R, NO, NT, k, m', D', hork, hk, hnoff, hntg, hmn', hmw, hstep, hcsr,
    hlow, hgreedy, hdegree, harcs⟩ := hpost
  have hlenOrk : len "ork" = n := by simp [len]
  have hlenNoff : len "noff" = n + 1 := by
    simp [len, augWClen, augClen]
  have hlenNtg : len "ntg" = w := by
    simp [len, augWClen, augClen]
  have hlenAlv : len "alv" = n := by
    simp [len, augWClen, augClen]
  have hτork : (τ.arrs "ork").length = n := by
    rw [run_length hrun "ork", cutArrs_arrs, hlenOrk, hork₀,
      take_arrOf le_rfl, length_arrOf]
  have hτnoff : (τ.arrs "noff").length = n + 1 := by
    rw [run_length hrun "noff", cutArrs_arrs, hlenNoff, hno,
      take_arrOf le_rfl, length_arrOf]
  have hτntg : (τ.arrs "ntg").length = w := by
    rw [run_length hrun "ntg", cutArrs_arrs, hlenNtg, hnt₀,
      take_arrOf hwW, length_arrOf]
  have hork' : ∀ j, j < mm → (σ''.arrs "ork").getD (Mem j) 0 = R j := by
    intro j hj
    have hp := getD_padArrs (τ := τ) (tl := tailOf σ len) (a := "ork")
      (i := Mem j) (by rw [hτork]; exact hml.lt j hj)
    simpa only [σ''] using hp.trans (hork j hj)
  have hnoff' : ∀ i, i ≤ mm → (σ''.arrs "noff").getD i 0 = NO i := by
    intro i hi
    have hp := getD_padArrs (τ := τ) (tl := tailOf σ len) (a := "noff")
      (i := i) (by rw [hτnoff]; omega)
    simpa only [σ''] using hp.trans (hnoff i hi)
  have hntgLen : (σ''.arrs "ntg").length = W := by
    rw [run_length hrun' "ntg", hnt₀, length_arrOf]
  obtain ⟨NT', hntg'⟩ := exists_arrOf hntgLen
  have hNT : ∀ z, z < w → NT' z = NT z := by
    intro z hz
    have hp := getD_padArrs (τ := τ) (tl := tailOf σ len) (a := "ntg")
      (i := z) (by rw [hτntg]; exact hz)
    have hp' : (σ''.arrs "ntg").getD z 0 = (τ.arrs "ntg").getD z 0 := by
      simpa only [σ''] using hp
    rw [hntg', getD_arrOf NT' (lt_of_lt_of_le hz hwW), hntg, getD_arrOf NT hz] at hp'
    exact hp'
  have hcsr' : InCsr D' m' NO NT' :=
    Lax3Proofs.RamDriverAugment.inCsr_congr_prefix hcsr fun z hz =>
      hNT z (lt_of_lt_of_le hz hmw)
  have hpost' : AugMemPost mm W Mem D σ'' := by
    refine ⟨R, NO, NT', k, m', D', hork', ?_, hnoff', hntg', ?_,
      hmw.trans hwW, hstep, hcsr', hlow, hgreedy, hdegree, harcs⟩
    · simpa only [σ''] using hk
    · simpa only [σ''] using hmn'
  have htailAlv : tailOf σ len "alv" = [] := by
    rw [tailOf, hlenAlv, hal]
    exact List.drop_eq_nil_of_le (by simp [arrOf])
  have halvView : (cutArrs σ len).arrs "alv" = σ.arrs "alv" := by
    rw [cutArrs_arrs, hlenAlv, hal, take_arrOf le_rfl]
  refine ⟨σ'', hrun', hpost', ?_, ?_⟩
  change ((padArrs τ (tailOf σ len)).arrs "alv").drop mm = (σ.arrs "alv").drop mm
  rw [padArrs_arrs, htailAlv, List.append_nil, halvt, halvView]
  · simpa only [σ'', padArrs_vars] using hkn

/-- The live-width round with the saved carrier restored.  This is the
form consumed by a multi-round active phase: each following round again
sees the ambient carrier in `n`, while the executable and semantic answer
of the compact core are unchanged. -/
theorem augCompactCom_specLive {B n mm nt W w kd d db m : ℕ} {D : Orientation mm}
    {Mem IO IT : ℕ → ℕ} {X : Set (Fin n)} {σ : Env}
    (hml : MemList n mm Mem X) (hin : InCsr D m IO IT) (hd : D.InDegLE d)
    (hmkd : m ≤ kd) (hkdw : kd ≤ w) (hwW : w ≤ W) (hnt : fratSlots D ≤ nt)
    (hdb : 2 * (d * d) + d ≤ db) (hwidth : augWidthE mm kd db ≤ w)
    (hB : mm + w + 1 < B) (hnB : n < B)
    (hIOB : ∀ i ≤ mm, IO i < B) (hITB : ∀ j < kd, IT j < B)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hent : AugEntryC n mm nt W kd IO IT σ) :
    ∃ σ'', Run B augCompactCom σ σ'' (augCompactCost mm kd w + 2) ∧
      AugMemPost mm W Mem D σ'' ∧
      (σ''.arrs "alv").drop mm = (σ.arrs "alv").drop mm ∧
      σ''.vars "n" = n := by
  obtain ⟨τ, hrun, hpost, htail, hkn⟩ :=
    augCompact_specLive hml hin hd hmkd hkdw hwW hnt hdb hwidth hB hnB hIOB hITB hmem hent
  let σ'' := τ.setVar "n" n
  have hr : Run B (.assign "n" (.var "kn")) τ σ'' 2 := by
    have h := Run.assign (B := B) (σ := τ) (x := "n") (e := .var "kn")
      (evalB_var (by rw [hkn]; omega))
    rw [hkn] at h
    simpa only [σ''] using h
  refine ⟨σ'', ?_, ?_, ?_, ?_⟩
  · exact hrun.seq hr
  · simpa only [σ'', AugMemPost, vars_setVar, arrs_setVar, if_neg (by decide)] using hpost
  · simpa only [σ'', arrs_setVar] using htail
  · simp [σ'']

/-! ## Axioms -/

#print axioms augEntryC_cutWidth
#print axioms augCompact_specLive
#print axioms augCompactCom_specLive

end Lax3Proofs.Refine.OrderActiveWidth
