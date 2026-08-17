import Lax3Proofs.Refine.CoverActiveStreamColour
import Lax3Proofs.Refine.KillListWalk

/-!
# Carrier-free kill rows and kill list for a streamed cover row

The streamed colour adapter ends at the same mathematical palette as the
ordinary cluster driver, but deliberately does not reconstruct `TurnPre` or
the materialised cover offsets.  This file connects that state directly to
the two buffer-local kill walks.  Both commands walk only the fixed padded
batch; the resident cover row and its sparse palette are framed for the
nested call and later readback.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamKill

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (CsrGraph masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBot
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.Refine.CoverActiveStreamColour
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.KillPass
open Lax3Proofs.Refine.KillListPass
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

noncomputable def streamKillListCom (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) : Com :=
  .seq (killCom q_top cap mb j φ) (killListCom mb j)

noncomputable def streamKillListCost (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  killCost q_top cap mb (j + 1) φ + killListCost mb

/-- Everything the two batch-local kill walks need after streamed colouring. -/
structure StreamKillPre {n : ℕ}
    (B q_top cap mb ns nt na q j c tail bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ)
    (C C' : ℕ → ℕ → ℕ) (w : Fin mb → Fin n) (σ : Env) : Prop where
  sorted : StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
    Xmem asg M σ
  cluster_set : markSet n Xa =
    Lax3Proofs.Refine.MassMath.clusterAt G A₀ π centre cap c
  data : ClusterData n mb j B G A₀ (markSet n Xa) (markSet n Wa) w Alv Gam σ
  supports : StreamReuseSupports n tail Xmem Xa Ra Wa Alv Gam
  batch_arr : σ.arrs (batName j) = arrOf n Wa
  wa : ClusterWa mb w σ
  play : PlayRec B cap G (j + 1) Alv Gam σ
  colour_state : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra
    (waCell mb w) σ
  ambient_arr : σ.arrs (alvName j) = arrOf n A₀
  ambient_bound : ∀ v, v < n → A₀ v < B
  colour_arr : ∀ s, s < sigL cap mb (j + 1) →
    σ.arrs (colName (j + 1) s) = arrOf n (C' s)
  colour_bit : ∀ s, s < sigL cap mb (j + 1) → ∀ v, v < n → C' s v ≤ 1
  colour_read : colRead n C' (sigL cap mb (j + 1)) =
    stepColoringP cap (masked G A₀) (colRead n C (sigL cap mb j))
      (markSet n Xa) w
  tables : TablesSized q_top cap mb φ n σ
  base_arrs : BaseArrs B q_top cap mb ell φ σ
  kill_alloc : ∃ g, σ.arrs (klName j) = arrOf mb g

/-- State handed to the nested recursive call.  The padded buffer is retained
only because both kill walks frame it; recursion is free to reuse it. -/
structure StreamKillOut {n : ℕ}
    (B q_top cap mb ns nt na q j c tail bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ)
    (C C' : ℕ → ℕ → ℕ) (w : Fin mb → Fin n) (σ : Env) : Prop where
  sorted : StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
    Xmem asg M σ
  cluster_set : markSet n Xa =
    Lax3Proofs.Refine.MassMath.clusterAt G A₀ π centre cap c
  data : ClusterData n mb j B G A₀ (markSet n Xa) (markSet n Wa) w Alv Gam σ
  supports : StreamReuseSupports n tail Xmem Xa Ra Wa Alv Gam
  batch_arr : σ.arrs (batName j) = arrOf n Wa
  wa : ClusterWa mb w σ
  play : PlayRec B cap G (j + 1) Alv Gam σ
  colour_state : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra
    (waCell mb w) σ
  ambient_arr : σ.arrs (alvName j) = arrOf n A₀
  ambient_bound : ∀ v, v < n → A₀ v < B
  colour_arr : ∀ s, s < sigL cap mb (j + 1) →
    σ.arrs (colName (j + 1) s) = arrOf n (C' s)
  colour_bit : ∀ s, s < sigL cap mb (j + 1) → ∀ v, v < n → C' s v ≤ 1
  colour_read : colRead n C' (sigL cap mb (j + 1)) =
    stepColoringP cap (masked G A₀) (colRead n C (sigL cap mb j))
      (markSet n Xa) w
  tables : TablesSized q_top cap mb φ n σ
  base_arrs : BaseArrs B q_top cap mb ell φ σ
  kill_rows : KillRowsAt q_top cap mb j φ G A₀ Alv
    (markSet n Xa) (markSet n Wa) C' σ
  kill_list : KillListAt mb j A₀ (markSet n Xa) (markSet n Wa) σ

/-! Small character-arithmetic frames used twice below. -/

theorem kill_frame_lit_arr
    {B q_top cap mb j K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {σ σ' : Env} {a : String}
    (hr : Run B (killCom q_top cap mb j φ) σ σ' K)
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β)
    (htab : ∀ i, a ≠ tabName (j + 1) i) (hext : ¬ Ext "bb" a) :
    σ'.arrs a = σ.arrs a :=
  hr.frame_arr a (notMem_warrs_killCom hlocal htab hext)

theorem kill_frame_lit_var
    {B q_top cap mb j K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {σ σ' : Env} {y : String}
    (hr : Run B (killCom q_top cap mb j φ) σ σ' K)
    (hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β)
    (hkk : y ≠ "kk") (hkv : y ≠ "kv")
    (hev : ∀ i, y ≠ envName i) (hext : ¬ Ext "bb" y) :
    σ'.vars y = σ.vars y :=
  hr.frame_var y (notMem_wvars_killCom hlocal hkk hkv hev hext)

/-- **The streamed kill seam.**  It writes the child rows, deduplicates the
kill set into the fixed-width list, and retains exactly the state required by
the nested level.  No carrier or materialised cover scan is introduced. -/
theorem streamKillListStep
    {B n q_top cap mb ns nt na q j c tail bits ell d : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n}
    (hB : WordBoundK B n d ns cap mb) :
    Spec B
      (StreamKillPre B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
        centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w)
      (streamKillListCom q_top cap mb j φ)
      (fun σ σ' =>
        StreamKillOut B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
          centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ' ∧
        σ'.out = σ.out)
      (streamKillListCost q_top cap mb j φ) := by
  classical
  refine Spec.of_exists fun σ hpre => ?_
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1
  obtain ⟨Xa₀, hXa₀, hXaSet, hXa₀bit⟩ := hpre.data.1.1
  have hXaEq : ∀ v, v < n → Xa₀ v = Xa v := by
    intro v hv
    exact eq_of_arrOf_eq (hXa₀.symm.trans hpre.colour_state.cluster_arr) hv
  have hXabit : ∀ v, v < n → Xa v ≤ 1 := by
    intro v hv
    rw [← hXaEq v hv]
    exact hXa₀bit v hv
  obtain ⟨σ₁, hr₁, hrows₁⟩ :=
    (killCom_spec (M := A₀) (Xa := Xa) (w := w) hB.one_lt hB.n_lt hB.mb_lt
      hpre.colour_bit hlocal hpre.ambient_bound hXabit).run (σ := σ)
      ⟨⟨hpre.colour_state.n_var, hpre.colour_arr,
          hpre.base_arrs.2 (j + 1)⟩,
        clusterWa_eq hpre.wa, hpre.ambient_arr,
        hpre.colour_state.cluster_arr,
        fun i hi => hpre.tables.get (j + 1) hi⟩
  have harr₁ : ∀ (a : String), (∀ i, a ≠ tabName (j + 1) i) →
      ¬ Ext "bb" a → σ₁.arrs a = σ.arrs a :=
    fun a ht he => kill_frame_lit_arr hr₁ hlocal ht he
  have hvar₁ : ∀ (y : String), y ≠ "kk" → y ≠ "kv" →
      (∀ i, y ≠ envName i) → ¬ Ext "bb" y → σ₁.vars y = σ.vars y :=
    fun y hkk hkv hev hext => kill_frame_lit_var hr₁ hlocal hkk hkv hev hext
  have hnev : ∀ (p : String) (ch : Char), (∃ t, p.toList = ch :: t) → ch ≠ 'e' →
      ∀ i, p ≠ envName i :=
    fun p ch hp hc i => ne_of_head_ne hp (head_envName i) hc
  have harrDepth₁ : ∀ b, σ₁.arrs (alvName b) = σ.arrs (alvName b) := fun b =>
    harr₁ _ (fun i => alvName_ne_tabName b (j + 1) i)
      (fun h => not_ext_b_alvName b (Lax3Proofs.RamDriverCompose.ext_b_of_ext_bb h))
  have harrGam₁ : ∀ b, σ₁.arrs (gamName b) = σ.arrs (gamName b) := fun b =>
    harr₁ _ (fun i => gamName_ne_tabName b (j + 1) i)
      (fun h => not_ext_b_gamName b (Lax3Proofs.RamDriverCompose.ext_b_of_ext_bb h))
  have harrRes₁ : ∀ b, σ₁.arrs (resName b) = σ.arrs (resName b) := fun b =>
    harr₁ _ (fun i => by simp [resName, tabName, String.ext_iff])
      (by rw [resName]; exact DeadSweep.not_ext_bb_append (p := "res") rfl (by decide) _)
  have harrPar₁ : ∀ b, σ₁.arrs (parName b) = σ.arrs (parName b) := fun b =>
    harr₁ _ (fun i => by simp [parName, balName, tabName, String.ext_iff])
      (by rw [parName, balName]
          exact RamDriverWrites.not_ext_bb_append (p := "bal") (by decide) (by decide) _)
  have harrCol₁ : ∀ b s, σ₁.arrs (colName b s) = σ.arrs (colName b s) := fun b s =>
    harr₁ _ (fun i => colName_ne_tabName b s (j + 1) i)
      (fun h => not_ext_b_colName b s (Lax3Proofs.RamDriverCompose.ext_b_of_ext_bb h))
  have harrMem₁ : ∀ b, σ₁.arrs (memName b) = σ.arrs (memName b) := fun b =>
    harr₁ _ (fun i => ne_of_head_ne (Lax3Proofs.RamDriverCompose.head_memName b)
      (head_tabName (j + 1) i) (by decide))
      (Lax3Proofs.RamDriverCompose.not_ext_bb_memName b)
  have hvarMm₁ : ∀ b, σ₁.vars (mnumName b) = σ.vars (mnumName b) := fun b =>
    hvar₁ _ (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (hnev _ 'm' ⟨_, by rw [mnumName, String.toList_append]; rfl⟩ (by decide))
      (Lax3Proofs.RamDriverCompose.not_ext_bb_mnumName b)
  have hwa₁ : ClusterWa mb w σ₁ := by
    change σ₁.arrs "wa" = arrOf mb (waCell mb w)
    rw [harr₁ "wa" (fun i => RamDriverBase.lit_ne_tabName (by decide) (j + 1) i)
      (not_ext_of_not_prefix (by decide))]
    exact clusterWa_eq hpre.wa
  have hambient₁ : σ₁.arrs (alvName j) = arrOf n A₀ := by
    rw [harrDepth₁ j]
    exact hpre.ambient_arr
  have hclu₁ : σ₁.arrs (cluName j) = arrOf n Xa := by
    rw [harr₁ _ (fun i => by simp [cluName, tabName, String.ext_iff])
      (by rw [cluName]; exact DeadSweep.not_ext_bb_append (p := "clu") rfl (by decide) _)]
    exact hpre.colour_state.cluster_arr
  have hkl₁ : ∃ g, σ₁.arrs (klName j) = arrOf mb g := by
    obtain ⟨g, hg⟩ := hpre.kill_alloc
    refine ⟨g, ?_⟩
    rw [harr₁ _ (fun i => by simp [klName, tabName, String.ext_iff])
      (by rw [klName]; exact DeadSweep.not_ext_bb_append (p := "kl") rfl (by decide) _)]
    exact hg
  obtain ⟨σ₂, hr₂, hlist₂⟩ :=
    (killListCom_spec (M := A₀) (Xa := Xa) (w := w) (j := j)
      hB.one_lt hB.n_lt hB.mb_lt hpre.ambient_bound hXabit).run (σ := σ₁)
      ⟨clusterWa_eq hwa₁, hambient₁, hclu₁, hkl₁⟩
  have harr₂ : ∀ a : String, a ≠ klName j → σ₂.arrs a = σ₁.arrs a :=
    fun a ha => hr₂.frame_arr a (RamDriverWrites.notMem_warrs_killListCom ha)
  have hvar₂ : ∀ y : String, y ≠ kkName j → y ≠ "kk" → y ≠ "kv" →
      y ≠ "kf" → y ≠ "kt" → σ₂.vars y = σ₁.vars y :=
    fun y h₁ h₂ h₃ h₄ h₅ =>
      hr₂.frame_var y (RamDriverWrites.notMem_wvars_killListCom h₁ h₂ h₃ h₄ h₅)
  have harrDepth₂ : ∀ b, σ₂.arrs (alvName b) = σ.arrs (alvName b) := fun b =>
    (harr₂ _ (by simp [alvName, klName, String.ext_iff])).trans (harrDepth₁ b)
  have harrGam₂ : ∀ b, σ₂.arrs (gamName b) = σ.arrs (gamName b) := fun b =>
    (harr₂ _ (by simp [gamName, klName, String.ext_iff])).trans (harrGam₁ b)
  have harrRes₂ : ∀ b, σ₂.arrs (resName b) = σ.arrs (resName b) := fun b =>
    (harr₂ _ (by simp [resName, klName, String.ext_iff])).trans (harrRes₁ b)
  have harrPar₂ : ∀ b, σ₂.arrs (parName b) = σ.arrs (parName b) := fun b =>
    (harr₂ _ (by simp [parName, balName, klName, String.ext_iff])).trans (harrPar₁ b)
  have harrCol₂ : ∀ b s, σ₂.arrs (colName b s) = σ.arrs (colName b s) := fun b s =>
    (harr₂ _ (by simp [colName, klName, String.ext_iff])).trans (harrCol₁ b s)
  have harrMem₂ : ∀ b, σ₂.arrs (memName b) = σ.arrs (memName b) := fun b =>
    (harr₂ _ (by simp [memName, klName, String.ext_iff])).trans (harrMem₁ b)
  have hvarMm₂ : ∀ b, σ₂.vars (mnumName b) = σ.vars (mnumName b) := fun b =>
    (hvar₂ _ (by simp [mnumName, kkName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])).trans
        (hvarMm₁ b)
  have hdata₂ :
      ClusterData n mb j B G A₀ (markSet n Xa) (markSet n Wa) w Alv Gam σ₂ := by
    refine ⟨KillPass.batchData_congr hpre.data.1
      ((harr₂ _ (by simp [cluName, klName, String.ext_iff])).trans
        (harr₁ _ (fun i => by simp [cluName, tabName, String.ext_iff])
          (by rw [cluName]; exact DeadSweep.not_ext_bb_append (p := "clu") rfl (by decide) _)))
      ((harr₂ _ (by simp [batName, klName, String.ext_iff])).trans
        (harr₁ _ (fun i => by simp [batName, tabName, String.ext_iff])
          (not_ext_bb_of_cons₂ (y := batName j)
            (by rw [batName, String.toList_append]; rfl) (by decide))))
      ((harr₂ _ (by simp [resName, klName, String.ext_iff])).trans (harrRes₁ j))
      (harrDepth₂ (j + 1)) (harrGam₂ (j + 1)) (harrMem₂ (j + 1))
      (hvarMm₂ (j + 1)), hpre.data.2⟩
  have hplay₂ : PlayRec B cap G (j + 1) Alv Gam σ₂ :=
    hpre.play.congr
      (fun a _ => (hvar₂ _ (by simp [ctrName, kkName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])).trans
        (hvar₁ _ (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff])
          (hnev _ 'c' ⟨_, by rw [ctrName, String.toList_append]; rfl⟩ (by decide))
          (DeadSweep.not_ext_bb_ctrName a)))
      (fun a _ => harrRes₂ a) (fun a _ => harrGam₂ a) (fun a _ => harrPar₂ a)
  have hsorted₂ :
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
        Xmem asg M σ₂ := by
    have hvarLit (y : String) (hkk : y ≠ "kk") (hkv : y ≠ "kv")
        (hkq : y ≠ kkName j) (hkf : y ≠ "kf") (hkt : y ≠ "kt")
        (hev : ∀ i, y ≠ envName i) (hext : ¬ Ext "bb" y) :
        σ₂.vars y = σ.vars y :=
      (hvar₂ y hkq hkk hkv hkf hkt).trans
        (hvar₁ y hkk hkv hev hext)
    have harrLit (a : String) (hkl : a ≠ klName j)
        (hund : '_' ∉ a.toList) (hbb : ¬ "bb".toList <+: a.toList) :
        σ₂.arrs a = σ.arrs a :=
      (harr₂ a hkl).trans (harr₁ a
        (fun i => RamDriverBase.lit_ne_tabName hund (j + 1) i)
        (not_ext_of_not_prefix hbb))
    refine ⟨hpre.sorted.row,
      (hvarLit "n" (by decide) (by decide) (by simp [kkName, String.ext_iff])
        (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide))).trans hpre.sorted.n_var,
      (hvarLit "qn" (by decide) (by decide) (by simp [kkName, String.ext_iff])
        (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide))).trans hpre.sorted.q_var,
      (hvarLit "c" (by decide) (by decide) (by simp [kkName, String.ext_iff])
        (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide))).trans hpre.sorted.centre_var,
      (hvarLit "xp" (by decide) (by decide) (by simp [kkName, String.ext_iff])
        (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide))).trans hpre.sorted.pointer_var,
      (hvarLit "tail" (by decide) (by decide) (by simp [kkName, String.ext_iff])
        (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide))).trans hpre.sorted.tail_var,
      (hvarLit "rsbits" (by decide) (by decide) (by simp [kkName, String.ext_iff])
        (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide))).trans hpre.sorted.bits_var,
      (harrLit "ord" (by simp [klName, String.ext_iff]) (by decide) (by decide)).trans
        hpre.sorted.centre_arr,
      (harrLit "off" (by simp [klName, String.ext_iff]) (by decide) (by decide)).trans
        hpre.sorted.off_arr,
      (harrLit "tgt" (by simp [klName, String.ext_iff]) (by decide) (by decide)).trans
        hpre.sorted.target_arr,
      (harrLit "alv" (by simp [klName, String.ext_iff]) (by decide) (by decide)).trans
        hpre.sorted.mask_arr,
      (harrLit "xmem" (by simp [klName, String.ext_iff]) (by decide) (by decide)).trans
        hpre.sorted.row_arr,
      hpre.sorted.row_fit,
      (harrLit "asg" (by simp [klName, String.ext_iff]) (by decide) (by decide)).trans
        hpre.sorted.asg_arr,
      ?_, ?_, ?_, hpre.sorted.mask_bound⟩
    · apply Lax3Proofs.Refine.CoverActiveTurn.distClean_of_arrs_eq
        hpre.sorted.dist_clean
      exact harrLit "dist" (by simp [klName, String.ext_iff]) (by decide) (by decide)
    · obtain ⟨Q, hQ⟩ := hpre.sorted.queue_arr
      exact ⟨Q, (harrLit "q" (by simp [klName, String.ext_iff])
        (by decide) (by decide)).trans hQ⟩
    · obtain ⟨QD, hQD⟩ := hpre.sorted.qdist_arr
      exact ⟨QD, (harrLit "qd" (by simp [klName, String.ext_iff])
        (by decide) (by decide)).trans hQD⟩
  have hcolour₂ : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra
      (waCell mb w) σ₂ := by
    have hvarLit (y : String) (hkk : y ≠ "kk") (hkv : y ≠ "kv")
        (hkq : y ≠ kkName j) (hkf : y ≠ "kf") (hkt : y ≠ "kt")
        (hev : ∀ i, y ≠ envName i) (hext : ¬ Ext "bb" y) :
        σ₂.vars y = σ.vars y :=
      (hvar₂ y hkq hkk hkv hkf hkt).trans
        (hvar₁ y hkk hkv hev hext)
    have harrLit (a : String) (hkl : a ≠ klName j)
        (hund : '_' ∉ a.toList) (hbb : ¬ "bb".toList <+: a.toList) :
        σ₂.arrs a = σ.arrs a :=
      (harr₂ a hkl).trans (harr₁ a
        (fun i => RamDriverBase.lit_ne_tabName hund (j + 1) i)
        (not_ext_of_not_prefix hbb))
    exact {
      tail_var := (hvarLit "tail" (by decide) (by decide)
        (by simp [kkName, String.ext_iff]) (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide))).trans
          hpre.colour_state.tail_var
      n_var := (hvarLit "n" (by decide) (by decide)
        (by simp [kkName, String.ext_iff]) (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide))).trans
          hpre.colour_state.n_var
      off_arr := (harrLit "off" (by simp [klName, String.ext_iff])
        (by decide) (by decide)).trans
        hpre.colour_state.off_arr
      target_arr := (harrLit "tgt" (by simp [klName, String.ext_iff])
        (by decide) (by decide)).trans
        hpre.colour_state.target_arr
      target_fit := hpre.colour_state.target_fit
      row_arr := (harrLit "xmem" (by simp [klName, String.ext_iff])
        (by decide) (by decide)).trans
        hpre.colour_state.row_arr
      cluster_arr := by
        rw [harr₂ _ (by simp [cluName, klName, String.ext_iff])]
        exact hclu₁
      retained_arr := by rw [harrRes₂ j]; exact hpre.colour_state.retained_arr
      old_colours := fun s hs => by
        rw [harrCol₂ j s]
        exact hpre.colour_state.old_colours s hs
      batch_arr := by
        rw [harr₂ "wa" (by simp [klName, String.ext_iff])]
        exact hwa₁
      next_slots := fun s hs => by
        obtain ⟨F, hF, hFsup⟩ := hpre.colour_state.next_slots s hs
        exact ⟨F, by rw [harrCol₂ (j + 1) s]; exact hF, hFsup⟩ }
  have hkrows₁ : KillRowsAt q_top cap mb j φ G A₀ Alv
      (markSet n Xa) (markSet n Wa) C' σ₁ := by
    intro i hi Tb hTb v hMv hvX hvW
    obtain ⟨p, hp⟩ : ∃ p : Fin mb, w p = v := by
      have : v ∈ Set.range w := by rw [hpre.data.2]; exact ⟨hvW, hvX⟩
      exact this
    obtain ⟨Tb', hTb', hval'⟩ := hrows₁ i hi
    have hcell : Tb (v : ℕ) = Tb' (v : ℕ) :=
      eq_of_arrOf_eq (hTb.symm.trans hTb') v.isLt
    have hXav : Xa (v : ℕ) ≠ 0 := hvX
    obtain ⟨hb1, hbiff⟩ := hval' p (by rw [hp]; exact hMv)
      (by rw [hp]; exact hXav)
    rw [hp] at hb1 hbiff
    have hdead : Alv (v : ℕ) = 0 := by
      by_contra hc
      exact absurd ((hpre.data.1.2.2.2.2.2.2.1 v).mp hc).2.2 (by simp [hvW])
    refine ⟨by rw [hcell]; exact hb1, ?_⟩
    rw [hcell, hbiff]
    exact (DeadRow.sat_bot_of_dead₁ (G := G) hdead
      (hlocal _ (List.getElem_mem hi))).symm
  have hkrows₂ : KillRowsAt q_top cap mb j φ G A₀ Alv
      (markSet n Xa) (markSet n Wa) C' σ₂ := by
    intro i hi Tb hTb
    exact hkrows₁ i hi Tb (by
      rw [← harr₂ (tabName (j + 1) i)
        (by simp [tabName, klName, String.ext_iff])]
      exact hTb)
  have hklist₂ : KillListAt mb j A₀ (markSet n Xa) (markSet n Wa) σ₂ := by
    obtain ⟨kl, kq, hkl, hkq, hqle, hkln, hinj, hsound, hcomp⟩ := hlist₂
    refine ⟨kl, kq, hkl, hkq, hqle, hkln, hinj, fun e he => ?_, fun v hMv hvX hvW => ?_⟩
    · obtain ⟨hM, hXv, p, hp⟩ := hsound e he
      refine ⟨w p, hp, by rw [hp]; exact hM, ?_, hpre.data.mem_batch p⟩
      change Xa (w p : ℕ) ≠ 0
      rw [hp]
      exact hXv
    · obtain ⟨p, hp⟩ : ∃ p : Fin mb, w p = v := by
        have : v ∈ Set.range w := by rw [hpre.data.2]; exact ⟨hvW, hvX⟩
        exact this
      obtain ⟨e, he, hee⟩ := hcomp p (by rw [hp]; exact hMv)
        (by rw [hp]; exact hvX)
      exact ⟨e, he, by rw [hee, hp]⟩
  have hrun : Run B (streamKillListCom q_top cap mb j φ) σ σ₂
      (killCost q_top cap mb (j + 1) φ + killListCost mb) := by
    rw [streamKillListCom]
    exact hr₁.seq hr₂
  refine ⟨σ₂, _, hrun, ?_, ?_, ?_⟩
  · rfl
  · exact {
      sorted := hsorted₂
      cluster_set := hpre.cluster_set
      data := hdata₂
      supports := hpre.supports
      batch_arr := by
        rw [harr₂ _ (by simp [batName, klName, String.ext_iff])]
        exact harr₁ _ (fun i => by simp [batName, tabName, String.ext_iff])
          (not_ext_bb_of_cons₂ (y := batName j)
            (by rw [batName, String.toList_append]; rfl) (by decide)) |>.trans
              hpre.batch_arr
      wa := by
        change σ₂.arrs "wa" = arrOf mb (waCell mb w)
        rw [harr₂ "wa" (by simp [klName, String.ext_iff])]
        exact clusterWa_eq hwa₁
      play := hplay₂
      colour_state := hcolour₂
      ambient_arr := by rw [harrDepth₂ j]; exact hpre.ambient_arr
      ambient_bound := hpre.ambient_bound
      colour_arr := fun s hs => by rw [harrCol₂ (j + 1) s]; exact hpre.colour_arr s hs
      colour_bit := hpre.colour_bit
      colour_read := hpre.colour_read
      tables := hpre.tables.run hrun
      base_arrs := hpre.base_arrs.run hrun
      kill_rows := hkrows₂
      kill_list := hklist₂ }
  · exact (hr₂.out_eq (RamDriverWrites.noWrite_killListCom mb j)).trans
      (hr₁.out_eq (RamDriverWrites.noWrite_killCom q_top cap mb j φ))

#print axioms streamKillListStep

end Lax3Proofs.Refine.CoverActiveStreamKill
