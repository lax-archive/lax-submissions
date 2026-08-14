import Lax3Proofs.Refine.CoverActiveStreamLifecycle
import Lax3Proofs.Refine.SigmaLoop

/-!
# The streamed active-cover centre loop

This module composes the search/sort half of a streamed centre with its
recursive consume/release/advance lifecycle.  The resulting boundary is the
one used by the counted outer loop: only the progressive cover state and the
already-correct table rows survive between centres.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamLoop

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster (killSet markSet)
open Lax3Proofs.Refine.CoverActiveStream
open Lax3Proofs.Refine.CoverActiveStreamCentre
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.CoverActiveStreamScratch
open Lax3Proofs.Refine.CoverActiveStreamLifecycle
open Lax3Proofs.Refine.CoverActiveStreamPrepare
open Lax3Proofs.Refine.CoverActiveStreamRelease
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.CoverActiveStreamTurn
open Lax3Proofs.Refine.ScatterBlock (renCom_wvars renEnv)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ## The reusable row carries its own CSR budget -/

/-- A sorted streamed row enumerates its mathematical cluster without
duplicates.  Summing the CSR row lengths over its occupied prefix is
therefore bounded by the same `activeBallWeight` that pays the search. -/
theorem streamRow_expandRowSum_le_activeBallWeight
    {q r c tail : ℕ} {G : SimpleGraph (Fin n)} {A₀ : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre O Xmem asg M : ℕ → ℕ}
    (h : StreamRowA G A₀ π centre q r c tail Xmem asg M) :
    Lax3Proofs.RamDriverDescend.expandRowSum O Xmem 0 tail ≤
      Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
        n G A₀ π centre O r c := by
  classical
  let I : Finset ℕ := Finset.range tail
  have hinj : Set.InjOn Xmem (I : Set ℕ) := by
    intro p hp p' hp' heq
    exact h.block_inj p p' (Finset.mem_range.mp hp) (Finset.mem_range.mp hp') heq
  have hsub : I.image Xmem ⊆
      Lax3Proofs.Refine.CoverActiveBudget.activeClusterNat
        G A₀ π centre r c := by
    intro v hv
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hv
    have hp' : p < tail := Finset.mem_range.mp hp
    have hvn : v < n := by simpa [← hpv] using h.mem_lt p hp'
    apply Finset.mem_image.mpr
    refine ⟨⟨v, hvn⟩, ?_, rfl⟩
    apply Lax3Proofs.Refine.CoverActiveBudget.mem_activeClusterFin.mpr
    exact (h.block v).mp ⟨p, hp', hpv⟩
  calc
    Lax3Proofs.RamDriverDescend.expandRowSum O Xmem 0 tail =
        ∑ p ∈ I, Csr.rowLen O (Xmem p) := by
          simp [Lax3Proofs.RamDriverDescend.expandRowSum, I]
    _ = ∑ v ∈ I.image Xmem, Csr.rowLen O v := by
      symm
      exact Finset.sum_image hinj
    _ ≤ ∑ v ∈ Lax3Proofs.Refine.CoverActiveBudget.activeClusterNat
          G A₀ π centre r c, Csr.rowLen O v :=
      Finset.sum_le_sum_of_subset hsub
    _ ≤ Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
          n G A₀ π centre O r c :=
      Lax3Proofs.Refine.CoverActiveBudget.activeClusterNat_rows_le_weight c

/-! ## Frames of the streamed search/sort half -/

private theorem searchSortLogical_var_frame
    {B j cap K : ℕ} {y : String} {σ σ' : Env}
    (hy : y ∉ (streamSearchSortCom cap).wvars)
    (hr : Run B (streamSearchSortAtDepthCom j cap) σ σ' K) :
    σ'.vars y = σ.vars y := by
  apply hr.frame_var
  simpa [streamSearchSortAtDepthCom, streamAtDepthCom] using hy

private theorem searchSortLogical_arr_frame
    {B j cap K : ℕ} {a : String} {σ σ' : Env}
    (ha : streamDepthSwap j a ∉ (streamSearchSortCom cap).warrs)
    (hr : Run B (streamSearchSortAtDepthCom j cap) σ σ' K) :
    σ'.arrs a = σ.arrs a := by
  apply hr.frame_arr
  intro h
  exact ha (Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
    (streamDepthSwap_invol j) _ h)

private theorem wvars_streamSearchSortCom (cap : ℕ) :
    (streamSearchSortCom cap).wvars =
      ["src", "tail", "tail", "head", "sc", "v", "dv", "dn", "j", "jend",
        "w", "tail", "sc", "j", "head", "ri", "u", "du", "ri", "xp", "cvk",
        "cvu", "cvd", "xp", "cvk", "rslo", "rsn", "rsb", "rsw", "rsi",
        "rsv", "rsd", "rsd", "rsw", "rsi", "rsi", "rsv", "rsd", "rsd",
        "rsw", "rsi", "rsi", "rsv", "rsi", "rsb"] := by
  simp [streamSearchSortCom, activeStreamTurnCom, activeStreamSortCom,
    Lax3Proofs.Refine.BfsBlock.bfsBlockCom,
    Lax3Proofs.Refine.BfsBlock.unwind, Lax3Proofs.Refine.BfsBlock.unwindSlot,
    Lax3Proofs.RamBfs.seedSrc, Lax3Proofs.RamBfs.bfsDrain,
    Lax3Proofs.RamBfs.expandRow, Lax3Proofs.RamBfs.scanSlot,
    Fill.put, Csr.loadRow, Csr.scan, Queue.drain,
    Lax3Proofs.Refine.CoverActiveBlock.emitQueueCom,
    Lax3Proofs.Refine.CoverActiveBlock.emitQueueSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixBlockCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixRoundCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixPassCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.stableScatterCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.countZeroCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.countZeroSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.copyBackCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.copyBackSlot, Com.wvars]

private theorem warrs_streamSearchSortCom (cap : ℕ) :
    (streamSearchSortCom cap).warrs =
      ["dist", "q", "dist", "q", "qd", "dist", "dist", "xmem", "asg",
        "alv", "q", "q", "xmem"] := by
  simp [streamSearchSortCom, activeStreamTurnCom, activeStreamSortCom,
    Lax3Proofs.Refine.BfsBlock.bfsBlockCom,
    Lax3Proofs.Refine.BfsBlock.unwind, Lax3Proofs.Refine.BfsBlock.unwindSlot,
    Lax3Proofs.RamBfs.seedSrc, Lax3Proofs.RamBfs.bfsDrain,
    Lax3Proofs.RamBfs.expandRow, Lax3Proofs.RamBfs.scanSlot,
    Fill.put, Csr.loadRow, Csr.scan, Queue.drain,
    Lax3Proofs.Refine.CoverActiveBlock.emitQueueCom,
    Lax3Proofs.Refine.CoverActiveBlock.emitQueueSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixBlockCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixRoundCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixPassCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.stableScatterCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.countZeroCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.countZeroSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.copyBackCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.copyBackSlot, Com.warrs]

/-- Search/sort uses the five arrays owned by the current depth and leaves
the reusable suffix for recursive calls untouched. -/
private theorem streamScratchFrom_run_streamSearchSortAtDepthCom
    {B n cap mb ell j K : ℕ} {σ σ' : Env}
    (h : StreamScratchFrom B n cap mb ell (j + 1) σ)
    (hr : Run B (streamSearchSortAtDepthCom j cap) σ σ' K) :
    StreamScratchFrom B n cap mb ell (j + 1) σ' := by
  have lift {a : String}
      (hswap : streamDepthSwap j a = a)
      (hlogical : a ∉ (streamSearchSortCom cap).warrs) :
      a ∉ (streamSearchSortAtDepthCom j cap).warrs := by
    intro ha
    have hpull := Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
      (streamDepthSwap_invol j) (streamSearchSortCom cap) ha
    rw [hswap] at hpull
    exact hlogical hpull
  apply h.run hr
  · intro d hd _
    have hdj : d ≠ j := by omega
    apply lift (a := cpsName d)
    · apply streamDepthSwap_of_ne
      · simp [cpsName, String.ext_iff]
      · simp [cpsName, ordName, String.ext_iff]
      · simp [cpsName, String.ext_iff]
      · intro he
        exact hdj (Lax3Proofs.RamDriverWrites.cpsName_inj he)
      · simp [cpsName, String.ext_iff]
      · simp [cpsName, xmmName, String.ext_iff]
      · simp [cpsName, String.ext_iff]
      · simp [cpsName, asgName, String.ext_iff]
      · simp [cpsName, String.ext_iff]
      · simp [cpsName, pdsName, balAltName, String.ext_iff]
    · rw [warrs_streamSearchSortCom]
      simp [cpsName, String.ext_iff]
  · intro d _ _
    apply lift (a := cluName d) (by simp)
    rw [warrs_streamSearchSortCom]
    simp [cluName, String.ext_iff]
  · intro d _ _
    apply lift (a := resName d) (by simp)
    rw [warrs_streamSearchSortCom]
    simp [resName, String.ext_iff]
  · intro d _ _
    apply lift (a := batName d) (by simp)
    rw [warrs_streamSearchSortCom]
    simp [batName, String.ext_iff]
  · intro d _ _
    apply lift (a := alvName (d + 1)) (by simp)
    rw [warrs_streamSearchSortCom]
    simp [alvName, String.ext_iff]
  · intro d _ _
    apply lift (a := gamName (d + 1)) (by simp)
    rw [warrs_streamSearchSortCom]
    simp [gamName, String.ext_iff]
  · intro d _ _ s _
    apply lift (a := colName (d + 1) s) (by simp)
    rw [warrs_streamSearchSortCom]
    simp [colName, String.ext_iff]

private theorem belowVar_notMem_wvars_streamSearchSortAtDepthCom
    (j cap : ℕ) {y : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamSearchSortAtDepthCom j cap).wvars := by
  rw [streamSearchSortAtDepthCom, streamAtDepthCom,
    Lax3Proofs.Refine.ScatterBlock.renCom_wvars,
    wvars_streamSearchSortCom]
  intro hy
  have hfixed : ∀ z ∈
      (["src", "tail", "tail", "head", "sc", "v", "dv", "dn", "j", "jend",
        "w", "tail", "sc", "j", "head", "ri", "u", "du", "ri", "xp", "cvk",
        "cvu", "cvd", "xp", "cvk", "rslo", "rsn", "rsb", "rsw", "rsi",
        "rsv", "rsd", "rsd", "rsw", "rsi", "rsi", "rsv", "rsd", "rsd",
        "rsw", "rsi", "rsi", "rsv", "rsi", "rsb"] : List String),
      ¬ Lax3Proofs.RamDriverWrites.HasDigit z := by decide
  exact hfixed y hy (Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h)

set_option maxHeartbeats 2000000 in
private theorem belowArr_notMem_warrs_streamSearchSortAtDepthCom
    (j cap : ℕ) {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamSearchSortAtDepthCom j cap).warrs := by
  intro ha
  have hpull := Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
    (streamDepthSwap_invol j) (streamSearchSortCom cap) ha
  rw [warrs_streamSearchSortCom] at hpull
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpull
  have hpds : a ≠ pdsName j :=
    Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto)
  have hxmm : a ≠ xmmName j :=
    Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto)
  have hasg' : a ≠ asgName j :=
    Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto)
  have hcps : a ≠ cpsName j :=
    Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto)
  rcases hpull with hd | hq | hd | hq | hqd | hd | hd | hx | hasg | halv | hq | hq | hx
  · have he := congrArg (streamDepthSwap j) hd
    have : a = pdsName j := by simpa only [streamDepthSwap_invol,
      streamDepthSwap_dist] using he
    exact hpds this
  · have he := congrArg (streamDepthSwap j) hq
    rw [streamDepthSwap_invol j] at he
    have : a = "q" := by simpa [streamDepthSwap, ordName, cpsName, xmmName,
      asgName, pdsName, balAltName, String.ext_iff] using he
    exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "q")
      (this ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowArr h)
  · have he := congrArg (streamDepthSwap j) hd
    have : a = pdsName j := by simpa only [streamDepthSwap_invol,
      streamDepthSwap_dist] using he
    exact hpds this
  · have he := congrArg (streamDepthSwap j) hq
    rw [streamDepthSwap_invol j] at he
    have : a = "q" := by simpa [streamDepthSwap, ordName, cpsName, xmmName,
      asgName, pdsName, balAltName, String.ext_iff] using he
    exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "q")
      (this ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowArr h)
  · have he := congrArg (streamDepthSwap j) hqd
    rw [streamDepthSwap_invol j] at he
    have : a = "qd" := by simpa [streamDepthSwap, ordName, cpsName, xmmName,
      asgName, pdsName, balAltName, String.ext_iff] using he
    exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "qd")
      (this ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowArr h)
  · have he := congrArg (streamDepthSwap j) hd
    have : a = pdsName j := by simpa only [streamDepthSwap_invol,
      streamDepthSwap_dist] using he
    exact hpds this
  · have he := congrArg (streamDepthSwap j) hd
    have : a = pdsName j := by simpa only [streamDepthSwap_invol,
      streamDepthSwap_dist] using he
    exact hpds this
  · have he := congrArg (streamDepthSwap j) hx
    have : a = xmmName j := by simpa only [streamDepthSwap_invol,
      streamDepthSwap_xmem] using he
    exact hxmm this
  · have he := congrArg (streamDepthSwap j) hasg
    have : a = asgName j := by simpa only [streamDepthSwap_invol,
      streamDepthSwap_asg] using he
    exact hasg' this
  · have he := congrArg (streamDepthSwap j) halv
    have : a = cpsName j := by simpa only [streamDepthSwap_invol,
      streamDepthSwap_alv] using he
    exact hcps this
  · have he := congrArg (streamDepthSwap j) hq
    rw [streamDepthSwap_invol j] at he
    have : a = "q" := by simpa [streamDepthSwap, ordName, cpsName, xmmName,
      asgName, pdsName, balAltName, String.ext_iff] using he
    exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "q")
      (this ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowArr h)
  · have he := congrArg (streamDepthSwap j) hq
    rw [streamDepthSwap_invol j] at he
    have : a = "q" := by simpa [streamDepthSwap, ordName, cpsName, xmmName,
      asgName, pdsName, balAltName, String.ext_iff] using he
    exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "q")
      (this ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowArr h)
  · have he := congrArg (streamDepthSwap j) hx
    have : a = xmmName j := by simpa only [streamDepthSwap_invol,
      streamDepthSwap_xmem] using he
    exact hxmm this

private theorem levelPre_run_streamSearchSortAtDepthCom
    {B cap mb ns nt j K : ℕ} {O T A₀ Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B (streamSearchSortAtDepthCom j cap) σ σ' K) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  have hfvLit (y : String)
      (hy : y ∉ (streamSearchSortCom cap).wvars) :
      y ∉ (streamSearchSortAtDepthCom j cap).wvars := by
    simpa [streamSearchSortAtDepthCom, streamAtDepthCom] using hy
  have hfa (a : String)
      (ha : streamDepthSwap j a ∉ (streamSearchSortCom cap).warrs) :
      a ∉ (streamSearchSortAtDepthCom j cap).warrs := by
    intro hw
    exact ha (Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
      (streamDepthSwap_invol j) _ hw)
  apply Lax3Proofs.RamDriverCompose.levelPre_run hp hr
  · apply hfvLit
    rw [wvars_streamSearchSortCom]
    decide
  · apply hfvLit
    rw [wvars_streamSearchSortCom]
    decide
  · apply hfvLit
    rw [wvars_streamSearchSortCom]
    decide
  · apply hfa
    rw [warrs_streamSearchSortCom]
    simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, pdsName,
      balAltName, String.ext_iff]
  · apply hfa
    rw [warrs_streamSearchSortCom]
    simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, pdsName,
      balAltName, String.ext_iff]
  · apply hfa
    rw [streamDepthSwap_alvName]
    rw [warrs_streamSearchSortCom]
    simp [alvName, cpsName, String.ext_iff]
  · apply hfa
    rw [streamDepthSwap_gamName]
    rw [warrs_streamSearchSortCom]
    simp [gamName, String.ext_iff]
  · intro s
    apply hfa
    rw [streamDepthSwap_colName]
    rw [warrs_streamSearchSortCom]
    simp [colName, String.ext_iff]
  · intro a ha
    simp only [Lax3Proofs.RamDriverCompose.zeroArrs, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply hfa <;> rw [warrs_streamSearchSortCom] <;>
      simp [streamDepthSwap, ordName, cpsName, xmmName, asgName, pdsName,
        balAltName, String.ext_iff]
  · apply hfa
    rw [streamDepthSwap_memName]
    rw [warrs_streamSearchSortCom]
    simp [memName, String.ext_iff]
  · apply hfvLit
    rw [wvars_streamSearchSortCom]
    intro hm
    have hfixed : ∀ z ∈
        (["src", "tail", "tail", "head", "sc", "v", "dv", "dn", "j", "jend",
          "w", "tail", "sc", "j", "head", "ri", "u", "du", "ri", "xp", "cvk",
          "cvu", "cvd", "xp", "cvk", "rslo", "rsn", "rsb", "rsw", "rsi",
          "rsv", "rsd", "rsd", "rsw", "rsi", "rsi", "rsv", "rsd", "rsd",
          "rsw", "rsi", "rsi", "rsv", "rsi", "rsb"] : List String),
        ¬ Lax3Proofs.RamDriverWrites.HasDigit z := by decide
    exact hfixed _ hm (Lax3Proofs.RamDriverWrites.hasDigit_mnumName j)

private theorem playRec_run_streamSearchSortAtDepthCom
    {B cap j K : ℕ} {G : SimpleGraph (Fin n)} {A₀ Gm : ℕ → ℕ}
    {σ σ' : Env}
    (hp : PlayRec B cap G j A₀ Gm σ)
    (hr : Run B (streamSearchSortAtDepthCom j cap) σ σ' K) :
    PlayRec B cap G j A₀ Gm σ' := by
  apply hp.congr
  · intro a ha
    exact hr.frame_var _
      (belowVar_notMem_wvars_streamSearchSortAtDepthCom j cap
        ⟨a, ha, Or.inl rfl⟩)
  · intro a ha
    exact hr.frame_arr _
      (belowArr_notMem_warrs_streamSearchSortAtDepthCom j cap
        ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)
  · intro a ha
    exact hr.frame_arr _
      (belowArr_notMem_warrs_streamSearchSortAtDepthCom j cap
        ⟨a, ha, Or.inr (Or.inl rfl)⟩)
  · intro a ha
    exact hr.frame_arr _
      (belowArr_notMem_warrs_streamSearchSortAtDepthCom j cap
        ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)

/-! A pulled-back size clause survives an arbitrary physical run: the
renaming changes which array is named, while a run preserves that array's
length. -/
private theorem sized_renEnv_run
    {B K : ℕ} {f : String → String} {l : List (String × ℕ)}
    {cmd : Com} {σ σ' : Env}
    (h : Sized l (renEnv f σ)) (hr : Run B cmd σ σ' K) :
    Sized l (renEnv f σ') := by
  intro p hp
  apply exists_arrOf
  exact (run_length_arrs hr (f p.1)).trans (h.length hp)

/-! The physical parent level and the entering pulled-back level together
reconstruct the pulled-back level after any run.  Semantic arrays and the
ordering scratch come from the physical postcondition (the swap fixes those
names); length and word clauses for the five exchanged scratch arrays cross
the run directly. -/
theorem levelPre_renEnv_streamDepthSwap_after_run
    {B cap mb ns nt j K : ℕ} {O T A₀ Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {cmd : Com} {σ σ' : Env}
    (hlog : LevelPre B n cap mb ns nt O T j A₀ Gm C
      (renEnv (streamDepthSwap j) σ))
    (hphys : LevelPre B n cap mb ns nt O T j A₀ Gm C σ')
    (hr : Run B cmd σ σ' K) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C
      (renEnv (streamDepthSwap j) σ') := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hlevelMem₀, hdepthMem₀,
    -, -, -, -, -⟩ := hlog
  obtain ⟨hn, hoff, htgt, halv, hgam, hcol, hA₀B, hGmB, hCbit,
    -, -, hm, horder, hpad, htB, hmember⟩ := hphys
  have hlevelMem : LevelMem B n cap mb
      (renEnv (streamDepthSwap j) σ') := by
    refine ⟨sized_renEnv_run hlevelMem₀.1 hr, ?_, ?_⟩
    · have h₀ : ∀ v ∈ σ.arrs (streamDepthSwap j "dist"), v < B := by
        simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs] using hlevelMem₀.2.1
      simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs] using
        (run_mem_arrs_lt hr (streamDepthSwap j "dist") h₀)
    · have h₀ : ∀ v ∈ σ.arrs (streamDepthSwap j "q"), v < B := by
        simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs] using hlevelMem₀.2.2
      simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs] using
        (run_mem_arrs_lt hr (streamDepthSwap j "q") h₀)
  have hdepthMem : DepthMem n cap mb
      (renEnv (streamDepthSwap j) σ') := by
    intro d
    refine ⟨sized_renEnv_run (hdepthMem₀ d).1 hr, ?_⟩
    intro c hc
    obtain ⟨g, hg⟩ := (hdepthMem₀ d).2 c hc
    apply exists_arrOf
    exact (run_length_arrs hr (streamDepthSwap j (colName d c))).trans
      (by rw [← Lax3Proofs.Refine.ScatterBlock.renEnv_arrs, hg, length_arrOf])
  have horder' : OrderMem B n ns nt
      (renEnv (streamDepthSwap j) σ') := by
    simpa [OrderMem, Sized, Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      Lax3Proofs.Refine.ScatterBlock.renEnv_vars, streamDepthSwap, ordName,
      cpsName, xmmName, asgName, pdsName, balAltName, String.ext_iff] using horder
  refine ⟨by simpa using hn, ?_, ?_, ?_, ?_, ?_, hA₀B, hGmB, hCbit,
    hlevelMem, hdepthMem, by simpa using hm, horder', hpad, htB, ?_⟩
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

private theorem playRec_renEnv_streamDepthSwap
    {B cap j : ℕ} {G : SimpleGraph (Fin n)} {A₀ Gm : ℕ → ℕ} {σ : Env}
    (h : PlayRec B cap G j A₀ Gm σ) :
    PlayRec B cap G j A₀ Gm (renEnv (streamDepthSwap j) σ) := by
  apply h.congr
  · intro a ha
    simp only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars]
  · intro a ha
    simp only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_resName]
  · intro a ha
    simp only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_gamName]
  · intro a ha
    simp only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_parName]

theorem tablesSized_renEnv_run
    {B q_top cap mb n K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {f : String → String} {cmd : Com} {σ σ' : Env}
    (h : TablesSized q_top cap mb φ n (renEnv f σ))
    (hr : Run B cmd σ σ' K) :
    TablesSized q_top cap mb φ n (renEnv f σ') :=
  fun d => sized_renEnv_run (h d) hr

theorem baseArrs_renEnv_run
    {B q_top cap mb ell K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {f : String → String} {cmd : Com} {σ σ' : Env}
    (h : BaseArrs B q_top cap mb ell φ (renEnv f σ))
    (hr : Run B cmd σ σ' K) :
    BaseArrs B q_top cap mb ell φ (renEnv f σ') := by
  refine ⟨sized_renEnv_run h.1 hr, ?_⟩
  intro jd i hi
  apply botMem_of_length (σ := renEnv f σ)
    (σ' := renEnv f σ') (fun a => ?_) _ "bb" (h.2 jd i hi)
  exact run_length_arrs hr (f a)

private theorem noWrite_streamSearchSortCom (cap : ℕ) :
    (streamSearchSortCom cap).NoWrite := by
  simp [streamSearchSortCom, activeStreamTurnCom, activeStreamSortCom,
    Lax3Proofs.Refine.BfsBlock.bfsBlockCom,
    Lax3Proofs.Refine.BfsBlock.unwind, Lax3Proofs.Refine.BfsBlock.unwindSlot,
    Lax3Proofs.RamBfs.seedSrc, Lax3Proofs.RamBfs.bfsDrain,
    Lax3Proofs.RamBfs.expandRow, Lax3Proofs.RamBfs.scanSlot,
    Fill.put, Csr.loadRow, Csr.scan, Queue.drain,
    Lax3Proofs.Refine.CoverActiveBlock.emitQueueCom,
    Lax3Proofs.Refine.CoverActiveBlock.emitQueueSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixBlockCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixRoundCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixPassCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.stableScatterCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.countZeroCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.countZeroSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitSlot,
    Lax3Proofs.Refine.CoverActiveRadixPass.copyBackCom,
    Lax3Proofs.Refine.CoverActiveRadixPass.copyBackSlot, Com.NoWrite]

private theorem noWrite_streamSearchSortAtDepthCom (j cap : ℕ) :
    (streamSearchSortAtDepthCom j cap).NoWrite := by
  exact Lax3Proofs.Refine.ScatterBlock.renCom_noWrite _
    (noWrite_streamSearchSortCom cap)

/-! ## The stable boundary and one fused turn -/

/-- Everything needed at the boundary between two streamed centres.  The
pulled-back level clauses are retained explicitly because the next preparation
runs over the depth-owned view, while the physical clauses are the recursive
driver's public interface. -/
structure StreamStableState
    (B n q_top cap mb ns nt q j c bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (σ : Env) : Prop where
  turn : StreamTurnState B ns nt (n * n) q cap c G A₀ π centre O T
    Xmem asg M (renEnv (streamDepthSwap j) σ)
  bits_var : (renEnv (streamDepthSwap j) σ).vars "rsbits" = bits
  level : LevelPre B n cap mb ns nt O T j A₀ Gm C σ
  logical_level : LevelPre B n cap mb ns nt O T j A₀ Gm C
    (renEnv (streamDepthSwap j) σ)
  play : PlayRec B cap G j A₀ Gm σ
  logical_tables : TablesSized q_top cap mb φ n
    (renEnv (streamDepthSwap j) σ)
  tables : TablesSized q_top cap mb φ n σ
  logical_base : BaseArrs B q_top cap mb ell φ
    (renEnv (streamDepthSwap j) σ)
  base_arrs : BaseArrs B q_top cap mb ell φ σ
  cluster_zero : σ.arrs (cluName j) = arrOf n (fun _ => 0)
  retained_zero : σ.arrs (resName j) = arrOf n (fun _ => 0)
  batch_zero : σ.arrs (batName j) = arrOf n (fun _ => 0)
  child_zero : σ.arrs (alvName (j + 1)) = arrOf n (fun _ => 0)
  game_zero : σ.arrs (gamName (j + 1)) = arrOf n (fun _ => 0)
  colours_zero : ∀ s, s < sigL cap mb (j + 1) →
    σ.arrs (colName (j + 1) s) = arrOf n (fun _ => 0)
  scratch : StreamScratchFrom B n cap mb ell (j + 1) σ

/-- Search and sort a centre, consume it recursively, release its scratch,
and advance to the next centre. -/
noncomputable def streamCentreTurnCom
    (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) (inner : Com) : Com :=
  .seq (streamSearchSortAtDepthCom j cap)
    (streamCentreLifecycleCom q_top cap mb j φ inner)

structure StreamCentreTurnOut
    (B n q_top cap mb ns nt q j c bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (σ₀ σ : Env) : Prop where
  stable : StreamStableState B n q_top cap mb ns nt q j (c + 1) bits ell φ G
    A₀ π centre O T Xmem asg M Gm C σ
  out_eq : σ.out = σ₀.out
  table_step : ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
    ∃ Tb Tb₀ : ℕ → ℕ,
      σ.arrs (tabName j i) = arrOf n Tb ∧
      σ₀.arrs (tabName j i) = arrOf n Tb₀ ∧
      (∀ v : Fin n, A₀ (v : ℕ) = 0 ∨ asg (v : ℕ) ≠ c →
        Tb (v : ℕ) = Tb₀ (v : ℕ)) ∧
      ∀ v : Fin n, A₀ (v : ℕ) ≠ 0 → asg (v : ℕ) = c →
        Tb (v : ℕ) ≤ 1 ∧
        (Tb (v : ℕ) ≠ 0 ↔
          Sat (Lax3Proofs.RamBfs.masked G A₀)
            (colRead n C (sigL cap mb j)) (fun _ => v)
            (tablesAt q_top cap mb φ j)[i])

open Classical in
/-- **One repeatable streamed centre turn.**  Search/sort and the complete
recursive lifecycle compose without materialising an accumulated cover.  The
only abstract cost input is a uniform ceiling for the lifecycle of any row
the search can emit within its advertised vertex budget. -/
theorem streamCentreTurnStep
    {B n q_top cap mb ns nt q j c bits ell Kinner : ℕ}
    {searchBw searchNb Kb Ki Kscatter Klife d : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {A : Finset ℕ} {inner : Com}
    (hchild : ∀ (Xa Ra Wa Alv Gam : ℕ → ℕ)
        (C' : ℕ → ℕ → ℕ) (w : Fin mb → Fin n),
      Lax3Proofs.Refine.MassWeight.arenaWeight n G Alv ≤
          Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
            n G A₀ π centre O cap c →
      Lax3Proofs.Refine.CoverActiveStreamInner.StreamLevelImplementsD
        B q_top cap mb ns nt ell j φ G O T Alv Gam C'
          (killSet A₀ (markSet n Xa) (markSet n Wa)) inner Kinner)
    (hframes : Lax3Proofs.Refine.CoverActiveStreamInner.StreamInnerFrames j inner)
    (hcap : cap = rhoMinus 0 q_top)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T) (hnt : ns ≤ nt)
    (hB : WordBoundK B n d ns cap mb)
    (hcentres : Lax3Proofs.RamCoverActive.CentresBy n q A₀ π centre)
    (hmb : mb = ell * (2 * cap + 1)) (hjl : j < ell)
    (hbitsB : bits < B) (hpow : n ≤ 2 ^ bits)
    (hbitsEq : bits = Nat.clog 2 n)
    (hA : ∀ v, v < n → M v ≠ 0 →
      Lax3Proofs.RamBfs.WD G M (2 * cap) (centre c) v → v ∈ A)
    (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ searchBw)
    (hnb : A.card ≤ searchNb)
    (hbnd : ∀ (Xa : ℕ → ℕ) β,
        β ∈ tablesAt q_top cap mb φ j →
      ∀ s ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        (markSet n Xa).ncard ≤
            Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap c →
          s.r + 1 < B ∧ s.t + n + mb < B ∧
          Lax3Proofs.Refine.ScatterDeadTurn.deadAtomKX s.β n
            (markSet n Xa).ncard mb
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap c)
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap c) s.t ≤ Kb)
    (hcost : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hK : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Kscatter)
    (hlife : ∀ (tail : ℕ) (Xm am Mm : ℕ → ℕ), tail ≤ searchNb →
      Lax3Proofs.RamDriverDescend.expandRowSum O Xm 0 tail ≤
          Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
            n G A₀ π centre O cap c →
      streamCentreLifecycleCost q_top cap mb j tail
        (Lax3Proofs.RamDriverDescend.expandRowSum O Xm 0 tail)
        (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
          n G A₀ π centre O cap c) Kinner Kscatter φ ≤ Klife) :
    Spec B
      (fun σ =>
        StreamStableState B n q_top cap mb ns nt q j c bits ell φ G A₀ π
          centre O T Xmem asg M Gm C σ ∧ c < q)
      (streamCentreTurnCom q_top cap mb j φ inner)
      (fun σ σ' => ∃ tail Xmem' asg' M', tail ≤ searchNb ∧
        StreamCentreTurnOut B n q_top cap mb ns nt q j c bits ell φ G A₀ π
          centre O T Xmem' asg' M' Gm C σ σ')
      (streamSearchSortCost bits searchBw searchNb + Klife) := by
  refine Spec.of_exists fun σ hpre => ?_
  have hnB : n < B := hB.n_lt
  have hnsB : ns < B := hB.ns_lt
  have hqB : q < B := lt_of_le_of_lt hcentres.count_le hnB
  have hrB : 2 * cap + 1 < B := by
    have := hB.arena
    omega
  obtain ⟨σ₁, hr₁, tail, Xmem₁, asg₁, M₁, htail, hsorted₁⟩ :=
    (streamSearchSortAtDepthStep hcentres hcsr.csr hnB hnsB hnt hqB hrB
      hbitsB hpow hA hbw hnb).run
      ⟨hpre.1.turn, hpre.2, hpre.1.bits_var⟩
  have hlevel₁ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₁ :=
    levelPre_run_streamSearchSortAtDepthCom hpre.1.level hr₁
  have hlogicalLevel₁ : LevelPre B n cap mb ns nt O T j A₀ Gm C
      (renEnv (streamDepthSwap j) σ₁) :=
    levelPre_renEnv_streamDepthSwap_after_run hpre.1.logical_level hlevel₁ hr₁
  have hplay₁ : PlayRec B cap G j A₀ Gm σ₁ :=
    playRec_run_streamSearchSortAtDepthCom hpre.1.play hr₁
  have hlogicalPlay₁ : PlayRec B cap G j A₀ Gm
      (renEnv (streamDepthSwap j) σ₁) :=
    playRec_renEnv_streamDepthSwap hplay₁
  have htables₁ : TablesSized q_top cap mb φ n σ₁ := hpre.1.tables.run hr₁
  have hlogicalTables₁ : TablesSized q_top cap mb φ n
      (renEnv (streamDepthSwap j) σ₁) :=
    tablesSized_renEnv_run hpre.1.logical_tables hr₁
  have hbase₁ : BaseArrs B q_top cap mb ell φ σ₁ := hpre.1.base_arrs.run hr₁
  have hscratch₁ : StreamScratchFrom B n cap mb ell (j + 1) σ₁ :=
    streamScratchFrom_run_streamSearchSortAtDepthCom hpre.1.scratch hr₁
  have hlogicalBase₁ : BaseArrs B q_top cap mb ell φ
      (renEnv (streamDepthSwap j) σ₁) :=
    baseArrs_renEnv_run hpre.1.logical_base hr₁
  have hfa (a : String)
      (ha : streamDepthSwap j a ∉ (streamSearchSortCom cap).warrs) :
      σ₁.arrs a = σ.arrs a := searchSortLogical_arr_frame ha hr₁
  have hclu₁ : σ₁.arrs (cluName j) = arrOf n (fun _ => 0) := by
    have hnwrite : streamDepthSwap j (cluName j) ∉
        (streamSearchSortCom cap).warrs := by
      rw [streamDepthSwap_cluName, warrs_streamSearchSortCom]
      simp [cluName, String.ext_iff]
    rw [hfa _ hnwrite]
    exact hpre.1.cluster_zero
  have hres₁ : σ₁.arrs (resName j) = arrOf n (fun _ => 0) := by
    have hnwrite : streamDepthSwap j (resName j) ∉
        (streamSearchSortCom cap).warrs := by
      rw [streamDepthSwap_resName, warrs_streamSearchSortCom]
      simp [resName, String.ext_iff]
    rw [hfa _ hnwrite]
    exact hpre.1.retained_zero
  have hbat₁ : σ₁.arrs (batName j) = arrOf n (fun _ => 0) := by
    have hnwrite : streamDepthSwap j (batName j) ∉
        (streamSearchSortCom cap).warrs := by
      rw [streamDepthSwap_batName, warrs_streamSearchSortCom]
      simp [batName, String.ext_iff]
    rw [hfa _ hnwrite]
    exact hpre.1.batch_zero
  have halv₁ : σ₁.arrs (alvName (j + 1)) = arrOf n (fun _ => 0) := by
    have hnwrite : streamDepthSwap j (alvName (j + 1)) ∉
        (streamSearchSortCom cap).warrs := by
      rw [streamDepthSwap_alvName, warrs_streamSearchSortCom]
      simp [alvName, String.ext_iff]
    rw [hfa _ hnwrite]
    exact hpre.1.child_zero
  have hgam₁ : σ₁.arrs (gamName (j + 1)) = arrOf n (fun _ => 0) := by
    have hnwrite : streamDepthSwap j (gamName (j + 1)) ∉
        (streamSearchSortCom cap).warrs := by
      rw [streamDepthSwap_gamName, warrs_streamSearchSortCom]
      simp [gamName, String.ext_iff]
    rw [hfa _ hnwrite]
    exact hpre.1.game_zero
  have hcol₁ : ∀ s, s < sigL cap mb (j + 1) →
      σ₁.arrs (colName (j + 1) s) = arrOf n (fun _ => 0) := by
    intro s hs
    have hnwrite : streamDepthSwap j (colName (j + 1) s) ∉
        (streamSearchSortCom cap).warrs := by
      rw [streamDepthSwap_colName, warrs_streamSearchSortCom]
      simp [colName, String.ext_iff]
    rw [hfa _ hnwrite]
    exact hpre.1.colours_zero s hs
  have hprepare₁ : StreamPreparePre B q_top cap mb ns nt (n * n) q j c tail
      bits ell φ G A₀ π centre O T Xmem₁ asg₁ M₁ Gm C
        (renEnv (streamDepthSwap j) σ₁) := {
    sorted := hsorted₁
    level := hlogicalLevel₁
    play := hlogicalPlay₁
    cluster_zero := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_cluName] using hclu₁
    retained_zero := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_resName] using hres₁
    batch_zero := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_batName] using hbat₁
    child_zero := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_alvName] using halv₁
    game_zero := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_gamName] using hgam₁
    next_colours_zero := fun s hs => by
      simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
        streamDepthSwap_colName] using hcol₁ s hs
    tables := hlogicalTables₁
    base_arrs := hlogicalBase₁ }
  obtain ⟨σ₂, hr₂, hout₂⟩ :=
    (streamCentreLifecycleStep hchild hframes hcap hcsr hnt hB hcentres hmb hjl
      hbitsB hpow hbitsEq hbnd hcost hK).run
      ⟨hprepare₁, hlevel₁, htables₁, hbase₁, hscratch₁⟩
  have hrowMass := streamRow_expandRowSum_le_activeBallWeight
    (O := O) hsorted₁.row
  have hrall := hr₁.seq hr₂
  have hrun : Run B (streamCentreTurnCom q_top cap mb j φ inner) σ σ₂
      (streamSearchSortCost bits searchBw searchNb + Klife) := by
    apply (hr₁.seq hr₂).mono
    exact Nat.add_le_add_left (hlife tail Xmem₁ asg₁ M₁ htail hrowMass) _
  refine ⟨σ₂, _, ?_, le_rfl, tail, Xmem₁, asg₁, M₁, htail, {
    stable := {
      turn := hout₂.turn
      bits_var := hout₂.bits_var
      level := hout₂.level
      logical_level := levelPre_renEnv_streamDepthSwap_after_run
        hpre.1.logical_level hout₂.level hrall
      play := hout₂.play
      logical_tables := tablesSized_renEnv_run hpre.1.logical_tables hrall
      tables := hout₂.tables
      logical_base := baseArrs_renEnv_run hpre.1.logical_base hrall
      base_arrs := hout₂.base_arrs
      cluster_zero := hout₂.cluster_zero
      retained_zero := hout₂.retained_zero
      batch_zero := hout₂.batch_zero
      child_zero := hout₂.child_zero
      game_zero := hout₂.game_zero
      colours_zero := hout₂.colours_zero
      scratch := hout₂.scratch }
    out_eq := hout₂.out_eq.trans
      (hr₁.out_eq (noWrite_streamSearchSortAtDepthCom j cap))
    table_step := ?_ }⟩
  · simpa [streamCentreTurnCom] using hrun
  · intro i hi
    obtain ⟨Tb, Tb₀, hTb, hTb₀, hkeep, hsem⟩ := hout₂.table_step i hi
    refine ⟨Tb, Tb₀, hTb, ?_, hkeep, hsem⟩
    have htab : σ₁.arrs (tabName j i) = σ.arrs (tabName j i) :=
      searchSortLogical_arr_frame (hr := hr₁) (by
        rw [streamDepthSwap_tabName]
        rw [warrs_streamSearchSortCom]
        simp [tabName, String.ext_iff])
    exact htab.symm.trans hTb₀

/-! ## The counted streamed loop -/

def streamDone (A₀ asg : ℕ → ℕ) (c : ℕ) : Set (Fin n) :=
  {v | A₀ (v : ℕ) ≠ 0 ∧ asg (v : ℕ) < c}

/-- The existential streamed data changes at every centre, while the parent
level, output tape, and correctness of all earlier rows persist. -/
def StreamLoopInv
    (B n q_top cap mb ns nt q j bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (D : Set (Fin n)) (outs : List ℕ) (σ : Env) : Prop :=
  ∃ Xmem asg M : ℕ → ℕ,
    StreamStableState B n q_top cap mb ns nt q j (σ.vars "c") bits ell
      φ G A₀ π centre O T Xmem asg M Gm C σ ∧
    σ.out = outs ∧
    TableInvOn q_top cap mb φ G j A₀ C
      (D ∪ streamDone A₀ asg (σ.vars "c")) σ

def StreamLoopOut
    (B n q_top cap mb ns nt q j bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (D : Set (Fin n)) (σ₀ σ : Env) : Prop :=
  ∃ Xmem asg M : ℕ → ℕ,
    StreamStableState B n q_top cap mb ns nt q j q bits ell φ G A₀ π
      centre O T Xmem asg M Gm C σ ∧
    TableInvOn q_top cap mb φ G j A₀ C
      ({v : Fin n | A₀ (v : ℕ) ≠ 0} ∪ D) σ ∧
    σ.out = σ₀.out

noncomputable def streamCentreLoopCom
    (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) (inner : Com) : Com :=
  .seq (.assign "c" (.lit 0))
    (.while (.lt (.var "c") (.var "qn"))
      (streamCentreTurnCom q_top cap mb j φ inner))

/-- The counted streamed loop inherits the recursive command's depth
discipline and writes no array owned by a shallower level. -/
theorem belowArr_notMem_warrs_streamCentreLoopCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {inner : Com}
    {a : String}
    (hinner : ∀ a, Lax3Proofs.RamDriverWrites.BelowArr (j + 1) a →
      a ∉ inner.warrs)
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamCentreLoopCom q_top cap mb j phi inner).warrs := by
  intro hm
  simp only [streamCentreLoopCom, streamCentreTurnCom, Com.warrs,
    List.mem_append, List.not_mem_nil, false_or] at hm
  rcases hm with hm | hm
  · exact (belowArr_notMem_warrs_streamSearchSortAtDepthCom j cap h) hm
  · exact (belowArr_notMem_warrs_streamCentreLifecycleCom
      q_top cap mb j phi hinner h) hm

/-- Scalar counterpart of `belowArr_notMem_warrs_streamCentreLoopCom`. -/
theorem belowVar_notMem_wvars_streamCentreLoopCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {inner : Com}
    {y : String}
    (hinner : ∀ y, Lax3Proofs.RamDriverWrites.BelowVar (j + 1) y →
      y ∉ inner.wvars)
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamCentreLoopCom q_top cap mb j phi inner).wvars := by
  intro hm
  simp only [streamCentreLoopCom, streamCentreTurnCom, Com.wvars,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hc | hm | hm
  · have hd := Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h
    exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "c") (hc ▸ hd)
  · exact (belowVar_notMem_wvars_streamSearchSortAtDepthCom j cap h) hm
  · exact (belowVar_notMem_wvars_streamCentreLifecycleCom
      q_top cap mb j phi hinner h) hm

open Classical in
/-- **The whole streamed centre loop.**  The Σ-shaped loop rule charges each
centre its own mathematical cluster weight and its own recursive lifecycle
budget.  At exit every live row is correct, while the caller's dead domain is
preserved. -/
theorem streamCentreLoopStep
    {B n q_top cap mb ns nt q j bits ell : ℕ} {Kinner : ℕ → ℕ}
    {Kb Ki Kscatter Klife : ℕ → ℕ} {d : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {D : Set (Fin n)} {inner : Com}
    (hchild : ∀ k, k < q → ∀ (Xa Ra Wa Alv Gam : ℕ → ℕ)
        (C' : ℕ → ℕ → ℕ) (w : Fin mb → Fin n),
      Lax3Proofs.Refine.MassWeight.arenaWeight n G Alv ≤
          Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
            n G A₀ π centre O cap k →
      Lax3Proofs.Refine.CoverActiveStreamInner.StreamLevelImplementsD
        B q_top cap mb ns nt ell j φ G O T Alv Gam C'
          (killSet A₀ (markSet n Xa) (markSet n Wa)) inner (Kinner k))
    (hframes : Lax3Proofs.Refine.CoverActiveStreamInner.StreamInnerFrames j inner)
    (hcap : cap = rhoMinus 0 q_top)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T) (hnt : ns ≤ nt)
    (hB : WordBoundK B n d ns cap mb)
    (hcentres : Lax3Proofs.RamCoverActive.CentresBy n q A₀ π centre)
    (hmb : mb = ell * (2 * cap + 1)) (hjl : j < ell)
    (hbitsB : bits < B) (hpow : n ≤ 2 ^ bits)
    (hbitsEq : bits = Nat.clog 2 n)
    (hbnd : ∀ k < q, ∀ (Xa : ℕ → ℕ) β,
        β ∈ tablesAt q_top cap mb φ j →
      ∀ s ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        (markSet n Xa).ncard ≤
            Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap k →
          s.r + 1 < B ∧ s.t + n + mb < B ∧
          Lax3Proofs.Refine.ScatterDeadTurn.deadAtomKX s.β n
            (markSet n Xa).ncard mb
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap k)
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap k) s.t ≤ Kb k)
    (hcost : ∀ k < q, ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb k * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki k)
    (hK : ∀ k < q,
      Ki k * (tablesAt q_top cap mb φ j).length + 1 ≤ Kscatter k)
    (hlife : ∀ k < q, ∀ (tail : ℕ) (Xm am Mm : ℕ → ℕ),
      tail ≤ Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
        n G A₀ π centre O cap k →
      Lax3Proofs.RamDriverDescend.expandRowSum O Xm 0 tail ≤
          Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
            n G A₀ π centre O cap k →
      streamCentreLifecycleCost q_top cap mb j tail
        (Lax3Proofs.RamDriverDescend.expandRowSum O Xm 0 tail)
        (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
          n G A₀ π centre O cap k) (Kinner k) (Kscatter k) φ ≤ Klife k)
    (hDdead : ∀ v : Fin n, v ∈ D → A₀ (v : ℕ) = 0) :
    Spec B
      (fun σ => StreamLoopInv B n q_top cap mb ns nt q j bits ell φ G A₀ π
        centre O T Gm C D σ.out (σ.setVar "c" 0))
      (streamCentreLoopCom q_top cap mb j φ inner)
      (StreamLoopOut B n q_top cap mb ns nt q j bits ell φ G A₀ π centre O T
        Gm C D)
      ((∑ k ∈ Finset.range q,
        (streamSearchSortCost bits
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap k)
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap k) + Klife k + 4)) + 6) := by
  refine Spec.of_exists fun σ hstart => ?_
  let W : ℕ → ℕ := fun k =>
    Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
      n G A₀ π centre O cap k
  let I : Env → Prop := StreamLoopInv B n q_top cap mb ns nt q j bits ell φ G A₀ π
    centre O T Gm C D σ.out
  have hqB : q < B := lt_of_le_of_lt hcentres.count_le hB.n_lt
  have hbody : ∀ k, k < q → Spec B
      (fun τ => I τ ∧ τ.vars "c" = k)
      (streamCentreTurnCom q_top cap mb j φ inner)
      (fun _ τ' => I τ' ∧ τ'.vars "c" = k + 1)
      (streamSearchSortCost bits (W k) (W k) + Klife k) := by
    intro k hk
    refine Spec.of_exists fun τ hτ => ?_
    obtain ⟨hI, hck⟩ := hτ
    obtain ⟨Xm, am, Mm, hstable, hout, htab⟩ := hI
    have hstableK : StreamStableState B n q_top cap mb ns nt q j k bits ell
        φ G A₀ π centre O T Xm am Mm Gm C τ := by
      simpa [hck] using hstable
    obtain ⟨A, hA, hAw, hAn⟩ :=
      (Lax3Proofs.Refine.CoverActiveBudget.activeBallBudget hcentres)
        k hk Mm hstableK.turn.state.mask
    obtain ⟨τ', hr, tail, Xm', am', Mm', htail, hturn⟩ :=
      (streamCentreTurnStep (searchBw := W k) (searchNb := W k)
        (Kb := Kb k) (Ki := Ki k) (Kscatter := Kscatter k)
        (hchild k hk) hframes hcap hcsr hnt hB hcentres hmb hjl hbitsB
        hpow hbitsEq hA hAw hAn (hbnd k hk) (hcost k hk) (hK k hk)
        (fun tail X a M ht hm => hlife k hk tail X a M ht hm)).run
        ⟨hstableK, hk⟩
    have hcnext : τ'.vars "c" = k + 1 := by
      simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using
        hturn.stable.turn.centre_var
    have htable' : TableInvOn q_top cap mb φ G j A₀ C
        (D ∪ streamDone A₀ am' (τ'.vars "c")) τ' := by
      intro i hi
      obtain ⟨Told, hTold, hbitOld, hvalOld⟩ := htab i hi
      obtain ⟨Tnew, Tpre, hTnew, hTpre, hkeep, hsem⟩ := hturn.table_step i hi
      refine ⟨Tnew, hTnew, ?_, ?_⟩
      · intro v hv
        rcases hv with hvD | ⟨halive, hlt⟩
        · have hsame := hkeep v (Or.inl (hDdead v hvD))
          have heq : Tpre (v : ℕ) = Told (v : ℕ) :=
            Lax3Proofs.RamDriverCluster.eq_of_arrOf_eq
              (hTpre.symm.trans hTold) v.isLt
          rw [hsame, heq]
          exact hbitOld v (Or.inl hvD)
        · rw [hcnext] at hlt
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hbefore | hcur
          · have hasgeq := CoverPrefixA.assignment_eq_of_lt
              hstableK.turn.state hturn.stable.turn.state (v : ℕ) v.isLt
                halive hbefore
            have hne : am' (v : ℕ) ≠ k := by omega
            have hsame := hkeep v (Or.inr hne)
            have heq : Tpre (v : ℕ) = Told (v : ℕ) :=
              Lax3Proofs.RamDriverCluster.eq_of_arrOf_eq
                (hTpre.symm.trans hTold) v.isLt
            rw [hsame, heq]
            exact hbitOld v (Or.inr ⟨halive, by simpa [hck, hasgeq]⟩)
          · exact (hsem v halive hcur).1
      · intro v hv
        rcases hv with hvD | ⟨halive, hlt⟩
        · have hsame := hkeep v (Or.inl (hDdead v hvD))
          have heq : Tpre (v : ℕ) = Told (v : ℕ) :=
            Lax3Proofs.RamDriverCluster.eq_of_arrOf_eq
              (hTpre.symm.trans hTold) v.isLt
          rw [hsame, heq]
          exact hvalOld v (Or.inl hvD)
        · rw [hcnext] at hlt
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hbefore | hcur
          · have hasgeq := CoverPrefixA.assignment_eq_of_lt
              hstableK.turn.state hturn.stable.turn.state (v : ℕ) v.isLt
                halive hbefore
            have hne : am' (v : ℕ) ≠ k := by omega
            have hsame := hkeep v (Or.inr hne)
            have heq : Tpre (v : ℕ) = Told (v : ℕ) :=
              Lax3Proofs.RamDriverCluster.eq_of_arrOf_eq
                (hTpre.symm.trans hTold) v.isLt
            rw [hsame, heq]
            exact hvalOld v (Or.inr ⟨halive, by simpa [hck, hasgeq]⟩)
          · exact (hsem v halive hcur).2
    refine ⟨τ', _, hr, le_rfl, ?_, hcnext⟩
    exact ⟨Xm', am', Mm', by simpa [hcnext] using hturn.stable,
      hturn.out_eq.trans hout, htable'⟩
  obtain ⟨σ', hr, hI', hcq⟩ :=
    (Lax3Proofs.Refine.SigmaLoop.forRangeZeroSum "c" "qn" I q
      (fun k => streamSearchSortCost bits (W k) (W k) + Klife k)
      hqB
      (fun τ hτ => by
        obtain ⟨_, _, _, hstable, _, _⟩ := hτ
        exact hstable.turn.state.pos_le)
      (fun τ hτ => by
        obtain ⟨_, _, _, hstable, _, _⟩ := hτ
        simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using
          hstable.turn.q_var)
      hbody).run hstart
  obtain ⟨Xm, am, Mm, hstable, hout, htab⟩ := hI'
  have hstableQ : StreamStableState B n q_top cap mb ns nt q j q bits ell
      φ G A₀ π centre O T Xm am Mm Gm C σ' := by
    simpa [hcq] using hstable
  have hfinal : TableInvOn q_top cap mb φ G j A₀ C
      ({v : Fin n | A₀ (v : ℕ) ≠ 0} ∪ D) σ' := by
    apply htab.mono
    intro v hv
    rcases hv with halive | hvD
    · have hasg := CoverPrefixA.asg_lt_at_end hcentres hstableQ.turn.state
          (v : ℕ) v.isLt halive
      exact Or.inr ⟨halive, by simpa [hcq] using hasg⟩
    · exact Or.inl hvD
  refine ⟨σ', _, ?_, le_rfl, Xm, am, Mm, hstableQ, hfinal, hout⟩
  simpa [streamCentreLoopCom, W, Nat.add_assoc] using hr

end Lax3Proofs.Refine.CoverActiveStreamLoop
