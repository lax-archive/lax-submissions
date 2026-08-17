import Lax3Proofs.Refine.CoverActiveStreamPrepare

/-!
# Releasing one streamed centre's reusable buffers

Every temporary mask produced for a streamed centre is supported on its
resident row.  This module clears exactly that row after recursive readback,
including every successor-depth colour slot.  No carrier-wide reset is used.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamRelease

open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.Refine.CoverActiveStreamMask
open Lax3Proofs.Refine.CoverActiveStreamColour
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.ScatterBlock (renEnv renEnv_arrs renEnv_vars)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {n : ℕ}

/-- One allocated carrier array whose nonzero cells lie on the current row. -/
def StreamSparseAt (n tail : ℕ) (Xmem : ℕ → ℕ) (a : String) (σ : Env) : Prop :=
  ∃ F, σ.arrs a = arrOf n F ∧ BlockSupported n 0 tail Xmem F

/-- The complete row-supported state that must be reset between centres. -/
structure StreamReleasePre
    (n na tail cap mb j : ℕ) (Xmem : ℕ → ℕ) (σ : Env) : Prop where
  tail_var : σ.vars "tail" = tail
  row_arr : σ.arrs (xmmName j) = arrOf na Xmem
  tail_le : tail ≤ n
  row_fit : tail ≤ na
  index_bound : ∀ p, p < tail → Xmem p < n
  cluster : StreamSparseAt n tail Xmem (cluName j) σ
  retained : StreamSparseAt n tail Xmem (resName j) σ
  batch : StreamSparseAt n tail Xmem (batName j) σ
  child : StreamSparseAt n tail Xmem (alvName (j + 1)) σ
  game : StreamSparseAt n tail Xmem (gamName (j + 1)) σ
  colours : ∀ s, s < sigL cap mb (j + 1) →
    StreamSparseAt n tail Xmem (colName (j + 1) s) σ

/-- The five non-palette buffers cleared once per centre. -/
def streamFixedReleaseCom (j : ℕ) : Com :=
  .seq (streamBlockClearCom (xmmName j) (cluName j))
    (.seq (streamBlockClearCom (xmmName j) (resName j))
      (.seq (streamBlockClearCom (xmmName j) (batName j))
        (.seq (streamBlockClearCom (xmmName j) (alvName (j + 1)))
          (streamBlockClearCom (xmmName j) (gamName (j + 1))))))

/-- Clear the five masks, then every successor-depth palette slot. -/
def streamReleaseCom (cap mb j : ℕ) : Com :=
  .seq (streamFixedReleaseCom j)
    (streamAtDepthCom j (streamPaletteClearCom cap mb j))

def streamReleaseCost (tail slots : ℕ) : ℕ :=
  5 * streamBlockClearCost tail + streamPaletteClearCost tail slots

/-- A sparse array other than the destination is framed by one clear pass. -/
theorem StreamSparseAt.frame_clear
    {B n tail K : ℕ} {Xmem : ℕ → ℕ} {a idx dst : String}
    {σ σ' : Env}
    (h : StreamSparseAt n tail Xmem a σ)
    (hr : Run B (streamBlockClearCom idx dst) σ σ' K) (hne : a ≠ dst) :
    StreamSparseAt n tail Xmem a σ' := by
  obtain ⟨F, hF, hsup⟩ := h
  refine ⟨F, ?_, hsup⟩
  rw [hr.frame_arr a (fun hm => hne (mem_warrs_streamBlockMapCom hm))]
  exact hF

/-- A successful sparse clear leaves the destination represented by the
zero function, while retaining its sparse-support certificate. -/
theorem sparseAt_zero_of_clear
    {n tail : ℕ} {Xmem F : ℕ → ℕ} {a : String} {σ : Env}
    (harr : σ.arrs a = arrOf n F) (hval : ∀ v, v < n → F v = 0)
    (hsup : BlockSupported n 0 tail Xmem F) :
    StreamSparseAt n tail Xmem a σ ∧
      σ.arrs a = arrOf n (fun _ => 0) := by
  refine ⟨⟨F, harr, hsup⟩, ?_⟩
  rw [harr]
  exact arrOf_congr hval

theorem mem_warrs_streamFixedReleaseCom {j : ℕ} {a : String}
    (h : a ∈ (streamFixedReleaseCom j).warrs) :
    a = cluName j ∨ a = resName j ∨ a = batName j ∨
      a = alvName (j + 1) ∨ a = gamName (j + 1) := by
  simp only [streamFixedReleaseCom, Com.warrs, List.mem_append,
    List.not_mem_nil, false_or] at h
  rcases h with h | h | h | h | h
  · exact Or.inl (mem_warrs_streamBlockMapCom h)
  · exact Or.inr (Or.inl (mem_warrs_streamBlockMapCom h))
  · exact Or.inr (Or.inr (Or.inl (mem_warrs_streamBlockMapCom h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_warrs_streamBlockMapCom h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_warrs_streamBlockMapCom h))))

theorem notMem_warrs_streamFixedReleaseCom {j : ℕ} {a : String}
    (hclu : a ≠ cluName j) (hres : a ≠ resName j) (hbat : a ≠ batName j)
    (halv : a ≠ alvName (j + 1)) (hgam : a ≠ gamName (j + 1)) :
    a ∉ (streamFixedReleaseCom j).warrs := by
  intro h
  rcases mem_warrs_streamFixedReleaseCom h with h | h | h | h | h
  exacts [hclu h, hres h, hbat h, halv h, hgam h]

theorem notMem_wvars_streamFixedReleaseCom {j : ℕ} {y : String}
    (hp : y ≠ "p") (hpend : y ≠ "pend") (hcw : y ≠ "cw") :
    y ∉ (streamFixedReleaseCom j).wvars := by
  simp [streamFixedReleaseCom, streamBlockClearCom, streamBlockMapCom,
    Lax3Proofs.Refine.BlockLeaves.blockMapRangeCom, Com.wvars, hp, hpend, hcw]

theorem mem_warrs_streamPaletteClearCom
    {cap mb j : ℕ} {a : String} (h : a ∈ (streamPaletteClearCom cap mb j).warrs) :
    ∃ s, s < sigL cap mb (j + 1) ∧ a = colName (j + 1) s := by
  obtain ⟨s, hs, hm⟩ := Lax3Proofs.RamDriverFrames.mem_warrs_foldRange
    (fun s => streamBlockClearCom "xmem" (colName (j + 1) s))
    (sigL cap mb (j + 1)) h
  exact ⟨s, hs, mem_warrs_streamBlockMapCom hm⟩

theorem notMem_warrs_streamPaletteAtDepthCom
    {cap mb j : ℕ} {a : String}
    (hcol : ∀ s, s < sigL cap mb (j + 1) → a ≠ colName (j + 1) s) :
    a ∉ (streamAtDepthCom j (streamPaletteClearCom cap mb j)).warrs := by
  intro h
  have hpull := Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
    (streamDepthSwap_invol j) _ h
  obtain ⟨s, hs, he⟩ := mem_warrs_streamPaletteClearCom hpull
  have hae : a = colName (j + 1) s := by
    have := congrArg (streamDepthSwap j) he
    simpa only [streamDepthSwap_invol, streamDepthSwap_colName] using this
  exact hcol s hs hae

theorem notMem_wvars_streamPaletteAtDepthCom
    {cap mb j : ℕ} {y : String}
    (hp : y ≠ "p") (hpend : y ≠ "pend") (hcw : y ≠ "cw") :
    y ∉ (streamAtDepthCom j (streamPaletteClearCom cap mb j)).wvars := by
  intro h
  rw [streamAtDepthCom, Lax3Proofs.Refine.ScatterBlock.renCom_wvars] at h
  obtain ⟨s, -, hm⟩ := Lax3Proofs.RamDriverDescend.mem_wvars_foldRange
    (fun s => streamBlockClearCom "xmem" (colName (j + 1) s))
    (sigL cap mb (j + 1)) h
  have hm' := mem_wvars_streamBlockMapCom hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
  rcases hm' with h | h | h
  exacts [hp h, hpend h, hcw h]

/-- Complete array frame for a centre release. -/
theorem notMem_warrs_streamReleaseCom
    {cap mb j : ℕ} {a : String}
    (hclu : a ≠ cluName j) (hres : a ≠ resName j)
    (hbat : a ≠ batName j) (halv : a ≠ alvName (j + 1))
    (hgam : a ≠ gamName (j + 1))
    (hcol : ∀ s, s < sigL cap mb (j + 1) → a ≠ colName (j + 1) s) :
    a ∉ (streamReleaseCom cap mb j).warrs := by
  intro h
  simp only [streamReleaseCom, Com.warrs, List.mem_append] at h
  rcases h with h | h
  · exact notMem_warrs_streamFixedReleaseCom hclu hres hbat halv hgam h
  · exact notMem_warrs_streamPaletteAtDepthCom hcol h

/-- Complete scalar frame for a centre release. -/
theorem notMem_wvars_streamReleaseCom
    {cap mb j : ℕ} {y : String}
    (hp : y ≠ "p") (hpend : y ≠ "pend") (hcw : y ≠ "cw") :
    y ∉ (streamReleaseCom cap mb j).wvars := by
  intro h
  simp only [streamReleaseCom, Com.wvars, List.mem_append] at h
  rcases h with h | h
  · exact notMem_wvars_streamFixedReleaseCom hp hpend hcw h
  · exact notMem_wvars_streamPaletteAtDepthCom hp hpend hcw h

/-- The release program writes only successor scratch and therefore frames
the parent `LevelPre`. -/
theorem levelPre_run_streamFixedReleaseCom
    {B cap mb ns nt j K : ℕ} {O T A₀ Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B (streamFixedReleaseCom j) σ σ' K) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  apply Lax3Proofs.RamDriverCompose.levelPre_run hp hr
  · exact notMem_wvars_streamFixedReleaseCom (by decide) (by decide) (by decide)
  · exact notMem_wvars_streamFixedReleaseCom (by decide) (by decide) (by decide)
  · exact notMem_wvars_streamFixedReleaseCom (by decide) (by decide) (by decide)
  · exact notMem_warrs_streamFixedReleaseCom (by simp [cluName, String.ext_iff])
      (by simp [resName, String.ext_iff]) (by simp [batName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
  · exact notMem_warrs_streamFixedReleaseCom (by simp [cluName, String.ext_iff])
      (by simp [resName, String.ext_iff]) (by simp [batName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
  · exact notMem_warrs_streamFixedReleaseCom
      (by simp [alvName, cluName, String.ext_iff])
      (by simp [alvName, resName, String.ext_iff])
      (by simp [alvName, batName, String.ext_iff]) (alvName_ne_succ j)
      (by simp [alvName, gamName, String.ext_iff])
  · exact notMem_warrs_streamFixedReleaseCom
      (by simp [gamName, cluName, String.ext_iff])
      (by simp [gamName, resName, String.ext_iff])
      (by simp [gamName, batName, String.ext_iff])
      (by simp [gamName, alvName, String.ext_iff]) (gamName_ne_succ (le_refl j))
  · intro s
    exact notMem_warrs_streamFixedReleaseCom
      (by simp [colName, cluName, String.ext_iff])
      (by simp [colName, resName, String.ext_iff])
      (by simp [colName, batName, String.ext_iff])
      (by simp [colName, alvName, String.ext_iff])
      (by simp [colName, gamName, String.ext_iff])
  · intro a ha
    simp only [Lax3Proofs.RamDriverCompose.zeroArrs, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact notMem_warrs_streamFixedReleaseCom
        (by simp [cluName, String.ext_iff]) (by simp [resName, String.ext_iff])
        (by simp [batName, String.ext_iff]) (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
  · exact notMem_warrs_streamFixedReleaseCom
      (by simp [memName, cluName, String.ext_iff])
      (by simp [memName, resName, String.ext_iff])
      (by simp [memName, batName, String.ext_iff])
      (by simp [memName, alvName, String.ext_iff])
      (by simp [memName, gamName, String.ext_iff])
  · exact notMem_wvars_streamFixedReleaseCom
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff])

/-- Palette release at physical depth-owned storage also frames the parent
level, since it writes only `colName (j+1) _`. -/
theorem levelPre_run_streamPaletteAtDepthCom
    {B cap mb ns nt j K : ℕ} {O T A₀ Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B (streamAtDepthCom j (streamPaletteClearCom cap mb j)) σ σ' K) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  apply Lax3Proofs.RamDriverCompose.levelPre_run hp hr
  · exact notMem_wvars_streamPaletteAtDepthCom (by decide) (by decide) (by decide)
  · exact notMem_wvars_streamPaletteAtDepthCom (by decide) (by decide) (by decide)
  · exact notMem_wvars_streamPaletteAtDepthCom (by decide) (by decide) (by decide)
  · exact notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_lit (by decide)))
  · exact notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_lit (by decide)))
  · exact notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_alvName _ _ _))
  · exact notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_gamName _ _ _))
  · intro q
    exact notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => colName_ne_depth (by omega))
  · intro a ha
    simp only [Lax3Proofs.RamDriverCompose.zeroArrs, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact notMem_warrs_streamPaletteAtDepthCom
        (fun s _ => Ne.symm (colName_ne_lit (by decide)))
  · exact notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_memName _ _ _))
  · exact notMem_wvars_streamPaletteAtDepthCom
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff])

/-- Exact postcondition of a released centre. -/
structure StreamReleaseOut
    (B n cap mb ns nt na tail j : ℕ)
    (O T A₀ Gm Xmem : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (σ₀ σ : Env) : Prop where
  level : LevelPre B n cap mb ns nt O T j A₀ Gm C σ
  tail_var : σ.vars "tail" = tail
  row_arr : σ.arrs (xmmName j) = arrOf na Xmem
  cluster_zero : σ.arrs (cluName j) = arrOf n (fun _ => 0)
  retained_zero : σ.arrs (resName j) = arrOf n (fun _ => 0)
  batch_zero : σ.arrs (batName j) = arrOf n (fun _ => 0)
  child_zero : σ.arrs (alvName (j + 1)) = arrOf n (fun _ => 0)
  game_zero : σ.arrs (gamName (j + 1)) = arrOf n (fun _ => 0)
  colours_zero : ∀ s, s < sigL cap mb (j + 1) →
    σ.arrs (colName (j + 1) s) = arrOf n (fun _ => 0)
  out_eq : σ.out = σ₀.out

open Classical in
/-- **All per-centre storage is released in row time.**  The five masks and
each successor palette slot are cleared only at the `tail` resident vertices;
the parent level and output tape are framed. -/
theorem streamReleaseStep
    {B cap mb ns nt na tail j : ℕ}
    {O T A₀ Gm Xmem : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) :
    Spec B
      (fun σ => StreamReleasePre n na tail cap mb j Xmem σ ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
      (streamReleaseCom cap mb j)
      (fun σ σ' => StreamReleaseOut B n cap mb ns nt na tail j
        O T A₀ Gm Xmem C σ σ')
      (streamReleaseCost tail (sigL cap mb (j + 1))) := by
  refine Spec.of_exists fun σ hpre => ?_
  let hp := hpre.1
  obtain ⟨Fclu, hclu, hcluSup⟩ := hp.cluster
  obtain ⟨σ₁, hr₁, hq₁⟩ :=
    (streamBlockClearCom_supported_spec h1B hnB hp.tail_le hp.row_fit
      hp.index_bound (by simp [xmmName, cluName, String.ext_iff])).run
      ⟨hp.tail_var, hp.row_arr, hclu, hcluSup⟩
  obtain ⟨Fclu₁, hclu₁, hcluVal₁, hcluSup₁⟩ := hq₁.1
  have hcluZero₁ : σ₁.arrs (cluName j) = arrOf n (fun _ => 0) := by
    rw [hclu₁]
    exact arrOf_congr hcluVal₁
  let hp₁ : StreamReleasePre n na tail cap mb j Xmem σ₁ := {
    tail_var := hq₁.2.1
    row_arr := hq₁.2.2
    tail_le := hp.tail_le
    row_fit := hp.row_fit
    index_bound := hp.index_bound
    cluster := ⟨Fclu₁, hclu₁, hcluSup₁⟩
    retained := hp.retained.frame_clear hr₁ (by simp [resName, cluName, String.ext_iff])
    batch := hp.batch.frame_clear hr₁ (by simp [batName, cluName, String.ext_iff])
    child := hp.child.frame_clear hr₁ (by simp [alvName, cluName, String.ext_iff])
    game := hp.game.frame_clear hr₁ (by simp [gamName, cluName, String.ext_iff])
    colours := fun s hs => (hp.colours s hs).frame_clear hr₁
      (by simp [colName, cluName, String.ext_iff]) }

  obtain ⟨Fres, hres, hresSup⟩ := hp₁.retained
  obtain ⟨σ₂, hr₂, hq₂⟩ :=
    (streamBlockClearCom_supported_spec h1B hnB hp₁.tail_le hp₁.row_fit
      hp₁.index_bound (by simp [xmmName, resName, String.ext_iff])).run
      ⟨hp₁.tail_var, hp₁.row_arr, hres, hresSup⟩
  obtain ⟨Fres₂, hres₂, hresVal₂, hresSup₂⟩ := hq₂.1
  have hresZero₂ : σ₂.arrs (resName j) = arrOf n (fun _ => 0) := by
    rw [hres₂]
    exact arrOf_congr hresVal₂
  have hcluZero₂ : σ₂.arrs (cluName j) = arrOf n (fun _ => 0) := by
    rw [hr₂.frame_arr _ (fun hm => (by
      have := mem_warrs_streamBlockMapCom hm
      simp [cluName, resName, String.ext_iff] at this))]
    exact hcluZero₁
  let hp₂ : StreamReleasePre n na tail cap mb j Xmem σ₂ := {
    tail_var := hq₂.2.1
    row_arr := hq₂.2.2
    tail_le := hp₁.tail_le
    row_fit := hp₁.row_fit
    index_bound := hp₁.index_bound
    cluster := hp₁.cluster.frame_clear hr₂ (by simp [cluName, resName, String.ext_iff])
    retained := ⟨Fres₂, hres₂, hresSup₂⟩
    batch := hp₁.batch.frame_clear hr₂ (by simp [batName, resName, String.ext_iff])
    child := hp₁.child.frame_clear hr₂ (by simp [alvName, resName, String.ext_iff])
    game := hp₁.game.frame_clear hr₂ (by simp [gamName, resName, String.ext_iff])
    colours := fun s hs => (hp₁.colours s hs).frame_clear hr₂
      (by simp [colName, resName, String.ext_iff]) }

  obtain ⟨Fbat, hbat, hbatSup⟩ := hp₂.batch
  obtain ⟨σ₃, hr₃, hq₃⟩ :=
    (streamBlockClearCom_supported_spec h1B hnB hp₂.tail_le hp₂.row_fit
      hp₂.index_bound (by simp [xmmName, batName, String.ext_iff])).run
      ⟨hp₂.tail_var, hp₂.row_arr, hbat, hbatSup⟩
  obtain ⟨Fbat₃, hbat₃, hbatVal₃, hbatSup₃⟩ := hq₃.1
  have hbatZero₃ : σ₃.arrs (batName j) = arrOf n (fun _ => 0) := by
    rw [hbat₃]
    exact arrOf_congr hbatVal₃
  have hcluZero₃ : σ₃.arrs (cluName j) = arrOf n (fun _ => 0) := by
    rw [hr₃.frame_arr _ (fun hm => (by
      have := mem_warrs_streamBlockMapCom hm
      simp [cluName, batName, String.ext_iff] at this))]
    exact hcluZero₂
  have hresZero₃ : σ₃.arrs (resName j) = arrOf n (fun _ => 0) := by
    rw [hr₃.frame_arr _ (fun hm => (by
      have := mem_warrs_streamBlockMapCom hm
      simp [resName, batName, String.ext_iff] at this))]
    exact hresZero₂
  let hp₃ : StreamReleasePre n na tail cap mb j Xmem σ₃ := {
    tail_var := hq₃.2.1
    row_arr := hq₃.2.2
    tail_le := hp₂.tail_le
    row_fit := hp₂.row_fit
    index_bound := hp₂.index_bound
    cluster := hp₂.cluster.frame_clear hr₃ (by simp [cluName, batName, String.ext_iff])
    retained := hp₂.retained.frame_clear hr₃ (by simp [resName, batName, String.ext_iff])
    batch := ⟨Fbat₃, hbat₃, hbatSup₃⟩
    child := hp₂.child.frame_clear hr₃ (by simp [alvName, batName, String.ext_iff])
    game := hp₂.game.frame_clear hr₃ (by simp [gamName, batName, String.ext_iff])
    colours := fun s hs => (hp₂.colours s hs).frame_clear hr₃
      (by simp [colName, batName, String.ext_iff]) }

  obtain ⟨Fchild, hchild, hchildSup⟩ := hp₃.child
  obtain ⟨σ₄, hr₄, hq₄⟩ :=
    (streamBlockClearCom_supported_spec h1B hnB hp₃.tail_le hp₃.row_fit
      hp₃.index_bound (by simp [xmmName, alvName, String.ext_iff])).run
      ⟨hp₃.tail_var, hp₃.row_arr, hchild, hchildSup⟩
  obtain ⟨Fchild₄, hchild₄, hchildVal₄, hchildSup₄⟩ := hq₄.1
  have hchildZero₄ : σ₄.arrs (alvName (j + 1)) = arrOf n (fun _ => 0) := by
    rw [hchild₄]
    exact arrOf_congr hchildVal₄
  have hcluZero₄ := (hr₄.frame_arr (cluName j) (fun hm => (by
    have := mem_warrs_streamBlockMapCom hm
    simp [cluName, alvName, String.ext_iff] at this))).trans hcluZero₃
  have hresZero₄ := (hr₄.frame_arr (resName j) (fun hm => (by
    have := mem_warrs_streamBlockMapCom hm
    simp [resName, alvName, String.ext_iff] at this))).trans hresZero₃
  have hbatZero₄ := (hr₄.frame_arr (batName j) (fun hm => (by
    have := mem_warrs_streamBlockMapCom hm
    simp [batName, alvName, String.ext_iff] at this))).trans hbatZero₃
  let hp₄ : StreamReleasePre n na tail cap mb j Xmem σ₄ := {
    tail_var := hq₄.2.1
    row_arr := hq₄.2.2
    tail_le := hp₃.tail_le
    row_fit := hp₃.row_fit
    index_bound := hp₃.index_bound
    cluster := hp₃.cluster.frame_clear hr₄ (by simp [cluName, alvName, String.ext_iff])
    retained := hp₃.retained.frame_clear hr₄ (by simp [resName, alvName, String.ext_iff])
    batch := hp₃.batch.frame_clear hr₄ (by simp [batName, alvName, String.ext_iff])
    child := ⟨Fchild₄, hchild₄, hchildSup₄⟩
    game := hp₃.game.frame_clear hr₄ (by simp [gamName, alvName, String.ext_iff])
    colours := fun s hs => (hp₃.colours s hs).frame_clear hr₄
      (by simp [colName, alvName, String.ext_iff]) }

  obtain ⟨Fgame, hgame, hgameSup⟩ := hp₄.game
  obtain ⟨σ₅, hr₅, hq₅⟩ :=
    (streamBlockClearCom_supported_spec h1B hnB hp₄.tail_le hp₄.row_fit
      hp₄.index_bound (by simp [xmmName, gamName, String.ext_iff])).run
      ⟨hp₄.tail_var, hp₄.row_arr, hgame, hgameSup⟩
  obtain ⟨Fgame₅, hgame₅, hgameVal₅, hgameSup₅⟩ := hq₅.1
  have hgameZero₅ : σ₅.arrs (gamName (j + 1)) = arrOf n (fun _ => 0) := by
    rw [hgame₅]
    exact arrOf_congr hgameVal₅
  have hcluZero₅ := (hr₅.frame_arr (cluName j) (fun hm => (by
    have := mem_warrs_streamBlockMapCom hm
    simp [cluName, gamName, String.ext_iff] at this))).trans hcluZero₄
  have hresZero₅ := (hr₅.frame_arr (resName j) (fun hm => (by
    have := mem_warrs_streamBlockMapCom hm
    simp [resName, gamName, String.ext_iff] at this))).trans hresZero₄
  have hbatZero₅ := (hr₅.frame_arr (batName j) (fun hm => (by
    have := mem_warrs_streamBlockMapCom hm
    simp [batName, gamName, String.ext_iff] at this))).trans hbatZero₄
  have hchildZero₅ := (hr₅.frame_arr (alvName (j + 1)) (fun hm => (by
    have := mem_warrs_streamBlockMapCom hm
    simp [alvName, gamName, String.ext_iff] at this))).trans hchildZero₄
  let hp₅ : StreamReleasePre n na tail cap mb j Xmem σ₅ := {
    tail_var := hq₅.2.1
    row_arr := hq₅.2.2
    tail_le := hp₄.tail_le
    row_fit := hp₄.row_fit
    index_bound := hp₄.index_bound
    cluster := hp₄.cluster.frame_clear hr₅ (by simp [cluName, gamName, String.ext_iff])
    retained := hp₄.retained.frame_clear hr₅ (by simp [resName, gamName, String.ext_iff])
    batch := hp₄.batch.frame_clear hr₅ (by simp [batName, gamName, String.ext_iff])
    child := hp₄.child.frame_clear hr₅ (by simp [alvName, gamName, String.ext_iff])
    game := ⟨Fgame₅, hgame₅, hgameSup₅⟩
    colours := fun s hs => (hp₄.colours s hs).frame_clear hr₅
      (by simp [colName, gamName, String.ext_iff]) }

  have hrFixed : Run B (streamFixedReleaseCom j) σ σ₅
      (5 * streamBlockClearCost tail) := by
    have hk : 5 * streamBlockClearCost tail =
        streamBlockClearCost tail + (streamBlockClearCost tail +
          (streamBlockClearCost tail +
            (streamBlockClearCost tail + streamBlockClearCost tail))) := by omega
    rw [hk]
    exact hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))
  have hlevel₅ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₅ :=
    levelPre_run_streamFixedReleaseCom hpre.2 hrFixed
  have hlevel₅keep := hlevel₅
  obtain ⟨hn₅, hoff₅, htgt₅, -, -, hcolsOld₅, -, -, -, hlevelMem₅,
    -, -, horder₅, -, -, -⟩ := hlevel₅
  obtain ⟨Xa₅, hXa₅, -⟩ := hp₅.cluster
  obtain ⟨Ra₅, hRa₅, -⟩ := hp₅.retained
  obtain ⟨Wf, hWf⟩ := hlevelMem₅.1 ("wa", mb) (by simp)
  have hpalettePre : StreamColPre n ns nt na tail cap mb j O T C Xmem
      Xa₅ Ra₅ Wf (renEnv (streamDepthSwap j) σ₅) := {
    tail_var := by simpa only [renEnv_vars] using hp₅.tail_var
    n_var := by simpa only [renEnv_vars] using hn₅
    off_arr := by simpa [renEnv_arrs, streamDepthSwap] using hoff₅
    target_arr := by simpa [renEnv_arrs, streamDepthSwap] using htgt₅
    target_fit := horder₅.1
    row_arr := by simpa only [renEnv_arrs, streamDepthSwap_xmem] using hp₅.row_arr
    cluster_arr := by simpa only [renEnv_arrs, streamDepthSwap_cluName] using hXa₅
    retained_arr := by simpa only [renEnv_arrs, streamDepthSwap_resName] using hRa₅
    old_colours := fun s hs => by
      simpa only [renEnv_arrs, streamDepthSwap_colName] using hcolsOld₅ s hs
    batch_arr := by simpa [renEnv_arrs, streamDepthSwap] using hWf
    next_slots := fun s hs => by
      obtain ⟨F, hF, hsup⟩ := hp₅.colours s hs
      exact ⟨F, by simpa only [renEnv_arrs, streamDepthSwap_colName] using hF, hsup⟩ }
  obtain ⟨σ₆, hr₆, hpalette₆⟩ :=
    (Lax3Proofs.Refine.ScatterBlock.renCom_spec (streamDepthSwap_invol j)
      (streamPaletteClearCom_spec h1B hnB hp₅.tail_le hp₅.row_fit
        hp₅.index_bound)).run hpalettePre
  have hlevel₆ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₆ :=
    levelPre_run_streamPaletteAtDepthCom hlevel₅keep hr₆
  have hcluZero₆ : σ₆.arrs (cluName j) = arrOf n (fun _ => 0) := by
    rw [hr₆.frame_arr _ (notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_cluName _ _ _)))]
    exact hcluZero₅
  have hresZero₆ : σ₆.arrs (resName j) = arrOf n (fun _ => 0) := by
    rw [hr₆.frame_arr _ (notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_resName _ _ _)))]
    exact hresZero₅
  have hbatZero₆ : σ₆.arrs (batName j) = arrOf n (fun _ => 0) := by
    rw [hr₆.frame_arr _ (notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_batName _ _ _)))]
    exact hbatZero₅
  have hchildZero₆ : σ₆.arrs (alvName (j + 1)) = arrOf n (fun _ => 0) := by
    rw [hr₆.frame_arr _ (notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_alvName _ _ _)))]
    exact hchildZero₅
  have hgameZero₆ : σ₆.arrs (gamName (j + 1)) = arrOf n (fun _ => 0) := by
    rw [hr₆.frame_arr _ (notMem_warrs_streamPaletteAtDepthCom
      (fun s _ => Ne.symm (colName_ne_gamName _ _ _)))]
    exact hgameZero₅
  have htail₆ : σ₆.vars "tail" = tail := by
    simpa only [renEnv_vars] using hpalette₆.1.tail_var
  have hrow₆ : σ₆.arrs (xmmName j) = arrOf na Xmem := by
    simpa only [renEnv_arrs, streamDepthSwap_xmem] using hpalette₆.1.row_arr
  have hcolZero₆ : ∀ s, s < sigL cap mb (j + 1) →
      σ₆.arrs (colName (j + 1) s) = arrOf n (fun _ => 0) := by
    intro s hs
    simpa only [renEnv_arrs, streamDepthSwap_colName] using hpalette₆.2 s hs
  refine ⟨σ₆, streamReleaseCost tail (sigL cap mb (j + 1)), ?_, le_rfl,
    hlevel₆, htail₆, hrow₆, hcluZero₆, hresZero₆, hbatZero₆,
    hchildZero₆, hgameZero₆, hcolZero₆, ?_⟩
  · simpa [streamReleaseCom, streamReleaseCost] using hrFixed.seq hr₆
  · apply (hrFixed.seq hr₆).out_eq
    change (streamFixedReleaseCom j).NoWrite ∧
      (streamAtDepthCom j (streamPaletteClearCom cap mb j)).NoWrite
    constructor
    · simp [streamFixedReleaseCom, streamBlockClearCom, streamBlockMapCom,
        Lax3Proofs.Refine.BlockLeaves.blockMapRangeCom, Com.NoWrite]
    · unfold streamAtDepthCom
      apply Lax3Proofs.Refine.ScatterBlock.renCom_noWrite
      rw [streamPaletteClearCom]
      exact Lax3Proofs.RamDriverBot.noWrite_foldRange _
        (fun _ => noWrite_streamBlockMapCom _ _ _) _

end Lax3Proofs.Refine.CoverActiveStreamRelease
