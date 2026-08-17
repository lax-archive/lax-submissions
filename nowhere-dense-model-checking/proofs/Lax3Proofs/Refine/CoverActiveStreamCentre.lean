import Lax3Proofs.Refine.CoverActiveStreamReadback
import Lax3Proofs.Refine.CoverActiveStreamPrepare
import Lax3Proofs.Refine.CoverActiveStreamRelease

/-!
# One complete streamed active-cover centre

This module composes the recursive seam, dead-aware scatter and streamed
readback.  The only scalar shared accidentally by the scatter engine and the
streamed loop is `"tail"`; the parent-depth `xpName j` save slot protects it
and the command below restores it before readback.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamCentre

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamCover Lax3Proofs.RamCoverActive
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBase
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.CoverActiveStreamScratch
open Lax3Proofs.Refine.CoverActiveStreamInner
open Lax3Proofs.Refine.CoverActiveStreamScatter
open Lax3Proofs.Refine.CoverActiveStreamReadback
open Lax3Proofs.Refine.CoverActiveStreamPrepare
open Lax3Proofs.Refine.CoverActiveStreamRelease
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.ScatterDeadTurn
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {n : ℕ}

noncomputable def streamScatterCom
    (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) : Com :=
  foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) 0
    (tablesAt q_top cap mb φ j)

/-- Restore the streamed row length after the scatter engine has reused its
literal `"tail"` scratch scalar. -/
noncomputable def streamScatterRestoreCom
    (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) : Com :=
  .seq (streamScatterCom q_top cap mb φ j)
    (.assign "tail" (.var (xpName j)))

/-- Recursion, scatter, and readback for one already-prepared streamed row. -/
noncomputable def streamCentreFinishCom
    (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) (inner : Com) : Com :=
  .seq (streamInnerCom j inner)
    (.seq (streamScatterRestoreCom q_top cap mb φ j)
      (streamReadbackCom q_top cap mb φ j))

noncomputable def streamCentreFinishCost
    (q_top cap mb j tail Kinner Kscatter : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  (8 + Kinner + 10) + ((Kscatter + 2) +
    (8 + rbCost q_top cap mb φ j tail))

/-- The whole body of one already-sorted streamed centre: prepare the child,
run it, scatter its answers, and read the current row back. -/
noncomputable def streamCentreCom
    (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) (inner : Com) : Com :=
  .seq (streamPrepareAtDepthCom q_top cap mb j φ)
    (streamCentreFinishCom q_top cap mb j φ inner)

noncomputable def streamCentreCost
    (q_top cap mb j tail rowMass ballWeight Kinner Kscatter : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  streamPrepareCost q_top cap mb j tail rowMass ballWeight φ +
    streamCentreFinishCost q_top cap mb j tail Kinner Kscatter φ

open Classical in
theorem notMem_warrs_streamScatterCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {a : String}
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ)
    (hfix : a ∉ ["mem", "alv", "dist", "exc", "q", "qd"])
    (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" a) :
    a ∉ (streamScatterCom q_top cap mb φ j).warrs := by
  intro hm
  rcases Lax3Proofs.RamDriverWrites.warrs_scatterDeadPhase j hloc
      (tablesAt q_top cap mb φ j) 0 (fun _ h => h) a hm with h | h
  · exact hfix h
  · exact hbb h

open Classical in
theorem notMem_warrs_streamScatterRestoreCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {a : String}
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ)
    (hfix : a ∉ ["mem", "alv", "dist", "exc", "q", "qd"])
    (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" a) :
    a ∉ (streamScatterRestoreCom q_top cap mb φ j).warrs := by
  simpa [streamScatterRestoreCom, Com.warrs] using
    notMem_warrs_streamScatterCom hloc hfix hbb

open Classical in
theorem notMem_wvars_streamScatterCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {y : String}
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ)
    (h₁ : y ∉ ["kc", "ke", "of", "oz", "oi", "oc", "mm", "ak", "av", "ac", "ax",
      "os", "flag"])
    (h₂ : y ∉ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
      "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"])
    (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" y)
    (henv : ∀ e, y ≠ envName e)
    (hflg : ∀ i k, y ≠ flgName j i k) :
    y ∉ (streamScatterCom q_top cap mb φ j).wvars := by
  intro hm
  rcases Lax3Proofs.RamDriverWrites.wvars_scatterDeadPhase j hloc
      (tablesAt q_top cap mb φ j) 0 (fun _ h => h) y hm with
    h | h | h | ⟨e, h⟩ | ⟨i, k, h⟩
  · exact h₁ h
  · exact h₂ h
  · exact hbb h
  · exact henv e h
  · exact hflg i k h

open Classical in
/-- Apart from the deliberate restoration of `"tail"`, the restored scatter
has the same scalar frame as the scatter fold. -/
theorem notMem_wvars_streamScatterRestoreCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {y : String}
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ)
    (h₁ : y ∉ ["kc", "ke", "of", "oz", "oi", "oc", "mm", "ak", "av", "ac", "ax",
      "os", "flag"])
    (h₂ : y ∉ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
      "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"])
    (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" y)
    (henv : ∀ e, y ≠ envName e)
    (hflg : ∀ i k, y ≠ flgName j i k)
    (htail : y ≠ "tail") :
    y ∉ (streamScatterRestoreCom q_top cap mb φ j).wvars := by
  intro h
  simp only [streamScatterRestoreCom, Com.wvars, List.mem_append] at h
  rcases h with h | h
  · exact notMem_wvars_streamScatterCom hloc h₁ h₂ hbb henv hflg h
  · exact htail (by simpa [Com.wvars] using h)

open Classical in
/-- The parent-depth save slot carrying `tail` is outside the complete
scatter phase's scalar write set. -/
theorem xpName_notMem_streamScatterCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ) :
    xpName j ∉ (streamScatterCom q_top cap mb φ j).wvars := by
  apply notMem_wvars_streamScatterCom hloc
  · simp [xpName, String.ext_iff]
  · simp [xpName, String.ext_iff]
  · exact not_ext_bb_xpName j
  · intro e; simp [xpName, envName, String.ext_iff]
  · intro i k; simp [xpName, flgName, String.ext_iff]

/-- Streamed readback writes only its private offset row and the current
depth's formula tables. -/
theorem notMem_warrs_streamReadbackCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {a : String}
    (hxof : a ≠ xofName j) (htab : ∀ i, a ≠ tabName j i) :
    a ∉ (streamReadbackCom q_top cap mb φ j).warrs := by
  intro h
  simp only [streamReadbackCom, Com.warrs, List.mem_append] at h
  rcases h with h | h
  · simp [streamOffsetCom, Com.warrs] at h
    exact hxof h
  · obtain ⟨i, hi⟩ := RamDriverBase.mem_warrs_readbackCom h
    exact htab i hi

/-- Readback changes only its three private scalar temporaries. -/
theorem notMem_wvars_streamReadbackCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} {y : String}
    (hz : y ≠ "z") (hzend : y ≠ "zend") (hrv : y ≠ "rv") :
    y ∉ (streamReadbackCom q_top cap mb φ j).wvars := by
  intro h
  simp only [streamReadbackCom, Com.wvars, List.mem_append] at h
  rcases h with h | h
  · simpa [streamOffsetCom, Com.wvars] using h
  · exact RamDriverBase.not_mem_wvars_readbackCom hz hzend hrv h

/-- In particular, readback leaves the streamed row length untouched. -/
theorem tail_notMem_wvars_streamReadbackCom
    {q_top cap mb j : ℕ} {φ : Lax3.FirstOrder.FO 0} :
    "tail" ∉ (streamReadbackCom q_top cap mb φ j).wvars := by
  exact notMem_wvars_streamReadbackCom (by decide) (by decide) (by decide)

theorem belowArr_notMem_warrs_streamScatterRestoreCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamScatterRestoreCom q_top cap mb phi j).warrs := by
  simpa [streamScatterRestoreCom, streamScatterCom, Com.warrs] using
    (Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_scatterDeadPhase
      q_top cap mb j phi h)

theorem belowVar_notMem_wvars_streamScatterRestoreCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {y : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamScatterRestoreCom q_top cap mb phi j).wvars := by
  intro hm
  simp only [streamScatterRestoreCom, Com.wvars, List.mem_append] at hm
  rcases hm with hm | hm
  · have hs : y ∉ (streamScatterCom q_top cap mb phi j).wvars := by
      simpa [streamScatterCom] using
        (Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_scatterDeadPhase
          q_top cap mb j phi h)
    exact hs hm
  · have htail : y ≠ "tail" := by
      intro he
      exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "tail")
        (he ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h)
    exact htail (by simpa [Com.wvars] using hm)

theorem belowArr_notMem_warrs_streamReadbackCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamReadbackCom q_top cap mb phi j).warrs :=
  notMem_warrs_streamReadbackCom
    (Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto))
    (fun i => Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto))

theorem belowVar_notMem_wvars_streamReadbackCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {y : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamReadbackCom q_top cap mb phi j).wvars := by
  apply notMem_wvars_streamReadbackCom
  all_goals
    intro he
    first
    | exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "z")
        (he ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h)
    | exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "zend")
        (he ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h)
    | exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "rv")
        (he ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h)

/-- The complete streamed centre respects every shallower depth-owned array
provided its recursive child does. -/
theorem belowArr_notMem_warrs_streamCentreCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {inner : Com}
    {a : String}
    (hinner : ∀ a, Lax3Proofs.RamDriverWrites.BelowArr (j + 1) a →
      a ∉ inner.warrs)
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamCentreCom q_top cap mb j phi inner).warrs := by
  intro hm
  simp only [streamCentreCom, streamCentreFinishCom, Com.warrs,
    List.mem_append] at hm
  rcases hm with hm | hm | hm | hm
  · exact (belowArr_notMem_warrs_streamPrepareAtDepthCom
      q_top cap mb j phi h) hm
  · exact (belowArr_notMem_warrs_streamInnerCom hinner h) hm
  · exact (belowArr_notMem_warrs_streamScatterRestoreCom
      q_top cap mb j phi h) hm
  · exact (belowArr_notMem_warrs_streamReadbackCom
      q_top cap mb j phi h) hm

/-- Scalar counterpart of `belowArr_notMem_warrs_streamCentreCom`. -/
theorem belowVar_notMem_wvars_streamCentreCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {inner : Com}
    {y : String}
    (hinner : ∀ y, Lax3Proofs.RamDriverWrites.BelowVar (j + 1) y →
      y ∉ inner.wvars)
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamCentreCom q_top cap mb j phi inner).wvars := by
  intro hm
  simp only [streamCentreCom, streamCentreFinishCom, Com.wvars,
    List.mem_append] at hm
  rcases hm with hm | hm | hm | hm
  · exact (belowVar_notMem_wvars_streamPrepareAtDepthCom
      q_top cap mb j phi h) hm
  · exact (belowVar_notMem_wvars_streamInnerCom hinner h) hm
  · exact (belowVar_notMem_wvars_streamScatterRestoreCom
      q_top cap mb j phi h) hm
  · exact (belowVar_notMem_wvars_streamReadbackCom
      q_top cap mb j phi h) hm

/-- The depth-storage renaming fixes every name read by a parent play record. -/
theorem playRec_of_renEnv_streamDepthSwap
    {B cap j : ℕ} {G : SimpleGraph (Fin n)} {M Gm : ℕ → ℕ} {σ : Env}
    (h : PlayRec B cap G j M Gm
      (Lax3Proofs.Refine.ScatterBlock.renEnv (streamDepthSwap j) σ)) :
    PlayRec B cap G j M Gm σ :=
  h.congr
    (fun _ _ => by simp only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars])
    (fun a _ => by simp only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_resName])
    (fun a _ => by simp only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_gamName])
    (fun a _ => by simp only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_parName])

open Classical in
/-- The cover-free scatter fold followed by the two-instruction restoration
of the row length. -/
theorem scatterRestoreStep {bw nb Kb Ki K : ℕ}
    {B q_top cap mb ns nt ell j tail : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T A₀ : ℕ → ℕ} {C C' : ℕ → ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv Gam : ℕ → ℕ}
    (hcsr : Lax3Proofs.RamBfs.CsrGraph G ns O T) {d : ℕ}
    (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → A₀ (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, Lax3Proofs.Refine.ScatterBlock.BallBudget n r G Alv O bw nb)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ s ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        s.r + 1 < B ∧ s.t + n + mb < B ∧
          deadAtomKX s.β n X.ncard mb bw nb s.t ≤ Kb)
    (hcost : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hK : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ K)
    (htailB : tail < B) :
    Spec B
      (fun σ => DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ ∧
        σ.vars (xpName j) = tail)
      (streamScatterRestoreCom q_top cap mb φ j)
      (fun σ σ' =>
        DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ' ∧
        σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
        σ'.vars "tail" = tail ∧ σ'.vars (xpName j) = tail ∧
        ∀ i, ∀ hi : i < (tablesAt q_top cap mb φ j).length,
          ∀ s ∈ (bcAtomsOf q_top (stepFml cap mb j
              (tablesAt q_top cap mb φ j)[i])).2,
            σ'.vars (flgName j i (posOf s (bcAtomsOf q_top
              (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≤ 1 ∧
            (σ'.vars (flgName j i (posOf s (bcAtomsOf q_top
              (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≠ 0 ↔
              ScatVal (stepArenaP (Lax3Proofs.RamBfs.masked G A₀) X w)
                (stepColoringP cap (Lax3Proofs.RamBfs.masked G A₀)
                  (colRead n C (sigL cap mb j)) X w) s))
      (K + 2) := by
  have hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ :=
    fun γ hγ => (tableRank_of_mem_tablesAt (j + 1) γ hγ).1
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨τ, hr, hview, hout, hcur, -, hflags⟩ :=
    (scatterViewStep hcsr hB hXalive hbud hbnd hcost hK).run hσ.1
  have hxp : τ.vars (xpName j) = tail := by
    rw [hr.frame_var _ (xpName_notMem_streamScatterCom hloc)]
    exact hσ.2
  have hexp : (Expr.var (xpName j)).evalB B τ = some tail := by
    rw [evalB_var (by rw [hxp]; exact htailB), hxp]
  let τ' := τ.setVar "tail" tail
  have hrestore : Run B (.assign "tail" (.var (xpName j))) τ τ' 2 := by
    simpa [τ', Expr.size] using Run.assign hexp
  have hview' : DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' τ' :=
    DeadView.setVar hview "tail" (by decide)
      (by simp [mnumName, String.ext_iff]) (by simp [kkName, String.ext_iff]) tail
  refine ⟨τ', K + 2, ?_, le_rfl, hview', ?_, ?_, ?_, ?_, ?_⟩
  · simpa [streamScatterRestoreCom, streamScatterCom] using hr.seq hrestore
  · simpa [τ'] using hout
  · simpa [τ', curName, String.ext_iff] using hcur
  · simp [τ']
  · simpa [τ', xpName, String.ext_iff] using hxp
  · intro i hi s hs
    simpa [τ', flgName, String.ext_iff] using hflags i hi s hs

/-! ## Rebuilding and framing the parent level -/

/- The child's returned common memory together with the explicit below-depth
frame reconstructs the parent `LevelPre`. -/
theorem levelPre_after_inner
    {B q_top cap mb ns nt j q c tail bits : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {O T A₀ Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Alv Gam : ℕ → ℕ} {C' : ℕ → ℕ → ℕ}
    {D : Set (Fin n)} {σ₀ σ : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₀)
    (hc : LevelPostD B q_top cap mb φ G ns nt O T (j + 1) Alv Gam C' D σ₀ σ)
    (hf : StreamParentFrame j q c tail bits σ₀ σ) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ := by
  obtain ⟨hn, hoff, htgt, -, -, -, -, -, -, hlm, hdm, hm, hom, hpad, htB, -⟩ := hc.1
  obtain ⟨-, -, -, hA, hGm, hC, hAb, hGmb, hCb, -, -, -, -, -, -,
    Mem, mm, hMem, hmm, henum, hmemB⟩ := hp
  have halv : Lax3Proofs.RamDriverWrites.BelowArr (j + 1) (alvName j) :=
    ⟨j, Nat.lt_succ_self j, Or.inl rfl⟩
  have hgam : Lax3Proofs.RamDriverWrites.BelowArr (j + 1) (gamName j) :=
    ⟨j, Nat.lt_succ_self j, Or.inr (Or.inl rfl)⟩
  have hcol : ∀ s, Lax3Proofs.RamDriverWrites.BelowArr (j + 1) (colName j s) := by
    intro s
    refine ⟨j, Nat.lt_succ_self j, ?_⟩
    right; right; right; right; right; right; right; right
    right; right; right; right; right; right
    exact Or.inl ⟨s, rfl⟩
  have hmem : Lax3Proofs.RamDriverWrites.BelowArr (j + 1) (memName j) := by
    refine ⟨j, Nat.lt_succ_self j, ?_⟩
    right; right; right; right; right; right; right; right
    right; right; right; right
    exact Or.inl rfl
  refine ⟨hn, hoff, htgt, ?_, ?_, ?_, hAb, hGmb, hCb, hlm, hdm, hm, hom,
    hpad, htB, Mem, mm, ?_, ?_, henum, hmemB⟩
  · exact (hf.depth_arr _ halv).trans hA
  · exact (hf.depth_arr _ hgam).trans hGm
  · intro s hs
    exact (hf.depth_arr _ (hcol s)).trans (hC s hs)
  · exact (hf.depth_arr _ hmem).trans hMem
  · exact hf.member_count_var.trans hmm

open Classical in
/-- A parent level is unchanged by the cover-free scatter fold. -/
theorem levelPre_run_streamScatterCom
    {B q_top cap mb ns nt j K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {O T A₀ Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B (streamScatterCom q_top cap mb φ j) σ σ' K)
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  have hfa (a : String)
      (ha : a ∉ ["mem", "alv", "dist", "exc", "q", "qd"])
      (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" a) :
      a ∉ (streamScatterCom q_top cap mb φ j).warrs :=
    notMem_warrs_streamScatterCom hloc ha hbb
  have hfv (y : String)
      (h₁ : y ∉ ["kc", "ke", "of", "oz", "oi", "oc", "mm", "ak", "av", "ac", "ax",
        "os", "flag"])
      (h₂ : y ∉ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
        "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"])
      (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" y)
      (henv : ∀ e, y ≠ envName e) (hflg : ∀ i k, y ≠ flgName j i k) :
      y ∉ (streamScatterCom q_top cap mb φ j).wvars :=
    notMem_wvars_streamScatterCom hloc h₁ h₂ hbb henv hflg
  apply Lax3Proofs.RamDriverCompose.levelPre_run hp hr
  · exact hfv "n" (by decide) (by decide)
      (not_ext_bb_short (by decide))
      (fun e => by simp [envName, String.ext_iff])
      (fun i k => by simp [flgName, String.ext_iff])
  · exact hfv "m" (by decide) (by decide)
      (not_ext_bb_short (by decide))
      (fun e => by simp [envName, String.ext_iff])
      (fun i k => by simp [flgName, String.ext_iff])
  · exact hfv "lw" (by decide) (by decide)
      (not_ext_bb_of_cons rfl (by decide))
      (fun e => by simp [envName, String.ext_iff])
      (fun i k => by simp [flgName, String.ext_iff])
  · exact hfa "off" (by decide) (not_ext_bb_of_cons rfl (by decide))
  · exact hfa "tgt" (by decide) (not_ext_bb_of_cons rfl (by decide))
  · exact hfa _ (by simp [alvName, String.ext_iff])
      (Lax3Proofs.RamDriverFrames.not_bbExt_alvName j)
  · exact hfa _ (by simp [gamName, String.ext_iff])
      (Lax3Proofs.RamDriverFrames.not_bbExt_gamName j)
  · intro s
    exact hfa _ (by simp [colName, String.ext_iff])
      (Lax3Proofs.RamDriverFrames.not_bbExt_colName j s)
  · intro a ha
    simp only [Lax3Proofs.RamDriverCompose.zeroArrs, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hfa _ (by decide) (not_ext_bb_of_cons rfl (by decide))
  · exact hfa _ (by simp [memName, String.ext_iff])
      (Lax3Proofs.RamDriverFrames.not_bbExt_memName j)
  · exact hfv _ (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (not_ext_bb_mnumName j)
      (fun e => by simp [mnumName, envName, String.ext_iff])
      (fun i k => by simp [mnumName, flgName, String.ext_iff])

/-- Restoring the streamed tail scalar also leaves the parent level intact. -/
theorem levelPre_run_streamScatterRestoreCom
    {B q_top cap mb ns nt j K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {O T A₀ Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {σ σ' : Env}
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hr : Run B (streamScatterRestoreCom q_top cap mb φ j) σ σ' K)
    (hloc : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
  rw [streamScatterRestoreCom] at hr
  obtain ⟨k, hk, hrun⟩ := hr
  cases hrun with
  | seq hscatter hrestore =>
      have hp' := levelPre_run_streamScatterCom hp (Run.of_bigStepB hscatter) hloc
      cases hrestore with
      | assign _ =>
          exact levelPre_setVar hp' "tail" (by decide) (by decide) (by decide)
            (by simp [mnumName, String.ext_iff]) _

/-! ## The recursive arena is paid by the streamed row -/

/-- The child mask produced from a streamed row is supported on that row's
mathematical cluster.  Consequently its ambient-graph arena weight is at
most the CSR weight assigned to the current centre.  This is the local
charging fact that lets the outer loop retain its genuine sigma-shaped
recursive cost instead of using one uniform child bound for every centre. -/
theorem childArenaWeight_le_activeBallWeightAtDepth
    {B n q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T)
    (h : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell
      φ G A₀ π centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ) :
    Lax3Proofs.Refine.MassWeight.arenaWeight n G Alv ≤
      Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
        n G A₀ π centre O cap c := by
  rw [Lax3Proofs.Refine.MassWeight.arenaWeight_eq_csr hcsr Alv,
    Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight]
  apply Lax3Proofs.Refine.MassWeight.wsum_mono
  intro v hv
  rw [← h.cluster_set]
  exact (h.data.1.2.2.2.2.2.2.1 v).mp hv |>.2.1

/-- Every search ball in the recursive child mask is contained in the
current mathematical cluster.  The same active-cluster weight therefore
budgets both its CSR rows and its number of vertices, independently of the
radius requested by the dead-atom scatter pass. -/
theorem childBallBudgetAtDepth
    {B n q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell
      φ G A₀ π centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ) :
    ∀ r : ℕ, Lax3Proofs.Refine.ScatterBlock.BallBudget n r G Alv O
      (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
        n G A₀ π centre O cap c)
      (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
        n G A₀ π centre O cap c) := by
  intro r s hs
  refine ⟨Lax3Proofs.Refine.CoverActiveBudget.activeClusterNat
      G A₀ π centre cap c, ?_, ?_, ?_⟩
  · intro v hv hAlv _
    apply Finset.mem_image.mpr
    refine ⟨⟨v, hv⟩, ?_, rfl⟩
    rw [Lax3Proofs.Refine.CoverActiveBudget.mem_activeClusterFin,
      ← h.cluster_set]
    exact (h.data.1.2.2.2.2.2.2.1 ⟨v, hv⟩).mp hAlv |>.2.1
  · exact Lax3Proofs.Refine.CoverActiveBudget.activeClusterNat_rows_le_weight
      (n := n) (G := G) (A₀ := A₀) (π := π) (centre := centre)
      (O := O) (r := cap) c
  · exact Lax3Proofs.Refine.CoverActiveBudget.activeClusterNat_card_le_weight
      (n := n) (G := G) (A₀ := A₀) (π := π) (centre := centre)
      (O := O) (r := cap) c

/-! ## The complete post-recursive centre boundary -/

open Classical in
/-- **A complete streamed centre after descent preparation.**  The concrete
recursive call, dead-aware scatter, protected tail restoration, and streamed
readback compose without an accumulated cover pointer.  In particular the
readback charge is proportional to `tail`, and its logical two-cell offset
adapter requires no `n * n < B` premise. -/
theorem streamCentreFinishStep
    {B n q_top cap mb ns nt q j c tail bits ell Kinner : ℕ}
    {Kb Ki Kscatter d : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam Gm : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {inner : Com}
    (hchild : StreamLevelImplementsD B q_top cap mb ns nt ell j φ G O T
      Alv Gam C' (killSet A₀ (markSet n Xa) (markSet n Wa)) inner Kinner)
    (hframes : StreamInnerFrames j inner)
    (hcap : cap = rhoMinus 0 q_top)
    (hcsr : Lax3Proofs.RamBfs.CsrGraph G ns O T)
    (hB : WordBoundK B n d ns cap mb)
    (hcentres : CentresBy n q A₀ π centre)
    (hbitsB : bits < B) (hpow : n ≤ 2 ^ bits)
    (hbitsEq : bits = Nat.clog 2 n)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ s ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        s.r + 1 < B ∧ s.t + n + mb < B ∧
          deadAtomKX s.β n (markSet n Xa).ncard mb
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap c)
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap c) s.t ≤ Kb)
    (hcost : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hK : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Kscatter) :
    Spec B
      (fun σ =>
        StreamKillOutAtDepth B q_top cap mb ns nt (n * n) q j c tail bits ell
          φ G A₀ π centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ ∧
        PlayRec B cap G j A₀ Gm σ ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ ∧
        TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ell φ σ ∧
        StreamScratchFrom B n cap mb ell (j + 1) σ)
      (streamCentreFinishCom q_top cap mb j φ inner)
      (fun σ σ' =>
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ' ∧
        PlayRec B cap G j A₀ Gm σ' ∧
        TablesSized q_top cap mb φ n σ' ∧
        σ'.out = σ.out ∧ σ'.vars (curName j) = c ∧
        σ'.arrs (xmmName j) = arrOf (n * n) Xmem ∧
        σ'.arrs (asgName j) = arrOf n asg ∧
        StreamSortedOut B ns nt (n * n) q cap c tail bits G A₀ π centre O T
          Xmem asg M (Lax3Proofs.Refine.ScatterBlock.renEnv
            (streamDepthSwap j) σ') ∧
        StreamReleasePre n (n * n) tail cap mb j Xmem σ' ∧
        StreamScratchFrom B n cap mb ell (j + 1) σ' ∧
        ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
          ∃ Tb Tb₀ : ℕ → ℕ,
            σ'.arrs (tabName j i) = arrOf n Tb ∧
            σ.arrs (tabName j i) = arrOf n Tb₀ ∧
            (∀ v : Fin n, A₀ (v : ℕ) = 0 ∨ asg (v : ℕ) ≠ c →
              Tb (v : ℕ) = Tb₀ (v : ℕ)) ∧
            ∀ v : Fin n, A₀ (v : ℕ) ≠ 0 → asg (v : ℕ) = c →
              Tb (v : ℕ) ≤ 1 ∧
              (Tb (v : ℕ) ≠ 0 ↔
                Sat (Lax3Proofs.RamBfs.masked G A₀)
                  (colRead n C (sigL cap mb j)) (fun _ => v)
                  (tablesAt q_top cap mb φ j)[i]))
      (streamCentreFinishCost q_top cap mb j tail Kinner Kscatter φ) := by
  refine Spec.of_exists fun σ hpre => ?_
  obtain ⟨hsrc, hparent, hlevel, htables, hbase, hscratch⟩ := hpre
  have hcq : c < q := hsrc.sorted.row.state.pos_le
  have hqB : q < B := lt_of_le_of_lt hcentres.count_le hB.n_lt
  have hcB : c < B := lt_trans hcq hqB
  have htailB : tail < B := lt_of_le_of_lt hsrc.sorted.row.tail_le hB.n_lt
  have hlocal : ∀ γ ∈ tablesAt q_top cap mb φ (j + 1), IsLocal γ :=
    fun γ hγ => (tableRank_of_mem_tablesAt (j + 1) γ hγ).1
  have hXalive : ∀ v : Fin n, v ∈ markSet n Xa → A₀ (v : ℕ) ≠ 0 := by
    intro v hv
    have hv' : v ∈ Lax3Proofs.Refine.MassMath.clusterAt G A₀ π centre cap c := by
      rw [← hsrc.cluster_set]
      exact hv
    exact Lax3Proofs.Refine.MassAlive.clusterAt_subset_alive
      (hcentres.alive c hcq) hv'
  have hX : ∀ v : Fin n, v ∈ markSet n Xa ↔
      InCluster (Lax3Proofs.RamBfs.masked G A₀) π cap (centre c) (v : ℕ) := by
    intro v
    change v ∈ markSet n Xa ↔ v ∈
      Lax3Proofs.Refine.MassMath.clusterAt G A₀ π centre cap c
    rw [hsrc.cluster_set]
  obtain ⟨σ₁, hr₁, hpost₁, hframe₁, hscratch₁⟩ :=
    (streamInnerStep hchild hframes hqB hcB htailB hbitsB hpow hbitsEq).run
      ⟨hsrc, hlevel, htables, hbase, hscratch⟩
  have hbase₁ : BaseArrs B q_top cap mb ell φ σ₁ := hbase.run hr₁
  have hdead₁ : DeadView B q_top cap mb ns nt ell j φ G O T A₀ C
      (markSet n Xa) (markSet n Wa) w Alv Gam C' σ₁ :=
    deadView_after_inner hsrc hpost₁ hframe₁ hbase₁
  obtain ⟨σ₂, hr₂, hdead₂, hout₂, hcur₂, htail₂, hxp₂, hflags₂⟩ :=
    (scatterRestoreStep hcsr hB hXalive (childBallBudgetAtDepth hsrc)
      hbnd hcost hK htailB).run
      ⟨hdead₁, hframe₁.saved.2.2.1⟩
  have hscratch₂ : StreamScratchFrom B n cap mb ell (j + 1) σ₂ := by
    apply hscratch₁.run hr₂
    · intro d _ _
      exact notMem_warrs_streamScatterRestoreCom hlocal
        (by simp [cpsName, String.ext_iff])
        (by
          simpa [cpsName] using
            (RamDriverWrites.not_ext_bb_append (p := "cs")
              (by decide) (by decide) (toString d)))
    · intro d _ _
      exact notMem_warrs_streamScatterRestoreCom hlocal
        (by simp [cluName, String.ext_iff])
        (by
          simpa [cluName] using
            (RamDriverWrites.not_ext_bb_append (p := "clu")
              (by decide) (by decide) (toString d)))
    · intro d _ _
      exact notMem_warrs_streamScatterRestoreCom hlocal
        (by simp [resName, String.ext_iff])
        (by
          simpa [resName] using
            (RamDriverWrites.not_ext_bb_append (p := "res")
              (by decide) (by decide) (toString d)))
    · intro d _ _
      exact notMem_warrs_streamScatterRestoreCom hlocal
        (by simp [batName, String.ext_iff])
        (by
          simpa [batName] using
            (RamDriverWrites.not_ext_bb_append (p := "bat")
              (by decide) (by decide) (toString d)))
    · intro d _ _
      exact notMem_warrs_streamScatterRestoreCom hlocal
        (by simp [alvName, String.ext_iff])
        (by
          simpa [alvName] using
            (RamDriverWrites.not_ext_bb_append (p := "alv")
              (by decide) (by decide) (toString (d + 1))))
    · intro d _ _
      exact notMem_warrs_streamScatterRestoreCom hlocal
        (by simp [gamName, String.ext_iff])
        (by
          simpa [gamName] using
            (RamDriverWrites.not_ext_bb_append (p := "gam")
              (by decide) (by decide) (toString (d + 1))))
    · intro d _ _ s _
      exact notMem_warrs_streamScatterRestoreCom hlocal
        (by simp [colName, String.ext_iff])
        (by
          simpa [colName, String.append_assoc] using
            (RamDriverWrites.not_ext_bb_append (p := "co")
              (by decide) (by decide)
              (toString (d + 1) ++ "_" ++ toString s)))
  have hlevel₁ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₁ :=
    levelPre_after_inner hlevel hpost₁ hframe₁
  have hparent₁ : PlayRec B cap G j A₀ Gm σ₁ :=
    hparent.congr hframe₁.round_var
      (fun a ha => hframe₁.depth_arr _
        ⟨a, by omega, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)
      (fun a ha => hframe₁.depth_arr _
        ⟨a, by omega, Or.inr (Or.inl rfl)⟩)
      (fun a ha => hframe₁.depth_arr _
        ⟨a, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩)
  have hlevel₂ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₂ :=
    levelPre_run_streamScatterRestoreCom hlevel₁ hr₂ hlocal
  have hparent₂ : PlayRec B cap G j A₀ Gm σ₂ :=
    hparent₁.congr
      (fun a ha => hr₂.frame_var _
        (belowVar_notMem_wvars_streamScatterRestoreCom q_top cap mb j φ
          ⟨a, ha, Or.inl rfl⟩))
      (fun a ha => hr₂.frame_arr _
        (belowArr_notMem_warrs_streamScatterRestoreCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))
      (fun a ha => hr₂.frame_arr _
        (belowArr_notMem_warrs_streamScatterRestoreCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inl rfl)⟩))
      (fun a ha => hr₂.frame_arr _
        (belowArr_notMem_warrs_streamScatterRestoreCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))
  have htables₂ : TablesSized q_top cap mb φ n σ₂ :=
    (htables.run hr₁).run hr₂
  have hxmm₀ : σ.arrs (xmmName j) = arrOf (n * n) Xmem := by
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_xmem] using hsrc.sorted.row_arr
  have hasg₀ : σ.arrs (asgName j) = arrOf n asg := by
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_asg] using hsrc.sorted.asg_arr
  have hxmm₂ : σ₂.arrs (xmmName j) = arrOf (n * n) Xmem := by
    rw [hr₂.frame_arr _ (notMem_warrs_streamScatterRestoreCom hlocal
      (by simp [xmmName, String.ext_iff])
      (Lax3Proofs.RamDriverFrames.not_bbExt_xmmName j)), hframe₁.row_arr]
    exact hxmm₀
  have hasg₂ : σ₂.arrs (asgName j) = arrOf n asg := by
    rw [hr₂.frame_arr _ (notMem_warrs_streamScatterRestoreCom hlocal
      (by simp [asgName, String.ext_iff])
      (Lax3Proofs.RamDriverFrames.not_bbExt_asgName j)), hframe₁.asg_arr]
    exact hasg₀
  have hcurrent₂ : σ₂.vars (curName j) = c :=
    hcur₂.trans hframe₁.saved.2.1
  have htabBelow : ∀ i,
      Lax3Proofs.RamDriverWrites.BelowArr (j + 1) (tabName j i) := by
    intro i
    refine ⟨j, Nat.lt_succ_self j, ?_⟩
    right; right; right; right; right; right; right; right
    right; right; right; right; right; right; right
    exact ⟨i, rfl⟩
  have htab₂₀ : ∀ i, σ₂.arrs (tabName j i) = σ.arrs (tabName j i) := by
    intro i
    rw [hr₂.frame_arr _ (notMem_warrs_streamScatterRestoreCom hlocal
      (by simp [tabName, String.ext_iff])
      (Lax3Proofs.Refine.ScatterDeadTurn.not_ext_bb_tabName j i))]
    exact hframe₁.depth_arr _ (htabBelow i)
  have hclu₀ : σ.arrs (cluName j) = arrOf n Xa := by
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_cluName] using hsrc.colour_state.cluster_arr
  have hres₀ : σ.arrs (resName j) = arrOf n Ra := by
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_resName] using hsrc.colour_state.retained_arr
  have hbat₀ : σ.arrs (batName j) = arrOf n Wa := by
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_batName] using hsrc.batch_arr
  have hcluBelow : Lax3Proofs.RamDriverWrites.BelowArr (j + 1) (cluName j) :=
    ⟨j, Nat.lt_succ_self j, by tauto⟩
  have hresBelow : Lax3Proofs.RamDriverWrites.BelowArr (j + 1) (resName j) :=
    ⟨j, Nat.lt_succ_self j, by tauto⟩
  have hbatBelow : Lax3Proofs.RamDriverWrites.BelowArr (j + 1) (batName j) :=
    ⟨j, Nat.lt_succ_self j, by tauto⟩
  have hclu₂ : σ₂.arrs (cluName j) = arrOf n Xa := by
    rw [hr₂.frame_arr _ (notMem_warrs_streamScatterRestoreCom hlocal
      (by simp [cluName, String.ext_iff])
      (by rw [cluName]; exact RamDriverWrites.not_ext_bb_append (by decide) (by decide) _)),
      hframe₁.depth_arr _ hcluBelow]
    exact hclu₀
  have hres₂ : σ₂.arrs (resName j) = arrOf n Ra := by
    rw [hr₂.frame_arr _ (notMem_warrs_streamScatterRestoreCom hlocal
      (by simp [resName, String.ext_iff])
      (by rw [resName]; exact RamDriverWrites.not_ext_bb_append (by decide) (by decide) _)),
      hframe₁.depth_arr _ hresBelow]
    exact hres₀
  have hbat₂ : σ₂.arrs (batName j) = arrOf n Wa := by
    rw [hr₂.frame_arr _ (notMem_warrs_streamScatterRestoreCom hlocal
      (by simp [batName, String.ext_iff])
      (Lax3Proofs.RamDriverWrites.not_ext_bb_of_belowArr hbatBelow)),
      hframe₁.depth_arr _ hbatBelow]
    exact hbat₀
  have hAlv₂ : σ₂.arrs (alvName (j + 1)) = arrOf n Alv :=
    hdead₂.data.1.2.2.2.1
  have hGam₂ : σ₂.arrs (gamName (j + 1)) = arrOf n Gam :=
    hdead₂.data.1.2.2.2.2.2.2.2.1
  obtain ⟨σ₃, hr₃, hlevel₃, htables₃, hout₃, hcur₃, hxmm₃, hasg₃, hread₃⟩ :=
    (streamReadbackViewStep hcap hB hcentres hX).run
      { level := hlevel₂
        tables := htables₂
        dead := hdead₂
        row := hsrc.sorted.row
        row_arr := hxmm₂
        asg_arr := hasg₂
        current_var := hcurrent₂
        tail_var := htail₂
        flags := hflags₂ }
  have hscratch₃ : StreamScratchFrom B n cap mb ell (j + 1) σ₃ := by
    apply hscratch₂.run hr₃
    · intro d _ _
      exact notMem_warrs_streamReadbackCom
        (by simp [cpsName, xofName, String.ext_iff])
        (fun i => by simp [cpsName, tabName, String.ext_iff])
    · intro d _ _
      exact notMem_warrs_streamReadbackCom
        (by simp [cluName, xofName, String.ext_iff])
        (fun i => by simp [cluName, tabName, String.ext_iff])
    · intro d _ _
      exact notMem_warrs_streamReadbackCom
        (by simp [resName, xofName, String.ext_iff])
        (fun i => by simp [resName, tabName, String.ext_iff])
    · intro d _ _
      exact notMem_warrs_streamReadbackCom
        (by simp [batName, xofName, String.ext_iff])
        (fun i => by simp [batName, tabName, String.ext_iff])
    · intro d _ _
      exact notMem_warrs_streamReadbackCom
        (by simp [alvName, xofName, String.ext_iff])
        (fun i => by simp [alvName, tabName, String.ext_iff])
    · intro d _ _
      exact notMem_warrs_streamReadbackCom
        (by simp [gamName, xofName, String.ext_iff])
        (fun i => by simp [gamName, tabName, String.ext_iff])
    · intro d _ _ s _
      exact notMem_warrs_streamReadbackCom
        (by simp [colName, xofName, String.ext_iff])
        (fun i => by simp [colName, tabName, String.ext_iff])
  have hparent₃ : PlayRec B cap G j A₀ Gm σ₃ :=
    hparent₂.congr
      (fun a ha => hr₃.frame_var _
        (belowVar_notMem_wvars_streamReadbackCom q_top cap mb j φ
          ⟨a, ha, Or.inl rfl⟩))
      (fun a ha => hr₃.frame_arr _
        (belowArr_notMem_warrs_streamReadbackCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))
      (fun a ha => hr₃.frame_arr _
        (belowArr_notMem_warrs_streamReadbackCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inl rfl)⟩))
      (fun a ha => hr₃.frame_arr _
        (belowArr_notMem_warrs_streamReadbackCom q_top cap mb j φ
          ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))
  have htail₃ : σ₃.vars "tail" = tail := by
    rw [hr₃.frame_var _ tail_notMem_wvars_streamReadbackCom]
    exact htail₂
  have hclu₃ : σ₃.arrs (cluName j) = arrOf n Xa := by
    rw [hr₃.frame_arr _ (notMem_warrs_streamReadbackCom
      (by simp [cluName, xofName, String.ext_iff])
      (fun i => by simp [cluName, tabName, String.ext_iff]))]
    exact hclu₂
  have hres₃ : σ₃.arrs (resName j) = arrOf n Ra := by
    rw [hr₃.frame_arr _ (notMem_warrs_streamReadbackCom
      (by simp [resName, xofName, String.ext_iff])
      (fun i => by simp [resName, tabName, String.ext_iff]))]
    exact hres₂
  have hbat₃ : σ₃.arrs (batName j) = arrOf n Wa := by
    rw [hr₃.frame_arr _ (notMem_warrs_streamReadbackCom
      (by simp [batName, xofName, String.ext_iff])
      (fun i => by simp [batName, tabName, String.ext_iff]))]
    exact hbat₂
  have hAlv₃ : σ₃.arrs (alvName (j + 1)) = arrOf n Alv := by
    rw [hr₃.frame_arr _ (notMem_warrs_streamReadbackCom
      (by simp [alvName, xofName, String.ext_iff])
      (fun i => by simp [alvName, tabName, String.ext_iff]))]
    exact hAlv₂
  have hGam₃ : σ₃.arrs (gamName (j + 1)) = arrOf n Gam := by
    rw [hr₃.frame_arr _ (notMem_warrs_streamReadbackCom
      (by simp [gamName, xofName, String.ext_iff])
      (fun i => by simp [gamName, tabName, String.ext_iff]))]
    exact hGam₂
  have hcol₃ : ∀ s, s < sigL cap mb (j + 1) →
      σ₃.arrs (colName (j + 1) s) = arrOf n (C' s) := by
    intro s hs
    rw [hr₃.frame_arr _ (notMem_warrs_streamReadbackCom
      (Lax3Proofs.RamDriverDescend.colName_ne_xofName _ _ _)
      (fun i => Lax3Proofs.RamDriverBot.colName_ne_tabName _ _ _ _))]
    exact hdead₂.col_arr s hs
  have hcolSup : ∀ s, s < sigL cap mb (j + 1) →
      BlockSupported n 0 tail Xmem (C' s) := by
    intro s hs
    obtain ⟨F, hF, hFsup⟩ := hsrc.colour_state.next_slots s hs
    have heq : ∀ v, v < n → F v = C' s v := by
      intro v hv
      exact eq_of_arrOf_eq (hF.symm.trans (hsrc.colour_arr s hs)) hv
    intro v hv hout
    rw [← heq v hv]
    exact hFsup v hv hout
  have hscatterVar (y : String)
      (h₁ : y ∉ ["kc", "ke", "of", "oz", "oi", "oc", "mm", "ak", "av", "ac", "ax",
        "os", "flag"])
      (h₂ : y ∉ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
        "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"])
      (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" y)
      (henv : ∀ e, y ≠ envName e)
      (hflg : ∀ i k, y ≠ flgName j i k) (ht : y ≠ "tail") :
      σ₂.vars y = σ₁.vars y :=
    hr₂.frame_var y
      (notMem_wvars_streamScatterRestoreCom hlocal h₁ h₂ hbb henv hflg ht)
  have hreadVar (y : String) (hz : y ≠ "z") (hze : y ≠ "zend")
      (hrv : y ≠ "rv") : σ₃.vars y = σ₂.vars y :=
    hr₃.frame_var y (notMem_wvars_streamReadbackCom hz hze hrv)
  have hq₂' : σ₂.vars "qn" = q := by
    exact (hscatterVar "qn" (by decide) (by decide)
      (not_ext_bb_of_cons rfl (by decide))
      (fun e => by simp [envName, String.ext_iff])
      (fun i k => by simp [flgName, String.ext_iff]) (by decide)).trans
        hframe₁.q_var
  have hc₂' : σ₂.vars "c" = c := by
    exact (hscatterVar "c" (by decide) (by decide)
      (not_ext_bb_short (by decide))
      (fun e => by simp [envName, String.ext_iff])
      (fun i k => by simp [flgName, String.ext_iff]) (by decide)).trans
        hframe₁.centre_var
  have hbits₂ : σ₂.vars "rsbits" = bits := by
    exact (hscatterVar "rsbits" (by decide) (by decide)
      (not_ext_bb_of_cons rfl (by decide))
      (fun e => by simp [envName, String.ext_iff])
      (fun i k => by simp [flgName, String.ext_iff]) (by decide)).trans
        hframe₁.bits_var
  have hxp₂' : σ₂.vars "xp" = tail := by
    exact (hscatterVar "xp" (by decide) (by decide)
      (not_ext_bb_of_cons rfl (by decide))
      (fun e => by simp [envName, String.ext_iff])
      (fun i k => by simp [flgName, String.ext_iff]) (by decide)).trans
        hframe₁.pointer_var
  have hq₃ : σ₃.vars "qn" = q :=
    (hreadVar "qn" (by decide) (by decide) (by decide)).trans hq₂'
  have hc₃' : σ₃.vars "c" = c :=
    (hreadVar "c" (by decide) (by decide) (by decide)).trans hc₂'
  have hxp₃ : σ₃.vars "xp" = tail :=
    (hreadVar "xp" (by decide) (by decide) (by decide)).trans hxp₂'
  have hbits₃ : σ₃.vars "rsbits" = bits :=
    (hreadVar "rsbits" (by decide) (by decide) (by decide)).trans hbits₂
  have hscatterArr (a : String)
      (hfix : a ∉ ["mem", "alv", "dist", "exc", "q", "qd"])
      (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" a) :
      σ₂.arrs a = σ₁.arrs a :=
    hr₂.frame_arr a (notMem_warrs_streamScatterRestoreCom hlocal hfix hbb)
  have hreadArr (a : String) (hxof : a ≠ xofName j)
      (htab : ∀ i, a ≠ tabName j i) : σ₃.arrs a = σ₂.arrs a :=
    hr₃.frame_arr a (notMem_warrs_streamReadbackCom hxof htab)
  have hpdsNotBB : ¬ Lax3Proofs.RamDriverBot.Ext "bb" (pdsName j) := by
    rw [pdsName, balAltName]
    exact Lax3Proofs.RamDriverWrites.not_ext_bb_append (by decide) (by decide) _
  have hord₃ : σ₃.arrs (ordName j) = σ.arrs (ordName j) := by
    exact (hreadArr (ordName j)
      (by simp [ordName, xofName, String.ext_iff])
      (fun i => by simp [ordName, tabName, String.ext_iff])).trans
        ((hscatterArr (ordName j) (by simp [ordName, String.ext_iff])
          (DeadSweep.not_ext_bb_ordName j)).trans hframe₁.ord_arr)
  have hcps₃ : σ₃.arrs (cpsName j) = σ.arrs (cpsName j) := by
    exact (hreadArr (cpsName j)
      (Lax3Proofs.RamDriverCompose.cpsName_ne_xofName j j)
      (fun i => by simp [cpsName, tabName, String.ext_iff])).trans
        ((hscatterArr (cpsName j) (by simp [cpsName, String.ext_iff])
          (DeadSweep.not_ext_bb_cpsName j)).trans hframe₁.mask_arr)
  have hpds₃ : σ₃.arrs (pdsName j) = σ.arrs (pdsName j) := by
    exact (hreadArr (pdsName j)
      (by simp [pdsName, balAltName, xofName, String.ext_iff])
      (fun i => by simp [pdsName, balAltName, tabName, String.ext_iff])).trans
        ((hscatterArr (pdsName j)
          (by simp [pdsName, balAltName, String.ext_iff]) hpdsNotBB).trans
            hframe₁.dist_arr)
  have hlevel₃keep := hlevel₃
  obtain ⟨hn₃, hoff₃, htgt₃, -, -, -, -, -, -, hlevelMem₃, -, -, -, -, -, -⟩ :=
    hlevel₃keep
  have hdist₃ : Lax3Proofs.Refine.BfsBlockMask.DistClean n (2 * cap) M
      (Lax3Proofs.Refine.ScatterBlock.renEnv (streamDepthSwap j) σ₃) := by
    apply Lax3Proofs.Refine.CoverActiveTurn.distClean_of_arrs_eq
      hsrc.sorted.dist_clean
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap_dist] using hpds₃
  have hqueue₃ : ∃ Q, (Lax3Proofs.Refine.ScatterBlock.renEnv
      (streamDepthSwap j) σ₃).arrs "q" = arrOf n Q := by
    obtain ⟨Q, hQ⟩ := hlevelMem₃.1 ("q", n) (by simp)
    exact ⟨Q, by simpa [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap] using hQ⟩
  have hqdist₃ : ∃ QD, (Lax3Proofs.Refine.ScatterBlock.renEnv
      (streamDepthSwap j) σ₃).arrs "qd" = arrOf n QD := by
    obtain ⟨QD, hQD⟩ := hlevelMem₃.1 ("qd", n) (by simp)
    exact ⟨QD, by simpa [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      streamDepthSwap] using hQD⟩
  have hsorted₃ : StreamSortedOut B ns nt (n * n) q cap c tail bits G A₀ π
      centre O T Xmem asg M (Lax3Proofs.Refine.ScatterBlock.renEnv
        (streamDepthSwap j) σ₃) := by
    refine {
      row := hsrc.sorted.row
      n_var := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using hn₃
      q_var := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using hq₃
      centre_var := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using hc₃'
      pointer_var := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using hxp₃
      tail_var := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using htail₃
      bits_var := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_vars] using hbits₃
      centre_arr := by
        simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
          streamDepthSwap_ord] using hord₃.trans (by
            simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
              streamDepthSwap_ord] using hsrc.sorted.centre_arr)
      off_arr := by simpa [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
        streamDepthSwap] using hoff₃
      target_arr := by simpa [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
        streamDepthSwap] using htgt₃
      mask_arr := by
        simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
          streamDepthSwap_alv] using hcps₃.trans (by
            simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
              streamDepthSwap_alv] using hsrc.sorted.mask_arr)
      row_arr := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
        streamDepthSwap_xmem] using hxmm₃
      row_fit := hsrc.sorted.row_fit
      asg_arr := by simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
        streamDepthSwap_asg] using hasg₃
      dist_clean := hdist₃
      queue_arr := hqueue₃
      qdist_arr := hqdist₃
      mask_bound := hsrc.sorted.mask_bound }
  have hrelease₃ : StreamReleasePre n (n * n) tail cap mb j Xmem σ₃ := {
    tail_var := htail₃
    row_arr := hxmm₃
    tail_le := hsrc.sorted.row.tail_le
    row_fit := hsrc.sorted.row.tail_le.trans hsrc.sorted.row_fit
    index_bound := hsrc.sorted.row.mem_lt
    cluster := ⟨Xa, hclu₃, hsrc.supports.cluster⟩
    retained := ⟨Ra, hres₃, hsrc.supports.retained⟩
    batch := ⟨Wa, hbat₃, hsrc.supports.batch⟩
    child := ⟨Alv, hAlv₃, hsrc.supports.child⟩
    game := ⟨Gam, hGam₃, hsrc.supports.game⟩
    colours := fun s hs => ⟨C' s, hcol₃ s hs, hcolSup s hs⟩ }
  refine ⟨σ₃, streamCentreFinishCost q_top cap mb j tail Kinner Kscatter φ,
    ?_, le_rfl, hlevel₃, hparent₃, htables₃, ?_, ?_, hxmm₃, hasg₃, hsorted₃,
    hrelease₃, hscratch₃, ?_⟩
  · simpa [streamCentreFinishCom, streamCentreFinishCost] using
      hr₁.seq (hr₂.seq hr₃)
  · exact hout₃.trans (hout₂.trans hframe₁.out_eq)
  · exact hcur₃.trans hcurrent₂
  · intro i hi
    obtain ⟨Tb, Tb₀, hTb, hTb₀, hkeep, hsem⟩ := hread₃ i hi
    refine ⟨Tb, Tb₀, hTb, ?_, hkeep, hsem⟩
    rw [← htab₂₀ i]
    exact hTb₀

open Classical in
/-- **One complete sorted streamed centre.**  The theorem starts before the
descent preparation and ends after recursive evaluation, dead-aware scatter,
and row-local readback.  The parent table rows outside this centre are framed
all the way back to the input state; assigned vertices in the current row are
read back with their exact formula semantics. -/
theorem streamCentreStep
    {B n q_top cap mb ns nt q j c tail bits ell Kinner : ℕ}
    {Kb Ki Kscatter d : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {inner : Com}
    (hchild : ∀ (Xa Ra Wa Alv Gam : ℕ → ℕ)
        (C' : ℕ → ℕ → ℕ) (w : Fin mb → Fin n),
      Lax3Proofs.Refine.MassWeight.arenaWeight n G Alv ≤
          Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
            n G A₀ π centre O cap c →
      StreamLevelImplementsD B q_top cap mb ns nt ell j φ G O T
        Alv Gam C' (killSet A₀ (markSet n Xa) (markSet n Wa)) inner Kinner)
    (hframes : StreamInnerFrames j inner)
    (hcap : cap = rhoMinus 0 q_top)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T) (hnt : ns ≤ nt)
    (hB : WordBoundK B n d ns cap mb)
    (hcentres : CentresBy n q A₀ π centre)
    (hmb : mb = ell * (2 * cap + 1)) (hjl : j < ell)
    (hbitsB : bits < B) (hpow : n ≤ 2 ^ bits)
    (hbitsEq : bits = Nat.clog 2 n)
    (hbnd : ∀ (Xa : ℕ → ℕ) β,
        β ∈ tablesAt q_top cap mb φ j →
      ∀ s ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        (markSet n Xa).ncard ≤
            Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap c →
          s.r + 1 < B ∧ s.t + n + mb < B ∧
          deadAtomKX s.β n (markSet n Xa).ncard mb
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap c)
            (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
              n G A₀ π centre O cap c) s.t ≤ Kb)
    (hcost : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hK : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ Kscatter) :
    Spec B
      (fun σ =>
        StreamPreparePre B q_top cap mb ns nt (n * n) q j c tail bits ell φ G A₀ π
          centre O T Xmem asg M Gm C
          (Lax3Proofs.Refine.ScatterBlock.renEnv (streamDepthSwap j) σ) ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ ∧
        TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ell φ σ ∧
        StreamScratchFrom B n cap mb ell (j + 1) σ)
      (streamCentreCom q_top cap mb j φ inner)
      (fun σ σ' =>
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ' ∧
        PlayRec B cap G j A₀ Gm σ' ∧
        TablesSized q_top cap mb φ n σ' ∧
        σ'.out = σ.out ∧ σ'.vars (curName j) = c ∧
        σ'.arrs (xmmName j) = arrOf (n * n) Xmem ∧
        σ'.arrs (asgName j) = arrOf n asg ∧
        StreamSortedOut B ns nt (n * n) q cap c tail bits G A₀ π centre O T
          Xmem asg M (Lax3Proofs.Refine.ScatterBlock.renEnv
            (streamDepthSwap j) σ') ∧
        StreamReleasePre n (n * n) tail cap mb j Xmem σ' ∧
        StreamScratchFrom B n cap mb ell (j + 1) σ' ∧
        ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
          ∃ Tb Tb₀ : ℕ → ℕ,
            σ'.arrs (tabName j i) = arrOf n Tb ∧
            σ.arrs (tabName j i) = arrOf n Tb₀ ∧
            (∀ v : Fin n, A₀ (v : ℕ) = 0 ∨ asg (v : ℕ) ≠ c →
              Tb (v : ℕ) = Tb₀ (v : ℕ)) ∧
            ∀ v : Fin n, A₀ (v : ℕ) ≠ 0 → asg (v : ℕ) = c →
              Tb (v : ℕ) ≤ 1 ∧
              (Tb (v : ℕ) ≠ 0 ↔
                Sat (Lax3Proofs.RamBfs.masked G A₀)
                  (colRead n C (sigL cap mb j)) (fun _ => v)
                  (tablesAt q_top cap mb φ j)[i]))
      (streamCentreCost q_top cap mb j tail
        (expandRowSum O Xmem 0 tail)
      (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
          n G A₀ π centre O cap c) Kinner Kscatter φ) := by
  refine Spec.of_exists fun σ hpre => ?_
  obtain ⟨hprepare₀, hlevel₀, htables₀, hbase₀, hscratch₀⟩ := hpre
  obtain ⟨σ₁, hr₁, hprep₁⟩ :=
    (streamPrepareAtDepthStep hcentres hcsr.csr hnt hB hmb hjl).run
      ⟨hprepare₀, hlevel₀, htables₀, hbase₀⟩
  obtain ⟨Xa, Mm, Ra, Wa, Alv, Gam, Mem, mm, w, C', hkill₁,
    hparentLog₁, hlevel₁, htables₁, hbase₁, hout₁⟩ := hprep₁
  have hparent₁ : PlayRec B cap G j A₀ Gm σ₁ :=
    playRec_of_renEnv_streamDepthSwap hparentLog₁
  have hscratch₁ : StreamScratchFrom B n cap mb ell (j + 1) σ₁ :=
    streamScratchFrom_run_streamPrepareAtDepthCom hscratch₀ hr₁
  have hchild₁ := hchild Xa Ra Wa Alv Gam C' w
    (childArenaWeight_le_activeBallWeightAtDepth hcsr hkill₁)
  have hXaCard : (markSet n Xa).ncard ≤
      Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
        n G A₀ π centre O cap c := by
    rw [hkill₁.cluster_set]
    calc
      (Lax3Proofs.Refine.MassMath.clusterAt G A₀ π centre cap c).ncard =
          (Set.toFinite (Lax3Proofs.Refine.MassMath.clusterAt
            G A₀ π centre cap c)).toFinset.card :=
        Set.ncard_eq_toFinset_card _ _
      _ ≤ Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
          n G A₀ π centre O cap c := by
        simpa only [Lax3Proofs.Refine.CoverActiveBudget.activeClusterFin] using
          (Lax3Proofs.Refine.CoverActiveBudget.activeClusterFin_card_le_weight
            (n := n) (G := G) (A₀ := A₀) (π := π) (centre := centre)
            (O := O) (r := cap) c)
  obtain ⟨σ₂, hr₂, hfinish₂⟩ :=
    (streamCentreFinishStep hchild₁ hframes hcap hcsr.csr hB
      hcentres hbitsB hpow hbitsEq
        (fun β hβ s hs => hbnd Xa β hβ s hs hXaCard) hcost hK).run
      ⟨hkill₁, hparent₁, hlevel₁, htables₁, hbase₁, hscratch₁⟩
  obtain ⟨hlevel₂, hparent₂, htables₂, hout₂, hcur₂, hxmm₂, hasg₂, hsorted₂,
    hrelease₂, hscratch₂, hread₂⟩ := hfinish₂
  refine ⟨σ₂, _, ?_, le_rfl, hlevel₂, hparent₂, htables₂,
    hout₂.trans hout₁, hcur₂, hxmm₂, hasg₂, hsorted₂, hrelease₂,
    hscratch₂, ?_⟩
  · simpa [streamCentreCom, streamCentreCost] using hr₁.seq hr₂
  · intro i hi
    obtain ⟨Tb, Tb₁, hTb, hTb₁, hkeep, hsem⟩ :=
      hread₂ i hi
    refine ⟨Tb, Tb₁, hTb, ?_, hkeep, hsem⟩
    rw [← hr₁.frame_arr _
      (tabName_notMem_streamPrepareAtDepthCom (q_top := q_top)
        (cap := cap) (mb := mb) (j := j) (i := i) (φ := φ))]
    exact hTb₁

end Lax3Proofs.Refine.CoverActiveStreamCentre
