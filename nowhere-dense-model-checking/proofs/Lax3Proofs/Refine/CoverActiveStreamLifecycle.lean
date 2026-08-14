import Lax3Proofs.Refine.CoverActiveStreamCentre

/-!
# Iterating one streamed active-cover centre

This module closes the operational loop around a verified centre: it frames
the persistent sorted state through row-local release and advances the centre
counter to the next progressive-cover prefix.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamLifecycle

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster (killSet markSet)
open Lax3Proofs.RamDriverDescend (expandRowSum)
open Lax3Proofs.Refine.CoverActiveStreamCentre
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.CoverActiveStreamScratch
open Lax3Proofs.Refine.CoverActiveStreamPrepare
open Lax3Proofs.Refine.CoverActiveStreamRelease
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.CoverActiveStreamTurn
open Lax3Proofs.Refine.ScatterDeadTurn (deadAtomKX)
open Lax3Proofs.Refine.CoverActiveTurn (distClean_of_arrs_eq)
open Lax3Proofs.Refine.ScatterBlock (renEnv renEnv_arrs renEnv_vars)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

open Classical in
/-- Releasing successor scratch leaves every component of the sorted streamed
row unchanged. -/
theorem StreamSortedOut.run_streamReleaseCom
    {B ns nt na q cap c tail bits mb j K : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M : ℕ → ℕ} {σ σ' : Env}
    (h : StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
      Xmem asg M (renEnv (streamDepthSwap j) σ))
    (hr : Run B (streamReleaseCom cap mb j) σ σ' K) :
    StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
      Xmem asg M (renEnv (streamDepthSwap j) σ') := by
  have hfv (y : String) (hp : y ≠ "p") (hpend : y ≠ "pend")
      (hcw : y ≠ "cw") : σ'.vars y = σ.vars y :=
    hr.frame_var y (notMem_wvars_streamReleaseCom hp hpend hcw)
  have hfa (a : String)
      (hclu : a ≠ cluName j) (hres : a ≠ resName j)
      (hbat : a ≠ batName j) (halv : a ≠ alvName (j + 1))
      (hgam : a ≠ gamName (j + 1))
      (hcol : ∀ s, s < sigL cap mb (j + 1) → a ≠ colName (j + 1) s) :
      σ'.arrs a = σ.arrs a :=
    hr.frame_arr a
      (notMem_warrs_streamReleaseCom hclu hres hbat halv hgam hcol)
  have hord : σ'.arrs (ordName j) = σ.arrs (ordName j) :=
    hfa _ (by simp [ordName, cluName, String.ext_iff])
      (by simp [ordName, resName, String.ext_iff])
      (by simp [ordName, batName, String.ext_iff])
      (by simp [ordName, alvName, String.ext_iff])
      (by simp [ordName, gamName, String.ext_iff])
      (fun s _ => Ne.symm
        (Lax3Proofs.RamDriverDescend.colName_ne_ordName _ _ _))
  have hcps : σ'.arrs (cpsName j) = σ.arrs (cpsName j) :=
    hfa _ (by simp [cpsName, cluName, String.ext_iff])
      (by simp [cpsName, resName, String.ext_iff])
      (by simp [cpsName, batName, String.ext_iff])
      (by simp [cpsName, alvName, String.ext_iff])
      (by simp [cpsName, gamName, String.ext_iff])
      (fun s _ => by simp [cpsName, colName, String.ext_iff])
  have hxmm : σ'.arrs (xmmName j) = σ.arrs (xmmName j) :=
    hfa _ (by simp [xmmName, cluName, String.ext_iff])
      (by simp [xmmName, resName, String.ext_iff])
      (by simp [xmmName, batName, String.ext_iff])
      (by simp [xmmName, alvName, String.ext_iff])
      (by simp [xmmName, gamName, String.ext_iff])
      (fun s _ => Ne.symm
        (Lax3Proofs.RamDriverDescend.colName_ne_xmmName _ _ _))
  have hasg : σ'.arrs (asgName j) = σ.arrs (asgName j) :=
    hfa _ (by simp [asgName, cluName, String.ext_iff])
      (by simp [asgName, resName, String.ext_iff])
      (by simp [asgName, batName, String.ext_iff])
      (by simp [asgName, alvName, String.ext_iff])
      (by simp [asgName, gamName, String.ext_iff])
      (fun s _ => Ne.symm
        (Lax3Proofs.RamDriverDescend.colName_ne_asgName _ _ _))
  have hpds : σ'.arrs (pdsName j) = σ.arrs (pdsName j) :=
    hfa _ (by simp [pdsName, balAltName, cluName, String.ext_iff])
      (by simp [pdsName, balAltName, resName, String.ext_iff])
      (by simp [pdsName, balAltName, batName, String.ext_iff])
      (by simp [pdsName, balAltName, alvName, String.ext_iff])
      (by simp [pdsName, balAltName, gamName, String.ext_iff])
      (fun s _ => Ne.symm
        (Lax3Proofs.RamDriverDescend.colName_ne_balAltName _ _ _))
  have hoff : σ'.arrs "off" = σ.arrs "off" :=
    hfa _ (by simp [cluName, String.ext_iff])
      (by simp [resName, String.ext_iff]) (by simp [batName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
      (fun s _ => Ne.symm
        (Lax3Proofs.RamDriverDescend.colName_ne_lit (by decide)))
  have htgt : σ'.arrs "tgt" = σ.arrs "tgt" :=
    hfa _ (by simp [cluName, String.ext_iff])
      (by simp [resName, String.ext_iff]) (by simp [batName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
      (fun s _ => Ne.symm
        (Lax3Proofs.RamDriverDescend.colName_ne_lit (by decide)))
  have hq : σ'.arrs "q" = σ.arrs "q" :=
    hfa _ (by simp [cluName, String.ext_iff])
      (by simp [resName, String.ext_iff]) (by simp [batName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
      (fun s _ => Ne.symm
        (Lax3Proofs.RamDriverDescend.colName_ne_lit (by decide)))
  have hqd : σ'.arrs "qd" = σ.arrs "qd" :=
    hfa _ (by simp [cluName, String.ext_iff])
      (by simp [resName, String.ext_iff]) (by simp [batName, String.ext_iff])
      (by simp [alvName, String.ext_iff]) (by simp [gamName, String.ext_iff])
      (fun s _ => Ne.symm
        (Lax3Proofs.RamDriverDescend.colName_ne_lit (by decide)))
  refine {
    row := h.row
    n_var := by simpa only [renEnv_vars] using
      (hfv "n" (by decide) (by decide) (by decide)).trans h.n_var
    q_var := by simpa only [renEnv_vars] using
      (hfv "qn" (by decide) (by decide) (by decide)).trans h.q_var
    centre_var := by simpa only [renEnv_vars] using
      (hfv "c" (by decide) (by decide) (by decide)).trans h.centre_var
    pointer_var := by simpa only [renEnv_vars] using
      (hfv "xp" (by decide) (by decide) (by decide)).trans h.pointer_var
    tail_var := by simpa only [renEnv_vars] using
      (hfv "tail" (by decide) (by decide) (by decide)).trans h.tail_var
    bits_var := by simpa only [renEnv_vars] using
      (hfv "rsbits" (by decide) (by decide) (by decide)).trans h.bits_var
    centre_arr := by
      simpa only [renEnv_arrs, streamDepthSwap_ord] using hord.trans
        (by simpa only [renEnv_arrs, streamDepthSwap_ord] using h.centre_arr)
    off_arr := by
      simpa [renEnv_arrs, streamDepthSwap] using hoff.trans
        (by simpa [renEnv_arrs, streamDepthSwap] using h.off_arr)
    target_arr := by
      simpa [renEnv_arrs, streamDepthSwap] using htgt.trans
        (by simpa [renEnv_arrs, streamDepthSwap] using h.target_arr)
    mask_arr := by
      simpa only [renEnv_arrs, streamDepthSwap_alv] using hcps.trans
        (by simpa only [renEnv_arrs, streamDepthSwap_alv] using h.mask_arr)
    row_arr := by
      simpa only [renEnv_arrs, streamDepthSwap_xmem] using hxmm.trans
        (by simpa only [renEnv_arrs, streamDepthSwap_xmem] using h.row_arr)
    row_fit := h.row_fit
    asg_arr := by
      simpa only [renEnv_arrs, streamDepthSwap_asg] using hasg.trans
        (by simpa only [renEnv_arrs, streamDepthSwap_asg] using h.asg_arr)
    dist_clean := by
      apply distClean_of_arrs_eq h.dist_clean
      simpa only [renEnv_arrs, streamDepthSwap_dist] using hpds
    queue_arr := by
      obtain ⟨Q, hQ⟩ := h.queue_arr
      refine ⟨Q, ?_⟩
      simpa [renEnv_arrs, streamDepthSwap] using hq.trans
        (by simpa [renEnv_arrs, streamDepthSwap] using hQ)
    qdist_arr := by
      obtain ⟨QD, hQD⟩ := h.qdist_arr
      refine ⟨QD, ?_⟩
      simpa [renEnv_arrs, streamDepthSwap] using hqd.trans
        (by simpa [renEnv_arrs, streamDepthSwap] using hQD)
    mask_bound := h.mask_bound }

/-- Releasing the row owned by `j` does not touch the reusable buffers of
any strictly deeper level. -/
theorem StreamScratchFrom.run_streamReleaseCom
    {B n cap mb ell j K : ℕ} {σ σ' : Env}
    (h : StreamScratchFrom B n cap mb ell (j + 1) σ)
    (hr : Run B (streamReleaseCom cap mb j) σ σ' K) :
    StreamScratchFrom B n cap mb ell (j + 1) σ' := by
  apply h.run hr
  · intro d _ _
    exact notMem_warrs_streamReleaseCom
      (by simp [cpsName, cluName, String.ext_iff])
      (by simp [cpsName, resName, String.ext_iff])
      (by simp [cpsName, batName, String.ext_iff])
      (by simp [cpsName, alvName, String.ext_iff])
      (by simp [cpsName, gamName, String.ext_iff])
      (fun s _ => by simp [cpsName, colName, String.ext_iff])
  · intro d hd _
    exact notMem_warrs_streamReleaseCom
      (fun he => by
        have := Lax3Proofs.RamDriverWrites.cluName_inj he
        omega)
      (by simp [cluName, resName, String.ext_iff])
      (by simp [cluName, batName, String.ext_iff])
      (by simp [cluName, alvName, String.ext_iff])
      (by simp [cluName, gamName, String.ext_iff])
      (fun s _ => by simp [cluName, colName, String.ext_iff])
  · intro d hd _
    exact notMem_warrs_streamReleaseCom
      (by simp [resName, cluName, String.ext_iff])
      (fun he => by
        have := Lax3Proofs.RamDriverWrites.resName_inj he
        omega)
      (by simp [resName, batName, String.ext_iff])
      (by simp [resName, alvName, String.ext_iff])
      (by simp [resName, gamName, String.ext_iff])
      (fun s _ => by simp [resName, colName, String.ext_iff])
  · intro d hd _
    exact notMem_warrs_streamReleaseCom
      (by simp [batName, cluName, String.ext_iff])
      (by simp [batName, resName, String.ext_iff])
      (fun he => by
        have := Lax3Proofs.RamDriverWrites.batName_inj he
        omega)
      (by simp [batName, alvName, String.ext_iff])
      (by simp [batName, gamName, String.ext_iff])
      (fun s _ => by simp [batName, colName, String.ext_iff])
  · intro d hd _
    exact notMem_warrs_streamReleaseCom
      (by simp [alvName, cluName, String.ext_iff])
      (by simp [alvName, resName, String.ext_iff])
      (by simp [alvName, batName, String.ext_iff])
      (fun he => by
        have := Lax3Proofs.RamDriverWrites.alvName_inj he
        omega)
      (by simp [alvName, gamName, String.ext_iff])
      (fun s _ => by simp [alvName, colName, String.ext_iff])
  · intro d hd _
    exact notMem_warrs_streamReleaseCom
      (by simp [gamName, cluName, String.ext_iff])
      (by simp [gamName, resName, String.ext_iff])
      (by simp [gamName, batName, String.ext_iff])
      (by simp [gamName, alvName, String.ext_iff])
      (fun he => by
        have := Lax3Proofs.RamDriverWrites.gamName_inj he
        omega)
      (fun s _ => by simp [gamName, colName, String.ext_iff])
  · intro d hd _ s _
    exact notMem_warrs_streamReleaseCom
      (by simp [colName, cluName, String.ext_iff])
      (by simp [colName, resName, String.ext_iff])
      (by simp [colName, batName, String.ext_iff])
      (by simp [colName, alvName, String.ext_iff])
      (by simp [colName, gamName, String.ext_iff])
      (fun t _ he => by
        have := (Lax3Proofs.RamDriverWrites.colName_inj he).1
        omega)

theorem belowArr_notMem_warrs_streamReleaseCom
    (cap mb j : ℕ) {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamReleaseCom cap mb j).warrs :=
  notMem_warrs_streamReleaseCom
    (Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto))
    (Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto))
    (Lax3Proofs.RamDriverWrites.belowArr_ne h (le_refl j) (by tauto))
    (Lax3Proofs.RamDriverWrites.belowArr_ne h (Nat.le_succ j) (by tauto))
    (Lax3Proofs.RamDriverWrites.belowArr_ne h (Nat.le_succ j) (by tauto))
    (fun s _ =>
      Lax3Proofs.RamDriverWrites.belowArr_ne h (Nat.le_succ j) (by tauto))

theorem belowVar_notMem_wvars_streamReleaseCom
    (cap mb j : ℕ) {y : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamReleaseCom cap mb j).wvars := by
  apply notMem_wvars_streamReleaseCom
  all_goals
    intro he
    first
    | exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "p")
        (he ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h)
    | exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "pend")
        (he ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h)
    | exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "cw")
        (he ▸ Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h)

/-! ## Advancing the progressive centre prefix -/

/-- The sole counter update between two streamed centres. -/
def streamAdvanceCom : Com :=
  .assign "c" (.add (.var "c") (.lit 1))

/-- A consumed sorted row already contains the semantic prefix at `c+1`;
updating the machine counter exposes it as the next turn state. -/
theorem streamAdvanceStep
    {B ns nt na q cap c tail bits j : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M : ℕ → ℕ}
    (hqB : q < B) (hcq : c < q) :
    Spec B
      (fun σ => StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
        Xmem asg M (renEnv (streamDepthSwap j) σ))
      streamAdvanceCom
      (fun _ σ' => StreamTurnState B ns nt na q cap (c + 1) G A₀ π centre O T
        Xmem asg M (renEnv (streamDepthSwap j) σ'))
      4 := by
  refine Spec.of_exists fun σ hsorted => ?_
  have hc : σ.vars "c" = c := by
    simpa only [renEnv_vars] using hsorted.centre_var
  have hcB : c < B := lt_trans hcq hqB
  have hnextB : c + 1 < B := by omega
  have he : (Expr.add (.var "c") (.lit 1)).evalB B σ = some (c + 1) := by
    have hv : (Expr.var "c").evalB B σ = some c := by
      rw [evalB_var (by rw [hc]; exact hcB), hc]
    have h1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by omega)
    exact evalB_bin (op := Bop.add) hv h1 (by simpa [Bop.apply_add] using hnextB)
  let σ' := σ.setVar "c" (c + 1)
  have hr : Run B streamAdvanceCom σ σ' 4 := by
    simpa [streamAdvanceCom, σ', Expr.size] using Run.assign he
  have hturn : StreamTurnState B ns nt na q cap (c + 1) G A₀ π centre O T
      Xmem asg M (renEnv (streamDepthSwap j) σ') := by
    refine {
      state := hsorted.row.state
      n_var := by simpa [σ', renEnv_vars, String.ext_iff] using hsorted.n_var
      q_var := by simpa [σ', renEnv_vars, String.ext_iff] using hsorted.q_var
      centre_var := by simp [σ', renEnv_vars]
      centre_arr := by simpa [σ', renEnv_arrs] using hsorted.centre_arr
      off_arr := by simpa [σ', renEnv_arrs] using hsorted.off_arr
      target_arr := by simpa [σ', renEnv_arrs] using hsorted.target_arr
      mask_arr := by simpa [σ', renEnv_arrs] using hsorted.mask_arr
      row_arr := by simpa [σ', renEnv_arrs] using hsorted.row_arr
      row_fit := hsorted.row_fit
      asg_arr := by simpa [σ', renEnv_arrs] using hsorted.asg_arr
      dist_clean := by
        apply distClean_of_arrs_eq hsorted.dist_clean
        simp [σ', renEnv_arrs]
      queue_arr := by
        obtain ⟨Q, hQ⟩ := hsorted.queue_arr
        exact ⟨Q, by simpa [σ', renEnv_arrs] using hQ⟩
      qdist_arr := by
        obtain ⟨QD, hQD⟩ := hsorted.qdist_arr
        exact ⟨QD, by simpa [σ', renEnv_arrs] using hQD⟩
      mask_bound := hsorted.mask_bound }
  exact ⟨σ', 4, hr, le_rfl, hturn⟩

/-! ## One reusable centre lifecycle -/

/-- Consume one already-sorted row, release all row-local scratch, and expose
the next progressive-cover prefix. -/
noncomputable def streamCentreLifecycleCom
    (q_top cap mb j : ℕ) (φ : Lax3.FirstOrder.FO 0) (inner : Com) : Com :=
  .seq (streamCentreCom q_top cap mb j φ inner)
    (.seq (streamReleaseCom cap mb j) streamAdvanceCom)

noncomputable def streamCentreLifecycleCost
    (q_top cap mb j tail rowMass ballWeight Kinner Kscatter : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  streamCentreCost q_top cap mb j tail rowMass ballWeight Kinner Kscatter φ +
    (streamReleaseCost tail (sigL cap mb (j + 1)) + 4)

theorem belowArr_notMem_warrs_streamCentreLifecycleCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {inner : Com}
    {a : String}
    (hinner : ∀ a, Lax3Proofs.RamDriverWrites.BelowArr (j + 1) a →
      a ∉ inner.warrs)
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamCentreLifecycleCom q_top cap mb j phi inner).warrs := by
  intro hm
  rw [streamCentreLifecycleCom] at hm
  rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hm with hm | hm
  · exact (belowArr_notMem_warrs_streamCentreCom
      q_top cap mb j phi hinner h) hm
  rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hm with hm | hm
  · exact (belowArr_notMem_warrs_streamReleaseCom cap mb j h) hm
  · simpa [streamAdvanceCom, Com.warrs] using hm

theorem belowVar_notMem_wvars_streamCentreLifecycleCom
    (q_top cap mb j : ℕ) (phi : Lax3.FirstOrder.FO 0) {inner : Com}
    {y : String}
    (hinner : ∀ y, Lax3Proofs.RamDriverWrites.BelowVar (j + 1) y →
      y ∉ inner.wvars)
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamCentreLifecycleCom q_top cap mb j phi inner).wvars := by
  intro hm
  rw [streamCentreLifecycleCom] at hm
  rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hm with hm | hm
  · exact (belowVar_notMem_wvars_streamCentreCom
      q_top cap mb j phi hinner h) hm
  rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hm with hm | hm
  · exact (belowVar_notMem_wvars_streamReleaseCom cap mb j h) hm
  · have hd := Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h
    have hne : y ≠ "c" := fun hq =>
      (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "c") (hq ▸ hd)
    exact hne (by simpa [streamAdvanceCom, Com.wvars] using hm)

/-- Both occupied-row measures in a centre lifecycle may be rounded up to
the centre's single CSR weight.  This is the arithmetic adapter used by the
recursive sigma recurrence. -/
theorem streamCentreLifecycleCost_le_diagonal
    {tail rowMass w Kinner : ℕ}
    (q_top cap mb j Kscatter : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (htail : tail ≤ w) (hrows : rowMass ≤ w) :
    streamCentreLifecycleCost q_top cap mb j tail rowMass w Kinner Kscatter φ ≤
      streamCentreLifecycleCost q_top cap mb j w w w Kinner Kscatter φ := by
  simp only [streamCentreLifecycleCost, streamCentreCost,
    CoverActiveStreamPrepare.streamPrepareCost,
    CoverActiveStreamPlay.streamPlayCost,
    CoverActiveStreamLoad.streamClusterLoadCost,
    CoverActiveStreamMask.streamBlockAndCost,
    Lax3Proofs.RamDriverDescend.cacheRoundCost,
    CoverActiveStreamBatch.streamBatchCachedCost,
    CoverActiveStreamChild.streamChildFilterCost,
    Lax3Proofs.Refine.ScatterDeadPass.memFillAtCost,
    CoverActiveStreamBatch.streamChildGameCost,
    CoverActiveStreamColour.streamEnumColourCost,
    CoverActiveStreamEnum.enumStreamCost,
    CoverActiveStreamColour.streamColourCost,
    CoverActiveStreamColour.streamOldCost,
    CoverActiveStreamColour.streamPdCost,
    CoverActiveStreamColour.streamPdBodyCost,
    CoverActiveStreamColour.streamPuCost,
    CoverActiveStreamColour.streamPuBodyCost,
    CoverActiveStreamColour.streamExpandCost,
    streamCentreFinishCost, Lax3Proofs.RamDriverBase.rbCost,
    streamReleaseCost, CoverActiveStreamMask.streamBlockClearCost,
    CoverActiveStreamColour.streamPaletteClearCost]
  gcongr

/-- The stable boundary between two streamed centres.  Besides the next turn
state it records the parent resources needed to execute that turn, the sparse
scratch reset needed by its consumer, and the exact table delta of the centre
just consumed. -/
structure StreamCentreLifecycleOut
    (B n q_top cap mb ns nt q j c bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (σ₀ σ : Env) : Prop where
  turn : StreamTurnState B ns nt (n * n) q cap (c + 1) G A₀ π centre O T
    Xmem asg M (renEnv (streamDepthSwap j) σ)
  bits_var : (renEnv (streamDepthSwap j) σ).vars "rsbits" = bits
  level : LevelPre B n cap mb ns nt O T j A₀ Gm C σ
  play : PlayRec B cap G j A₀ Gm σ
  tables : TablesSized q_top cap mb φ n σ
  base_arrs : BaseArrs B q_top cap mb ell φ σ
  cluster_zero : σ.arrs (cluName j) = arrOf n (fun _ => 0)
  retained_zero : σ.arrs (resName j) = arrOf n (fun _ => 0)
  batch_zero : σ.arrs (batName j) = arrOf n (fun _ => 0)
  child_zero : σ.arrs (alvName (j + 1)) = arrOf n (fun _ => 0)
  game_zero : σ.arrs (gamName (j + 1)) = arrOf n (fun _ => 0)
  colours_zero : ∀ s, s < sigL cap mb (j + 1) →
    σ.arrs (colName (j + 1) s) = arrOf n (fun _ => 0)
  scratch : StreamScratchFrom B n cap mb ell (j + 1) σ
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
/-- **The iterable centre boundary.**  A complete centre lifecycle advances
the semantic and machine counters together, resets all successor scratch,
and changes precisely the table cells assigned to the consumed centre. -/
theorem streamCentreLifecycleStep
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
          centre O T Xmem asg M Gm C (renEnv (streamDepthSwap j) σ) ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ ∧
        TablesSized q_top cap mb φ n σ ∧
        BaseArrs B q_top cap mb ell φ σ ∧
        StreamScratchFrom B n cap mb ell (j + 1) σ)
      (streamCentreLifecycleCom q_top cap mb j φ inner)
      (StreamCentreLifecycleOut B n q_top cap mb ns nt q j c bits ell φ G A₀ π
        centre O T Xmem asg M Gm C)
      (streamCentreLifecycleCost q_top cap mb j tail
        (expandRowSum O Xmem 0 tail)
        (Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
          n G A₀ π centre O cap c) Kinner Kscatter φ) := by
  intro σ hpre
  obtain ⟨hprepare₀, hlevel₀, htables₀, hbase₀, hscratch₀⟩ := hpre
  have hcq : c < q := hprepare₀.sorted.row.state.pos_le
  have hqB : q < B := lt_of_le_of_lt hcentres.count_le hB.n_lt
  obtain ⟨σ₁, hr₁, hcentre₁⟩ :=
    (streamCentreStep hchild hframes hcap hcsr hnt hB hcentres hmb hjl hbitsB
      hpow hbitsEq hbnd hcost hK).run
      ⟨hprepare₀, hlevel₀, htables₀, hbase₀, hscratch₀⟩
  obtain ⟨hlevel₁, hparent₁, htables₁, hout₁, -, -, -, hsorted₁,
    hrelease₁, hscratch₁, htable₁⟩ := hcentre₁
  obtain ⟨σ₂, hr₂, hrelease₂⟩ :=
    (streamReleaseStep hB.one_lt hB.n_lt).run ⟨hrelease₁, hlevel₁⟩
  have hscratch₂ : StreamScratchFrom B n cap mb ell (j + 1) σ₂ :=
    StreamScratchFrom.run_streamReleaseCom hscratch₁ hr₂
  have hparent₂ : PlayRec B cap G j A₀ Gm σ₂ :=
    hparent₁.congr
      (fun a ha => hr₂.frame_var _
        (belowVar_notMem_wvars_streamReleaseCom cap mb j
          ⟨a, ha, Or.inl rfl⟩))
      (fun a ha => hr₂.frame_arr _
        (belowArr_notMem_warrs_streamReleaseCom cap mb j
          ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))
      (fun a ha => hr₂.frame_arr _
        (belowArr_notMem_warrs_streamReleaseCom cap mb j
          ⟨a, ha, Or.inr (Or.inl rfl)⟩))
      (fun a ha => hr₂.frame_arr _
        (belowArr_notMem_warrs_streamReleaseCom cap mb j
          ⟨a, ha, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))
  have hsorted₂ :=
    Lax3Proofs.Refine.CoverActiveStreamLifecycle.StreamSortedOut.run_streamReleaseCom
      hsorted₁ hr₂
  obtain ⟨σ₃, hr₃, hturn₃⟩ :=
    (streamAdvanceStep hqB hcq).run hsorted₂
  have hparent₃ : PlayRec B cap G j A₀ Gm σ₃ :=
    hparent₂.congr
      (fun a _ => hr₃.frame_var _ (by
        simp [streamAdvanceCom, Com.wvars, ctrName, String.ext_iff]))
      (fun a _ => hr₃.frame_arr _ (by simp [streamAdvanceCom, Com.warrs]))
      (fun a _ => hr₃.frame_arr _ (by simp [streamAdvanceCom, Com.warrs]))
      (fun a _ => hr₃.frame_arr _ (by simp [streamAdvanceCom, Com.warrs]))
  have hlevel₃ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₃ := by
    apply Lax3Proofs.RamDriverCompose.levelPre_run hrelease₂.level hr₃ <;>
      simp [streamAdvanceCom, Com.wvars, Com.warrs, mnumName, String.ext_iff]
  have harr₃ (a : String) : σ₃.arrs a = σ₂.arrs a :=
    hr₃.frame_arr a (by simp [streamAdvanceCom, Com.warrs])
  have hscratch₃ : StreamScratchFrom B n cap mb ell (j + 1) σ₃ :=
    hscratch₂.congr harr₃
  have hout₃ : σ₃.out = σ.out :=
    (hr₃.out_eq (by simp [streamAdvanceCom, Com.NoWrite])).trans
      (hrelease₂.out_eq.trans hout₁)
  refine ⟨σ₃, ?_, {
    turn := hturn₃
    bits_var := by
      rw [renEnv_vars, hr₃.frame_var "rsbits" (by
        simp [streamAdvanceCom, Com.wvars])]
      exact hsorted₂.bits_var
    level := hlevel₃
    play := hparent₃
    tables := (htables₁.run hr₂).run hr₃
    base_arrs := ((hbase₀.run hr₁).run hr₂).run hr₃
    cluster_zero := (harr₃ _).trans hrelease₂.cluster_zero
    retained_zero := (harr₃ _).trans hrelease₂.retained_zero
    batch_zero := (harr₃ _).trans hrelease₂.batch_zero
    child_zero := (harr₃ _).trans hrelease₂.child_zero
    game_zero := (harr₃ _).trans hrelease₂.game_zero
    colours_zero := fun s hs => (harr₃ _).trans (hrelease₂.colours_zero s hs)
    scratch := hscratch₃
    out_eq := hout₃
    table_step := ?_ }⟩
  · simpa [streamCentreLifecycleCom] using hr₁.seq (hr₂.seq hr₃)
  · intro i hi
    obtain ⟨Tb, Tb₀, hTb, hTb₀, hkeep, hsem⟩ := htable₁ i hi
    have htab₂ : σ₂.arrs (tabName j i) = σ₁.arrs (tabName j i) :=
      hr₂.frame_arr _ (notMem_warrs_streamReleaseCom
        (by simp [tabName, cluName, String.ext_iff])
        (by simp [tabName, resName, String.ext_iff])
        (by simp [tabName, batName, String.ext_iff])
        (by simp [tabName, alvName, String.ext_iff])
        (by simp [tabName, gamName, String.ext_iff])
        (fun s _ => Lax3Proofs.RamDriverFrames.tabName_ne_colName j i (j + 1) s))
    refine ⟨Tb, Tb₀, ?_, hTb₀, hkeep, hsem⟩
    exact (harr₃ _).trans (htab₂.trans hTb)

/-! ## Producing the next sorted row -/

/-- Search the current progressive mask and immediately sort its reusable
row.  This command still lives at the logical scratch names; the depth-owned
adapter below transports it wholesale. -/
def streamSearchSortCom (r : ℕ) : Com :=
  .seq (activeStreamTurnCom r) activeStreamSortCom

def streamSearchSortCost (bits bw nb : ℕ) : ℕ :=
  activeStreamTurnK bw nb + activeStreamSortK bits nb

theorem activeStreamSortK_mono {bits a b : ℕ} (hab : a ≤ b) :
    activeStreamSortK bits a ≤ activeStreamSortK bits b := by
  simp only [activeStreamSortK, Lax3Proofs.Refine.CoverActiveRadixPass.radixBlockCost,
    Lax3Proofs.Refine.CoverActiveRadixPass.radixPassCost,
    Lax3Proofs.Refine.CoverActiveRadixPass.stableScatterCost,
    Lax3Proofs.Refine.CoverActiveRadixPass.selectDigitCost]
  gcongr

open Classical in
/-- One logical turn followed by its in-place radix sort.  The fixed cost
uses the advertised vertex budget `nb`; the actual emitted prefix may be
smaller. -/
theorem streamSearchSortStep
    {B n ns nt na q r c bits bw nb : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M : ℕ → ℕ} {A : Finset ℕ}
    (hcentres : Lax3Proofs.RamCoverActive.CentresBy n q A₀ π centre)
    (hcsr : Lax3Proofs.RamBfs.CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hbitsB : bits < B) (hpow : n ≤ 2 ^ bits)
    (hA : ∀ v, v < n → M v ≠ 0 →
      Lax3Proofs.RamBfs.WD G M (2 * r) (centre c) v → v ∈ A)
    (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw)
    (hnb : A.card ≤ nb) :
    Spec B
      (fun σ =>
        StreamTurnState B ns nt na q r c G A₀ π centre O T Xmem asg M σ ∧
        c < q ∧ σ.vars "rsbits" = bits)
      (streamSearchSortCom r)
      (fun _ σ' => ∃ tail Xmem' asg' M', tail ≤ nb ∧
        StreamSortedOut B ns nt na q r c tail bits G A₀ π centre O T
          Xmem' asg' M' σ')
      (streamSearchSortCost bits bw nb) := by
  refine Spec.of_exists fun σ hpre => ?_
  obtain ⟨σ₁, hr₁, tail, Q, QD, Xmem₁, htail, hturn₁⟩ :=
    (activeStreamTurn_spec hcentres hcsr hnB hnsB hnt hqB hrB hA hbw hnb).run
      ⟨hpre.1, hpre.2.1⟩
  have hbits₁ : σ₁.vars "rsbits" = bits := by
    rw [hr₁.frame_var "rsbits" (by
      simp [activeStreamTurnCom, Lax3Proofs.Refine.BfsBlock.bfsBlockCom,
        Lax3Proofs.Refine.BfsBlock.unwind,
        Lax3Proofs.Refine.BfsBlock.unwindSlot,
        Lax3Proofs.RamBfs.seedSrc, Lax3Proofs.RamBfs.bfsDrain,
        Lax3Proofs.RamBfs.expandRow, Lax3Proofs.RamBfs.scanSlot,
        Fill.put, Csr.loadRow, Csr.scan, Queue.drain,
        Lax3Proofs.Refine.CoverActiveBlock.emitQueueCom,
        Lax3Proofs.Refine.CoverActiveBlock.emitQueueSlot, Com.wvars])]
    exact hpre.2.2
  obtain ⟨σ₂, hr₂, Xmem₂, hsorted₂⟩ :=
    (activeStreamSort_spec (B := B) (n := n) (bits := bits)
      (by omega) hnB hbitsB hpow).run ⟨hturn₁, hbits₁⟩
  refine ⟨σ₂, _, hr₁.seq hr₂, ?_, tail, Xmem₂,
    Lax3Proofs.Refine.CoverActiveBlock.queueCell asg q c r tail Q QD,
    Lax13Proofs.Reasoning.Lib.upd M (centre c) 0, htail, hsorted₂⟩
  exact Nat.add_le_add_left (activeStreamSortK_mono htail) _

/-- The same search/sort pair running on the five arrays owned by depth `j`. -/
def streamSearchSortAtDepthCom (j r : ℕ) : Com :=
  streamAtDepthCom j (streamSearchSortCom r)

open Classical in
theorem streamSearchSortAtDepthStep
    {B n ns nt na q r c bits bw nb j : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M : ℕ → ℕ} {A : Finset ℕ}
    (hcentres : Lax3Proofs.RamCoverActive.CentresBy n q A₀ π centre)
    (hcsr : Lax3Proofs.RamBfs.CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hbitsB : bits < B) (hpow : n ≤ 2 ^ bits)
    (hA : ∀ v, v < n → M v ≠ 0 →
      Lax3Proofs.RamBfs.WD G M (2 * r) (centre c) v → v ∈ A)
    (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw)
    (hnb : A.card ≤ nb) :
    Spec B
      (fun σ =>
        StreamTurnState B ns nt na q r c G A₀ π centre O T Xmem asg M
          (renEnv (streamDepthSwap j) σ) ∧
        c < q ∧ (renEnv (streamDepthSwap j) σ).vars "rsbits" = bits)
      (streamSearchSortAtDepthCom j r)
      (fun _ σ' => ∃ tail Xmem' asg' M', tail ≤ nb ∧
        StreamSortedOut B ns nt na q r c tail bits G A₀ π centre O T
          Xmem' asg' M' (renEnv (streamDepthSwap j) σ'))
      (streamSearchSortCost bits bw nb) := by
  simpa only [streamSearchSortAtDepthCom, streamAtDepthCom] using
    (Lax3Proofs.Refine.ScatterBlock.renCom_spec (streamDepthSwap_invol j)
      (streamSearchSortStep hcentres hcsr hnB hnsB hnt hqB hrB hbitsB hpow
        hA hbw hnb))

end Lax3Proofs.Refine.CoverActiveStreamLifecycle
