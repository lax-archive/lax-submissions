import Lax3Proofs.Refine.CoverActiveStreamInner
import Lax3Proofs.Refine.ScatterDeadTurn

/-!
# Dead-aware scatter on a streamed active-cover row

The nested active driver returns the child tables on exactly
`alive ∪ killSet`.  This file turns that postcondition, together with the
depth-owned parent frame, into `ScatterDeadTurn.DeadView`.  The existing
dead-aware atom engine can therefore be reused without rebuilding a
carrier-wide cover or an offset table.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamScatter

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (CsrGraph masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.Refine.CoverActiveStreamKill
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.CoverActiveStreamInner
open Lax3Proofs.Refine.ScatterBlock (renEnv_arrs renEnv_vars BallBudget)
open Lax3Proofs.Refine.ScatterDeadTurn
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {n : ℕ}

/-! ## The child postcondition as a scatter view -/

/-- All arrays used by `ClusterData` are fixed by the physical storage
permutation. -/
theorem StreamKillOutAtDepth.clusterDataPhysical
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ) :
    ClusterData n mb j B G A₀ (markSet n Xa) (markSet n Wa) w Alv Gam σ := by
  simpa only [ClusterData, BatchData, renEnv_arrs, renEnv_vars,
    streamDepthSwap_cluName, streamDepthSwap_batName, streamDepthSwap_resName,
    streamDepthSwap_alvName, streamDepthSwap_gamName, streamDepthSwap_memName] using h.data

/-- The parent's kill list is likewise outside the five exchanges. -/
theorem StreamKillOutAtDepth.killListPhysical
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ) :
    KillListAt mb j A₀ (markSet n Xa) (markSet n Wa) σ := by
  simpa only [KillListAt, renEnv_arrs, renEnv_vars, streamDepthSwap_klName] using h.kill_list

/-- Reassemble `ClusterData` after recursion.  The three parent masks use the
general below-depth frame; the child masks and member list come from the
child's returned `LevelPre`. -/
theorem clusterData_after_inner
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ₀ σ : Env}
    (hsrc : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ₀)
    (hpost : LevelPostD B q_top cap mb φ G ns nt O T (j + 1) Alv Gam C'
      (killSet A₀ (markSet n Xa) (markSet n Wa)) σ₀ σ)
    (hfr : StreamParentFrame j q c tail bits σ₀ σ) :
    ClusterData n mb j B G A₀ (markSet n Xa) (markSet n Wa) w Alv Gam σ := by
  obtain ⟨⟨⟨Xa₀, hXa, hXaS, hXaB⟩, ⟨Wa₀, hWa, hWaS, hWaB⟩,
      ⟨Ra₀, hRa, hRaS, hRaB⟩, -, hAlvB, hmask, hmaskpt, -, hGamB,
      Mem₀, mm₀, -, -, hmemE₀, hmemB₀⟩, hwrange⟩ :=
    StreamKillOutAtDepth.clusterDataPhysical hsrc
  obtain ⟨-, -, -, hAlv, hGam, -, -, -, -, -, -, -, -, -, -,
      Mem, mm, hMem, hmm, hmemE, hmemB⟩ := hpost.1
  refine ⟨⟨⟨Xa₀, ?_, hXaS, hXaB⟩, ⟨Wa₀, ?_, hWaS, hWaB⟩,
    ⟨Ra₀, ?_, hRaS, hRaB⟩, hAlv, hAlvB, hmask, hmaskpt,
    hGam, hGamB, Mem, mm, hMem, hmm, hmemE, hmemB⟩, hwrange⟩
  · exact (hfr.depth_arr _ ⟨j, Nat.lt_succ_self j, by tauto⟩).trans hXa
  · exact (hfr.depth_arr _ ⟨j, Nat.lt_succ_self j, by tauto⟩).trans hWa
  · exact (hfr.depth_arr _ ⟨j, Nat.lt_succ_self j, by tauto⟩).trans hRa

/-- The kill list survives recursion through the parent-depth array and
scalar frames. -/
theorem killList_after_inner
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ₀ σ : Env}
    (hsrc : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ₀)
    (hfr : StreamParentFrame j q c tail bits σ₀ σ) :
    KillListAt mb j A₀ (markSet n Xa) (markSet n Wa) σ := by
  obtain ⟨kl, kq, hkl, hkk, hkq, hklt, hinj, hsnd, hcmp⟩ :=
    StreamKillOutAtDepth.killListPhysical hsrc
  exact ⟨kl, kq,
    (hfr.depth_arr _ ⟨j, Nat.lt_succ_self j, by tauto⟩).trans hkl,
    hfr.kill_count_var.trans hkk, hkq, hklt, hinj, hsnd, hcmp⟩

/-- The child postcondition plus the parent frame is exactly the
cover-independent view consumed by one dead-aware scatter atom. -/
theorem deadView_after_inner
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ₀ σ : Env}
    (hsrc : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ₀)
    (hpost : LevelPostD B q_top cap mb φ G ns nt O T (j + 1) Alv Gam C'
      (killSet A₀ (markSet n Xa) (markSet n Wa)) σ₀ σ)
    (hfr : StreamParentFrame j q c tail bits σ₀ σ)
    (hb : BaseArrs B q_top cap mb ell φ σ) :
    DeadView B q_top cap mb ns nt ell j φ G O T A₀ C
      (markSet n Xa) (markSet n Wa) w Alv Gam C' σ := by
  obtain ⟨hn, hoff, htgt, -, -, hcol, -, -, -, hlmem, -, -, hordmem, -, -, -⟩ := hpost.1
  exact
    { n_eq := hn
      off := hoff
      tgt := htgt
      mem := hlmem
      nsW := hordmem.1
      data := clusterData_after_inner hsrc hpost hfr
      col_arr := hcol
      col_bit := hsrc.colour_bit
      col_read := hsrc.colour_read
      table := hpost.2.2
      kill_list := killList_after_inner hsrc hfr
      base_arrs := hb }

/-! ## A cover-free frame for the atom engine -/

/-- `DeadView` is stable under one dead-aware atom.  This is the
cover-independent part of the landed `DeadPre.run_scatDead` proof. -/
theorem deadView_run_scatDead
    {B q_top cap mb ns nt ell j L ti r t K : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {O T A₀ : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv Gam : ℕ → ℕ}
    {C' : ℕ → ℕ → ℕ} {β : DistFO L 1} {σ σ' : Env}
    (h : DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ)
    (hloc : IsLocal β)
    (hr : Run B (scatDeadCom j ti β r t) σ σ' K) :
    DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ' := by
  have hfa (a : String)
      (ha : a ∉ ["mem", "alv", "dist", "exc", "q", "qd"])
      (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" a) : σ'.arrs a = σ.arrs a :=
    hr.frame_arr a (fun hm =>
      (Lax3Proofs.RamDriverWrites.warrs_scatDeadCom j ti β r t hloc hm).elim ha hbb)
  have hfv (y : String)
      (h₁ : y ∉ ["kc", "ke", "of", "oz", "oi", "oc", "mm", "ak", "av", "ac", "ax",
        "os", "flag"])
      (h₂ : y ∉ ["cnt", "mj", "mv", "sj", "src", "tail", "head", "sc", "v",
        "dv", "dn", "j", "jend", "w", "ri", "u", "du", "mw", "flag"])
      (hbb : ¬ Lax3Proofs.RamDriverBot.Ext "bb" y)
      (henv : ∀ e, y ≠ envName e) : σ'.vars y = σ.vars y :=
    hr.frame_var y (notMem_wvars_scatDeadCom_lit hloc h₁ h₂ hbb henv)
  obtain ⟨⟨⟨Xa, hXa, hXaS, hXaB⟩, ⟨Wa, hWa, hWaS, hWaB⟩,
      ⟨Ra, hRa, hRaS, hRaB⟩, hAlv, hAlvB, hmask, hmaskpt,
      hGam, hGamB, Mem, mm, hMem, hmm, hmemE, hmemB⟩, hwrange⟩ := h.data
  obtain ⟨kl, kq, hkl, hkk, hkq, hklt, hinj, hsnd, hcmp⟩ := h.kill_list
  refine
    { n_eq := (hfv "n" (by decide) (by decide)
        (not_ext_bb_short (by decide))
        (fun e => by simp [envName, String.ext_iff])).trans h.n_eq
      off := (hfa "off" (by decide) (not_ext_bb_of_cons rfl (by decide))).trans h.off
      tgt := (hfa "tgt" (by decide) (not_ext_bb_of_cons rfl (by decide))).trans h.tgt
      mem := levelMem_run hr h.mem
      nsW := h.nsW
      data := ⟨⟨⟨Xa, (hfa _ (by simp [cluName, String.ext_iff])
          (Lax3Proofs.RamDriverFrames.not_bbExt_cluName j)).trans hXa, hXaS, hXaB⟩,
        ⟨Wa, (hfa _ (by simp [batName, String.ext_iff])
          (Lax3Proofs.RamDriverFrames.not_bbExt_batName j)).trans hWa, hWaS, hWaB⟩,
        ⟨Ra, (hfa _ (by simp [resName, String.ext_iff])
          (Lax3Proofs.RamDriverFrames.not_bbExt_resName j)).trans hRa, hRaS, hRaB⟩,
        (hfa _ (by simp [alvName, String.ext_iff])
          (Lax3Proofs.RamDriverFrames.not_bbExt_alvName (j + 1))).trans hAlv,
        hAlvB, hmask, hmaskpt,
        (hfa _ (by simp [gamName, String.ext_iff])
          (Lax3Proofs.RamDriverFrames.not_bbExt_gamName (j + 1))).trans hGam,
        hGamB, Mem, mm,
        (hfa _ (by simp [memName, String.ext_iff])
          (Lax3Proofs.RamDriverFrames.not_bbExt_memName (j + 1))).trans hMem,
        (hfv _ (by simp [mnumName, String.ext_iff])
          (by simp [mnumName, String.ext_iff]) (not_ext_bb_mnumName (j + 1))
          (fun e => by simp [mnumName, envName, String.ext_iff])).trans hmm,
        hmemE, hmemB⟩, hwrange⟩
      col_arr := fun s hs =>
        (hfa _ (by simp [colName, String.ext_iff])
          (Lax3Proofs.RamDriverFrames.not_bbExt_colName (j + 1) s)).trans (h.col_arr s hs)
      col_bit := h.col_bit
      col_read := h.col_read
      table := by
        intro i hi
        obtain ⟨Tb, hTb, hbit, hval⟩ := h.table i hi
        exact ⟨Tb, (hfa _ (by simp [tabName, String.ext_iff])
          (Lax3Proofs.RamDriverFrames.not_bbExt_tabName (j + 1) i)).trans hTb,
          hbit, hval⟩
      kill_list := ⟨kl, kq,
        (hfa _ (by simp [klName, String.ext_iff]) (not_ext_bb_klName j)).trans hkl,
        (hfv _ (by simp [kkName, String.ext_iff])
          (by simp [kkName, String.ext_iff]) (not_ext_bb_kkName j)
          (fun e => by simp [kkName, envName, String.ext_iff])).trans hkk,
        hkq, hklt, hinj, hsnd, hcmp⟩
      base_arrs := h.base_arrs.run hr }

/-- Changing an unrelated scalar preserves a dead scatter view. -/
theorem DeadView.setVar
    {B q_top cap mb ns nt ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T A₀ : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv Gam : ℕ → ℕ}
    {C' : ℕ → ℕ → ℕ} {σ : Env}
    (h : DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ)
    (x : String) (hxn : x ≠ "n") (hxmm : x ≠ mnumName (j + 1))
    (hxkk : x ≠ kkName j) (v : ℕ) :
    DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C'
      (σ.setVar x v) := by
  obtain ⟨⟨hXa, hWa, hRa, hAlv, hAlvB, hmask, hmaskpt, hGam, hGamB,
      Mem, mm, hMem, hmm, hmemE, hmemB⟩, hwrange⟩ := h.data
  obtain ⟨kl, kq, hkl, hkk, hkq, hklt, hinj, hsnd, hcmp⟩ := h.kill_list
  exact
    { n_eq := by rw [vars_setVar, if_neg (Ne.symm hxn)]; exact h.n_eq
      off := by simpa using h.off
      tgt := by simpa using h.tgt
      mem := by simpa only [LevelMem, Sized, arrs_setVar] using h.mem
      nsW := h.nsW
      data := ⟨⟨by simpa using hXa, by simpa using hWa, by simpa using hRa,
        by simpa using hAlv, hAlvB, hmask, hmaskpt, by simpa using hGam, hGamB,
        Mem, mm, by simpa using hMem,
        by rw [vars_setVar, if_neg (Ne.symm hxmm)]; exact hmm,
        hmemE, hmemB⟩, hwrange⟩
      col_arr := fun s hs => by simpa using h.col_arr s hs
      col_bit := h.col_bit
      col_read := h.col_read
      table := by simpa only [TableInvOn, arrs_setVar] using h.table
      kill_list := ⟨kl, kq, by simpa using hkl,
        by rw [vars_setVar, if_neg (Ne.symm hxkk)]; exact hkk,
        hkq, hklt, hinj, hsnd, hcmp⟩
      base_arrs := baseArrs_setVar_c h.base_arrs x v }

/-! ## The cover-independent flag folds -/

open Classical in
/-- One streamed atom: run the landed dead-aware engine from its minimal
`DeadView`, then copy its verdict into the indexed flag cell. -/
theorem atomView_spec {bw nb : ℕ}
    {B q_top cap mb ns nt ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T A₀ : ℕ → ℕ} {C C' : ℕ → ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv Gam : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → A₀ (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, BallBudget n r G Alv O bw nb)
    (i k : ℕ) {σs : ScatterSentence (sigL cap mb (j + 1))}
    (hβ : σs.β ∈ tablesAt q_top cap mb φ (j + 1)) (hloc : IsLocal σs.β)
    (hrB : σs.r + 1 < B) (htB : σs.t + n + mb < B)
    {Kb : ℕ} (hKb : deadAtomKX σs.β n X.ncard mb bw nb σs.t ≤ Kb) :
    Spec B (DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C')
      (.seq (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1))) σs.β σs.r σs.t)
        (.assign (flgName j i k) (.var "flag")))
      (fun σ σ' => DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ' ∧
        σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
        (∀ i' k', ¬(i' = i ∧ k' = k) →
          σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
        σ'.vars (flgName j i k) ≤ 1 ∧
        (σ'.vars (flgName j i k) ≠ 0 ↔ ScatVal (stepArenaP (masked G A₀) X w)
          (stepColoringP cap (masked G A₀) (colRead n C (sigL cap mb j)) X w) σs))
      Kb := by
  classical
  have hcur : curName j ≠ flgName j i k := fun h =>
    RamDriverFrames.underscore_notMem_prefixed (p := "cu") (by decide) j
      (h ▸ (RamDriverFrames.underscore_mem_flgName j i k :
        '_' ∈ (flgName j i k).toList) : '_' ∈ (curName j).toList)
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨τ, hrτ, hview, hout, hcurτ, hflgfr, hfl1, hfliff⟩ :=
    (scatDead_specCore hcsr hB hXalive hbud hβ hloc hrB htB (le_refl _)
      (fun h => h) (fun h hr => deadView_run_scatDead h hloc hr)).run hσ
  have hflagB : τ.vars "flag" < B := lt_of_le_of_lt hfl1 hB.one_lt
  have r₂ : Run B (.assign (flgName j i k) (.var "flag")) τ
      (τ.setVar (flgName j i k) (τ.vars "flag")) (1 + (Expr.var "flag").size) :=
    Run.assign (evalB_var hflagB)
  have hset : DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C'
      (τ.setVar (flgName j i k) (τ.vars "flag")) :=
    Lax3Proofs.Refine.CoverActiveStreamScatter.DeadView.setVar hview _
      (by simp [flgName, String.ext_iff])
      (by simp [flgName, mnumName, String.ext_iff])
      (by simp [flgName, kkName, String.ext_iff]) _
  refine ⟨_, _, hrτ.seq r₂, ?_, hset, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hKb
    rw [deadAtomKX]
    simp only [Expr.size]
    omega
  · rw [out_setVar]; exact hout
  · rw [vars_setVar, if_neg hcur]; exact hcurτ
  · intro i' k' hik
    rw [vars_setVar, if_neg (fun hc => hik (by
      obtain ⟨-, hi, hk⟩ := RamDriverFrames.flgName_inj hc
      exact ⟨hi, hk⟩))]
    exact hflgfr i' k'
  · rw [vars_setVar, if_pos rfl]; exact hfl1
  · rw [vars_setVar, if_pos rfl]; exact hfliff

open Classical in
/-- Fold the cover-independent atom contract over one tabled formula. -/
theorem atomsView_spec {bw nb : ℕ}
    {B q_top cap mb ns nt ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T A₀ : ℕ → ℕ} {C C' : ℕ → ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv Gam : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → A₀ (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, BallBudget n r G Alv O bw nb)
    (i : ℕ) {Kb : ℕ} :
    ∀ (l : List (ScatterSentence (sigL cap mb (j + 1)))) (k₀ : ℕ),
      (∀ σs ∈ l, σs.β ∈ tablesAt q_top cap mb φ (j + 1) ∧ σs.r + 1 < B ∧
        σs.t + n + mb < B ∧ deadAtomKX σs.β n X.ncard mb bw nb σs.t ≤ Kb) →
      Spec B (DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C')
        (foldIdx (fun k σs =>
            Com.seq (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1)))
              σs.β σs.r σs.t) (.assign (flgName j i k) (.var "flag"))) k₀ l)
        (fun σ σ' => DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ' ∧
          σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
          (∀ i' k', (i' ≠ i ∨ ∀ p < l.length, k' ≠ k₀ + p) →
            σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
          ∀ p, ∀ _ : p < l.length,
            σ'.vars (flgName j i (k₀ + p)) ≤ 1 ∧
            (σ'.vars (flgName j i (k₀ + p)) ≠ 0 ↔
              ScatVal (stepArenaP (masked G A₀) X w)
                (stepColoringP cap (masked G A₀) (colRead n C (sigL cap mb j)) X w) l[p]))
        (Kb * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro k₀ _
      refine (Spec.skip (B := B)
        (P := DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C')).post ?_
        |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, rfl, fun _ _ _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro k₀ hall
      obtain ⟨hxβ, hxr, hxt, hxK⟩ := hall x (by simp)
      refine ((atomView_spec hcsr hB hXalive hbud i k₀ hxβ
        (tableRank_of_mem_tablesAt (j + 1) _ hxβ).1 hxr hxt hxK).seq
        (ih (k₀ + 1) (fun s hs => hall s (by simp [hs]))) (fun _ _ _ hq => hq.1) ?_).mono
        (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' - ⟨-, hout', hc', hfl', hle', hval'⟩
        ⟨hpre'', hout'', hc'', hfl'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], by rw [hc'', hc'], ?_, ?_⟩
      · intro i' k' hik
        rw [hfl'' i' k' ?_, hfl' i' k' ?_]
        · rcases hik with h | h
          · exact fun hc => h hc.1
          · exact fun hc => h 0 (by simp) (by omega)
        · rcases hik with h | h
          · exact _root_.Or.inl h
          · exact _root_.Or.inr fun p hp => by
              have := h (p + 1) (by simp only [List.length_cons]; omega)
              omega
      · intro p hp
        match p with
        | 0 =>
            rw [Nat.add_zero, hfl'' i k₀ (_root_.Or.inr fun p _ => by omega)]
            exact ⟨hle', hval'⟩
        | q + 1 =>
            rw [show k₀ + (q + 1) = k₀ + 1 + q from by omega]
            simpa using hval'' q (by simpa using hp)

set_option maxHeartbeats 1000000 in
open Classical in
/-- Fold the streamed atom contract over a list of tabled formulas. -/
theorem blocksView_spec {bw nb : ℕ}
    {B q_top cap mb ns nt ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T A₀ : ℕ → ℕ} {C C' : ℕ → ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv Gam : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → A₀ (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, BallBudget n r G Alv O bw nb)
    {Kb Ki : ℕ} :
    ∀ (l : List (DistFO (sigL cap mb j) 1)) (i₀ : ℕ),
      (∀ β ∈ l, β ∈ tablesAt q_top cap mb φ j) →
      (∀ β ∈ l, ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          deadAtomKX σs.β n X.ncard mb bw nb σs.t ≤ Kb) →
      (∀ β ∈ l, Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki) →
      Spec B (DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C')
        (foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) i₀ l)
        (fun σ σ' => DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ' ∧
          σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
          (∀ i' k', (∀ p < l.length, i' ≠ i₀ + p) →
            σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
          ∀ p, ∀ hp : p < l.length,
            ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j l[p])).2,
              σ'.vars (flgName j (i₀ + p)
                  (posOf σs (bcAtomsOf q_top (stepFml cap mb j l[p])).2)) ≤ 1 ∧
              (σ'.vars (flgName j (i₀ + p)
                  (posOf σs (bcAtomsOf q_top (stepFml cap mb j l[p])).2)) ≠ 0 ↔
                ScatVal (stepArenaP (masked G A₀) X w)
                  (stepColoringP cap (masked G A₀) (colRead n C (sigL cap mb j)) X w) σs))
        (Ki * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro i₀ _ _ _
      refine (Spec.skip (B := B)
        (P := DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C')).post ?_
        |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, rfl, fun _ _ _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro i₀ hmem hbnd hcost
      have hx : x ∈ tablesAt q_top cap mb φ j := hmem x (by simp)
      refine (((atomsView_spec hcsr hB hXalive hbud i₀
          (bcAtomsOf q_top (stepFml cap mb j x)).2 0
          (fun s hs => ⟨mem_tablesAt_succ_of_mem_bcAtomsOf_right hx hs,
            (hbnd x (by simp) s hs).1, (hbnd x (by simp) s hs).2.1,
            (hbnd x (by simp) s hs).2.2⟩)).mono (hcost x (by simp))).seq
        (ih (i₀ + 1) (fun β hβ => hmem β (by simp [hβ]))
          (fun β hβ => hbnd β (by simp [hβ])) (fun β hβ => hcost β (by simp [hβ])))
        (fun _ _ _ hq => hq.1) ?_).mono (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' - ⟨-, hout', hc', hfl', hval'⟩
        ⟨hpre'', hout'', hc'', hfl'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], by rw [hc'', hc'], ?_, ?_⟩
      · intro i' k' hik
        rw [hfl'' i' k' (fun p hp => by
            have := hik (p + 1) (by simp only [List.length_cons]; omega)
            omega),
          hfl' i' k' (_root_.Or.inl (by have := hik 0 (by simp); omega))]
      · intro p hp
        match p with
        | 0 =>
            intro σs hσs
            simp only [List.getElem_cons_zero] at hσs ⊢
            obtain ⟨hlt, hget⟩ := getElem_posOf hσs
            have hb := hval' (posOf σs (bcAtomsOf q_top (stepFml cap mb j x)).2) hlt
            rw [Nat.zero_add, hget] at hb
            rw [Nat.add_zero, hfl'' i₀ _ (fun p _ => by omega)]
            exact hb
        | q + 1 =>
            intro σs hσs
            rw [show i₀ + (q + 1) = i₀ + 1 + q from by omega]
            exact hval'' q (by simpa using hp) σs (by simpa using hσs)

open Classical in
/-- The complete streamed scatter phase, specialized to the depth's table
list.  This is the exact flag interface consumed by readback. -/
theorem scatterViewStep {bw nb Kb Ki K : ℕ}
    {B q_top cap mb ns nt ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T A₀ : ℕ → ℕ} {C C' : ℕ → ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv Gam : ℕ → ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → A₀ (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, BallBudget n r G Alv O bw nb)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          deadAtomKX σs.β n X.ncard mb bw nb σs.t ≤ Kb)
    (hcost : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hK : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ K) :
    Spec B (DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C')
      (foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) 0
        (tablesAt q_top cap mb φ j))
      (fun σ σ' =>
        DeadView B q_top cap mb ns nt ell j φ G O T A₀ C X W w Alv Gam C' σ' ∧
        σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
        (∀ i' k', (∀ p < (tablesAt q_top cap mb φ j).length, i' ≠ p) →
          σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
        ∀ i, ∀ hi : i < (tablesAt q_top cap mb φ j).length,
          ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j
              (tablesAt q_top cap mb φ j)[i])).2,
            σ'.vars (flgName j i
                (posOf σs (bcAtomsOf q_top (stepFml cap mb j
                  (tablesAt q_top cap mb φ j)[i])).2)) ≤ 1 ∧
            (σ'.vars (flgName j i
                (posOf σs (bcAtomsOf q_top (stepFml cap mb j
                  (tablesAt q_top cap mb φ j)[i])).2)) ≠ 0 ↔
              ScatVal (stepArenaP (masked G A₀) X w)
                (stepColoringP cap (masked G A₀) (colRead n C (sigL cap mb j)) X w)
                σs))
      K := by
  simpa using
    (blocksView_spec hcsr hB hXalive hbud (tablesAt q_top cap mb φ j) 0
      (fun _ hβ => hβ) hbnd hcost).mono hK

end Lax3Proofs.Refine.CoverActiveStreamScatter
