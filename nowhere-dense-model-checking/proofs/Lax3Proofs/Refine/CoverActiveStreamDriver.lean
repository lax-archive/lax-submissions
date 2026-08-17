import Lax3Proofs.Refine.CoverActiveStreamInit
import Lax3Proofs.Refine.CoverActiveStreamLoop
import Lax3Proofs.Refine.OrderActiveBudget
import Lax3Proofs.RamDriverCompose
import Lax3Proofs.RamDriverWrites

/-!
# The recursive streamed active-cover driver

This file replaces the materialised cover phase of the historical driver by
one ordering, one live-prefix initializer, and the fused streamed centre loop
at every nonterminal depth.  The recursion itself is deliberately small: the
substantial semantic and cost work lives at the phase boundaries proved in
the preceding streamed modules.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamDriver

open Classical
open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBot
open Lax3Proofs.RamDriverCompose
open Lax3Proofs.RamDriverCluster (killSet markSet)
open Lax3Proofs.Refine.CoverActiveInit (activeInitCost)
open Lax3Proofs.Refine.CoverActiveStreamScratch
open Lax3Proofs.Refine.CoverActiveStreamInner
open Lax3Proofs.Refine.CoverActiveStreamInit
open Lax3Proofs.Refine.CoverActiveStreamLifecycle
open Lax3Proofs.Refine.CoverActiveStreamLoop
open Lax3Proofs.Refine.OrderActiveDriver
open Lax3Proofs.Refine.OrderActiveBudget
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## Recursive semantic surface -/

/-- The complete entry state of one streamed level.  The last two conjuncts
are the reusable storage suffix and the radix width computed once by the
root prologue. -/
def StreamLevelPreD {n : ℕ}
    (B q_top cap mb ns nt ell j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (D : Set (Fin n)) (σ : Env) : Prop :=
  LevelPre B n cap mb ns nt O T j M Gm C σ ∧
    TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ell φ σ ∧
    PlayRec B cap G j M Gm σ ∧
    TableInvOn q_top cap mb φ G j M C D σ ∧
    StreamScratchFrom B n cap mb ell j σ ∧
    StreamRadixReady B n σ

/-- Domain-aware correctness of the concrete streamed driver at its current
depth.  This is definitionally the successor contract consumed by
`streamInnerStep`, with the depth shift removed. -/
def StreamLevelImplementsAtD {n : ℕ}
    (B q_top cap mb ns nt ell j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (D : Set (Fin n)) (cmd : Com) (K : ℕ) : Prop :=
  (∀ v : Fin n, v ∈ D → M (v : ℕ) = 0) →
  (∀ c < sigL cap mb j, ∀ v < n, C c v ≤ 1) →
  Spec B
    (StreamLevelPreD B q_top cap mb ns nt ell j φ G O T M Gm C D)
    cmd
    (fun σ σ' =>
      LevelPostD B q_top cap mb φ G ns nt O T j M Gm C D σ σ' ∧
      σ'.out = σ.out ∧ StreamScratchFrom B n cap mb ell j σ')
    K

/-- Re-index the current-depth contract as the child contract expected by a
centre at the preceding depth. -/
theorem streamLevelImplementsD_of_at_succ
    {B n q_top cap mb ns nt ell j K : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {D : Set (Fin n)} {cmd : Com}
    (h : StreamLevelImplementsAtD B q_top cap mb ns nt ell (j + 1) φ G O T
      M Gm C D cmd K) :
    StreamLevelImplementsD B q_top cap mb ns nt ell j φ G O T M Gm C D cmd K := by
  intro hdead hbit
  exact (h hdead hbit).pre (fun _ hp => by
    obtain ⟨⟨hlevel, htables, hbase, hplay, htable⟩, hscratch, hradix⟩ := hp
    exact ⟨hlevel, htables, hbase, hplay, htable, hscratch, hradix⟩)

/-- Active ordering preserves every clean row in the reusable suffix. -/
theorem streamScratchFrom_run_activeOrderPhase
    {B n cap mb ell j R K : ℕ} {σ σ' : Env}
    (h : StreamScratchFrom B n cap mb ell j σ)
    (hr : Run B (activeOrderPhase j R) σ σ' K) :
    StreamScratchFrom B n cap mb ell j σ' := by
  apply h.run hr
  · intro d _ _; exact cpsName_notMem_activeOrderPhase j R d
  · intro d _ _; exact cluName_notMem_activeOrderPhase j R d
  · intro d _ _; exact resName_notMem_activeOrderPhase j R d
  · intro d _ _; exact batName_notMem_activeOrderPhase j R d
  · intro d _ _; exact alvName_notMem_activeOrderPhase j R (d + 1)
  · intro d _ _; exact gamName_notMem_activeOrderPhase j R (d + 1)
  · intro d _ _ s _; exact colName_notMem_activeOrderPhase j R (d + 1) s

/-- The root-computed radix width is a scalar frame of active ordering. -/
theorem streamRadixReady_run_activeOrderPhase
    {B n j R K : ℕ} {σ σ' : Env}
    (h : StreamRadixReady B n σ)
    (hr : Run B (activeOrderPhase j R) σ σ' K) :
    StreamRadixReady B n σ' := by
  rw [StreamRadixReady, hr.frame_var "rsbits"
    (rsbits_notMem_activeOrderPhase j R)]
  exact h

/-- Active ordering never changes a formula-table row. -/
theorem tableInvOn_run_activeOrderPhase
    {B n q_top cap mb j R K : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {M : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {D : Set (Fin n)} {σ σ' : Env}
    (h : TableInvOn q_top cap mb φ G j M C D σ)
    (hr : Run B (activeOrderPhase j R) σ σ' K) :
    TableInvOn q_top cap mb φ G j M C D σ' := by
  intro i hi
  obtain ⟨Tb, hTb, hbit, hval⟩ := h i hi
  exact ⟨Tb,
    (hr.frame_arr _ (tabName_notMem_activeOrderPhase j R j i)).trans hTb,
    hbit, hval⟩

/-- At the end of the centre loop every ambient live vertex has appeared as
a centre, so the progressive mask is zero again.  Together with the row-local
release clauses this reconstructs the current reusable scratch head. -/
theorem streamScratchHead_of_finalStable
    {B n q_top cap mb ns nt q j bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {σ : Env}
    (hcentres : Lax3Proofs.RamCoverActive.CentresBy n q A₀ π centre)
    (h : StreamStableState B n q_top cap mb ns nt q j q bits ell φ G A₀ π
      centre O T Xmem asg M Gm C σ) :
    StreamScratchHead B n cap mb j σ := by
  have hmask : σ.arrs (cpsName j) = arrOf n M := by
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      Lax3Proofs.Refine.CoverActiveStreamDepth.streamDepthSwap_alv] using
        h.turn.mask_arr
  have hzero : ∀ u < n, M u = 0 := by
    intro u hu
    apply (h.turn.state.mask u hu).2
    by_cases halive : A₀ u = 0
    · exact Or.inl halive
    · obtain ⟨k, hk, hku⟩ := hcentres.complete u hu halive
      exact Or.inr ⟨k, hk, hku⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hmem, -⟩ := h.logical_level
  refine {
    mask_zero := hmask.trans
      (Lax3Proofs.RamDriverOrder.arrOf_congr fun u hu => hzero u hu)
    dist_words := ?_
    cluster_zero := h.cluster_zero
    retained_zero := h.retained_zero
    batch_zero := h.batch_zero
    child_zero := h.child_zero
    game_zero := h.game_zero
    colours_zero := h.colours_zero }
  intro v hv
  exact hmem.2.1 v (by
    simpa only [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
      Lax3Proofs.Refine.CoverActiveStreamDepth.streamDepthSwap_dist] using hv)

/-! ## Program text -/

noncomputable def streamDriverAux
    (q_top cap mb ell R : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ → ℕ → Com
  | 0, j => baseCom q_top cap mb j φ
  | f + 1, j =>
      .seq (activeOrderPhase j R)
        (.seq (streamInitAtDepthCom j cap)
          (streamCentreLoopCom q_top cap mb j φ
            (streamDriverAux q_top cap mb ell R φ f (j + 1))))

noncomputable def streamDriverAt
    (q_top cap mb ell R : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) : Com :=
  streamDriverAux q_top cap mb ell R φ (ell - j) j

theorem streamDriverAt_bot
    (q_top cap mb ell R : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    streamDriverAt q_top cap mb ell R φ ell =
      baseCom q_top cap mb ell φ := by
  rw [streamDriverAt, Nat.sub_self, streamDriverAux]

theorem streamDriverAt_succ
    (q_top cap mb ell R : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {j : ℕ} (hj : j < ell) :
    streamDriverAt q_top cap mb ell R φ j =
      .seq (activeOrderPhase j R)
        (.seq (streamInitAtDepthCom j cap)
          (streamCentreLoopCom q_top cap mb j φ
            (streamDriverAt q_top cap mb ell R φ (j + 1)))) := by
  obtain ⟨f, hf⟩ : ∃ f, ell - j = f + 1 := ⟨ell - j - 1, by omega⟩
  rw [streamDriverAt, hf, streamDriverAux, streamDriverAt,
    show ell - (j + 1) = f by omega]

/-! ## Recursive ownership -/

theorem belowArr_notMem_warrs_streamDriverAux
    (q_top cap mb ell R : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ (f d : ℕ) {a : String}, Lax3Proofs.RamDriverWrites.BelowArr d a →
      a ∉ (streamDriverAux q_top cap mb ell R φ f d).warrs := by
  intro f
  induction f with
  | zero =>
      intro d a h hm
      rw [streamDriverAux] at hm
      exact Lax3Proofs.RamDriverWrites.belowArr_notMem_warrs_baseCom
        q_top cap mb d φ h hm
  | succ f ih =>
      intro d a h hm
      rw [streamDriverAux] at hm
      rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hm with hm | hm
      · exact belowArr_notMem_activeOrderPhase h hm
      rcases Lax3Proofs.RamDriverWrites.mem_warrs_seq hm with hm | hm
      · exact belowArr_notMem_warrs_streamInitAtDepthCom h hm
      · exact (belowArr_notMem_warrs_streamCentreLoopCom
          q_top cap mb d φ (fun a ha => ih (d + 1) ha) h) hm

theorem belowVar_notMem_wvars_streamDriverAux
    (q_top cap mb ell R : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∀ (f d : ℕ) {y : String}, Lax3Proofs.RamDriverWrites.BelowVar d y →
      y ∉ (streamDriverAux q_top cap mb ell R φ f d).wvars := by
  intro f
  induction f with
  | zero =>
      intro d y h hm
      rw [streamDriverAux] at hm
      exact Lax3Proofs.RamDriverWrites.belowVar_notMem_wvars_baseCom
        q_top cap mb d φ h hm
  | succ f ih =>
      intro d y h hm
      rw [streamDriverAux] at hm
      rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hm with hm | hm
      · exact belowVar_notMem_activeOrderPhase h hm
      rcases Lax3Proofs.RamDriverWrites.mem_wvars_seq hm with hm | hm
      · exact belowVar_notMem_wvars_streamInitAtDepthCom h hm
      · exact (belowVar_notMem_wvars_streamCentreLoopCom
          q_top cap mb d φ (fun y hy => ih (d + 1) hy) h) hm

theorem belowArr_notMem_warrs_streamDriverAt
    {q_top cap mb ell R d : ℕ} {φ : Lax3.FirstOrder.FO 0} {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr d a) :
    a ∉ (streamDriverAt q_top cap mb ell R φ d).warrs := by
  rw [streamDriverAt]
  exact belowArr_notMem_warrs_streamDriverAux q_top cap mb ell R φ
    (ell - d) d h

theorem belowVar_notMem_wvars_streamDriverAt
    {q_top cap mb ell R d : ℕ} {φ : Lax3.FirstOrder.FO 0} {y : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar d y) :
    y ∉ (streamDriverAt q_top cap mb ell R φ d).wvars := by
  rw [streamDriverAt]
  exact belowVar_notMem_wvars_streamDriverAux q_top cap mb ell R φ
    (ell - d) d h

/-- The concrete recursive call at `j+1` owns exactly the successor suffix
and therefore satisfies the centre seam's complete frame contract. -/
theorem streamInnerFrames_driverAt
    {q_top cap mb ell R j : ℕ} {φ : Lax3.FirstOrder.FO 0} :
    StreamInnerFrames j
      (streamDriverAt q_top cap mb ell R φ (j + 1)) := by
  refine {
    saved_var := ?_
    parent_arr := ?_
    below_arr := fun a ha => belowArr_notMem_warrs_streamDriverAt ha
    below_var := fun y hy => belowVar_notMem_wvars_streamDriverAt hy }
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;>
      exact belowVar_notMem_wvars_streamDriverAt
        ⟨j, Nat.lt_succ_self j, by tauto⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      exact belowArr_notMem_warrs_streamDriverAt
        ⟨j, Nat.lt_succ_self j, by tauto⟩

/-! ## Recursive correctness -/

open Classical in
/-- The complete streamed active driver, proved by depth induction.  Every
centre is charged at its own fixed mathematical ball weight, so the recursive
budget and the scatter budget remain centre-indexed all the way to the sigma
recurrence. -/
theorem streamLevelAt
    {B n q_top cap mb ns nt ell s R d D₁ Kmass : ℕ} {N : ℕ → ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    {Katom : ℕ → ℕ} {Ki Ksc Ks Kl : ℕ → ℕ → ℕ}
    (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ell * (2 * cap + 1))
    (hell : ell = N (2 * s + 2))
    (hB : WordBoundK B n 1 ns cap mb)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T) (hnt : ns ≤ nt)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧
        2 * s + 2 ≤ Bd.ncard ∧
          DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ell, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ sa ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        sa.r + 1 < B ∧ sa.t + n + mb < B ∧
          ∀ x z, x ≤ z → Lax3Proofs.Refine.ScatterDeadTurn.deadAtomKX
            sa.β n x mb z z sa.t ≤ Katom z)
    (hcostI : ∀ j < ell, ∀ β ∈ tablesAt q_top cap mb φ j, ∀ z,
      Katom z * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j z)
    (hKsc : ∀ j < ell, ∀ z,
      Ki j z * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j z)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ell, ∀ z,
      Lax3Proofs.Refine.CoverActiveStreamLifecycle.streamCentreLifecycleCost
        q_top cap mb j z z z (Kl (j + 1) z) (Ksc j z) φ ≤ Ks j z)
    (hKbase : ∀ m,
      Lax3Proofs.RamDriverBot.baseCost q_top cap mb ell m φ ≤ Kl ell m)
    (horder : ∀ j < ell, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      Lax3Proofs.RamDriverMember.OrderImplementsA B n nt cap mb ns j O T M Gm C
        (Lax3Proofs.RamCoverActiveMass.ActiveOrderP G cap Kmass)
        (activeOrderPhase j R)
        (activeOrderCost d D₁ R
          (Lax3Proofs.Refine.MassWeight.arenaWeight n G M)))
    (hKl : ∀ j < ell, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ k ∈ Finset.range t, bs k) ≤ Kmass * (m + 1) →
      activeOrderCost d D₁ R m +
          (activeInitCost t +
            ((∑ k ∈ Finset.range t,
              (streamSearchSortCost (Nat.clog 2 n) (bs k) (bs k) +
                Ks j (bs k) + 4)) + 6)) ≤ Kl j m) :
    ∀ j ≤ ell, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      StreamLevelImplementsAtD B q_top cap mb ns nt ell j φ G O T M Gm C D
        (streamDriverAt q_top cap mb ell R φ j)
        (Kl j (Lax3Proofs.Refine.MassWeight.arenaWeight n G M)) := by
  have key : ∀ f j, ell - j = f → j ≤ ell →
      ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
        StreamLevelImplementsAtD B q_top cap mb ns nt ell j φ G O T M Gm C D
          (streamDriverAt q_top cap mb ell R φ j)
          (Kl j (Lax3Proofs.Refine.MassWeight.arenaWeight n G M)) := by
    intro f
    induction f with
    | zero =>
        intro j hfj hj M Gm C D hDdead hbit
        have hje : j = ell := by omega
        subst j
        refine Spec.of_exists fun σ hpre => ?_
        obtain ⟨hlevel, htables, hbase, hplay, htable, -, -⟩ := hpre
        have hbot : Lax3Proofs.RamBfs.masked G M = ⊥ :=
          eq_bot_of_playOk_full hQ
            (by rw [← hell]; exact playOk_of_playRec hplay)
        have hbaseK : Lax3Proofs.RamDriverBot.baseCost q_top cap mb ell
            (arenaSize n M) φ ≤
            Kl ell (Lax3Proofs.Refine.MassWeight.arenaWeight n G M) :=
          le_trans
            (Lax3Proofs.RamDriverBot.baseCost_mono q_top cap mb ell φ
              (Lax3Proofs.Refine.MassWeight.arenaSize_le_arenaWeight n G M))
            (hKbase _)
        obtain ⟨σ', hr, hpost, hout⟩ :=
          (baseImplementsD hbaseK hB hbot hDdead hbit).run
            ⟨hlevel, htables, hbase, htable⟩
        refine ⟨σ', _, ?_, le_rfl, hpost, hout, ?_⟩
        · simpa [streamDriverAt_bot] using hr
        · intro depth hdepth hlt
          omega
    | succ f ih =>
        intro j hfj hj M Gm C D hDdead hbit
        have hjell : j < ell := by omega
        refine Spec.of_exists fun σ hpre => ?_
        obtain ⟨hlevel₀, htables₀, hbase₀, hplay₀, htable₀,
          hscratch₀, hradix₀⟩ := hpre
        obtain ⟨σ₁, hr₁, hlevel₁, hout₁, hctr₁, hres₁, hgam₁, hpar₁,
            q, π, centre, hqn, hord, hcentre, horderP⟩ :=
          (horder j hjell M Gm C).run hlevel₀
        have htables₁ : TablesSized q_top cap mb φ n σ₁ := htables₀.run hr₁
        have hbase₁ : BaseArrs B q_top cap mb ell φ σ₁ := hbase₀.run hr₁
        have hplay₁ : PlayRec B cap G j M Gm σ₁ :=
          hplay₀.congr (fun a _ => hctr₁ a) (fun a _ => hres₁ a)
            (fun a _ => hgam₁ a) (fun a _ => hpar₁ a)
        have htable₁ : TableInvOn q_top cap mb φ G j M C D σ₁ :=
          tableInvOn_run_activeOrderPhase htable₀ hr₁
        have hscratch₁ : StreamScratchFrom B n cap mb ell j σ₁ :=
          streamScratchFrom_run_activeOrderPhase hscratch₀ hr₁
        have hradix₁ : StreamRadixReady B n σ₁ :=
          streamRadixReady_run_activeOrderPhase hradix₀ hr₁
        have hlevelMem := hlevel₁
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
          Mem, mm, -, hmm, henum, -⟩ := hlevelMem
        have hqmm : q = mm := horderP.count_eq_memEnum henum
        have hqB : q < B := lt_of_le_of_lt hqn hB.n_lt
        have hrB : 2 * cap + 1 < B := by
          have := hB.arena
          omega
        obtain ⟨σ₂, hr₂, Xmem, asg, Mcur, hstable₂, htable₂, hout₂⟩ :=
          (streamInitStableStep horderP.centres hB.n_lt hqB hrB).run
            { init :=
                { level := hlevel₁
                  count_var := by simpa [hqmm] using hmm
                  centre_arr := hord
                  mask_zero := (hscratch₁.head hjell).mask_zero
                  bits_var := hradix₁.1 }
              tables := htables₁
              base_arrs := hbase₁
              play := hplay₁
              table_inv := htable₁
              head := hscratch₁.head hjell
              scratch := hscratch₁.tail }
        have hloopInv : StreamLoopInv B n q_top cap mb ns nt q j
            (Nat.clog 2 n) ell φ G M π centre O T Gm C D σ₂.out
            (σ₂.setVar "c" 0) := by
          refine ⟨Xmem, asg, Mcur, hstable₂, rfl, ?_⟩
          simpa [streamDone] using htable₂
        let W : ℕ → ℕ := fun k =>
          Lax3Proofs.Refine.CoverActiveBudget.activeBallWeight
            n G M π centre O cap k
        have hchild : ∀ k, k < q → ∀ (Xa Ra Wa Alv Gam : ℕ → ℕ)
            (C' : ℕ → ℕ → ℕ) (w : Fin mb → Fin n),
            Lax3Proofs.Refine.MassWeight.arenaWeight n G Alv ≤ W k →
            StreamLevelImplementsD B q_top cap mb ns nt ell j φ G O T
              Alv Gam C' (killSet M (markSet n Xa) (markSet n Wa))
              (streamDriverAt q_top cap mb ell R φ (j + 1))
              (Kl (j + 1) (W k)) := by
          intro k hk Xa Ra Wa Alv Gam C' w hweight hdead hcol
          have hnext : ell - (j + 1) = f := by omega
          have hrec := ih (j + 1) hnext (by omega) Alv Gam C'
            (killSet M (markSet n Xa) (markSet n Wa))
          have hrec' := streamLevelImplementsD_of_at_succ hrec
          exact (hrec' hdead hcol).mono (hKmono (j + 1) hweight)
        have hlife : ∀ k < q, ∀ tail (Xm am Mm : ℕ → ℕ),
            tail ≤ W k →
            Lax3Proofs.RamDriverDescend.expandRowSum O Xm 0 tail ≤ W k →
            Lax3Proofs.Refine.CoverActiveStreamLifecycle.streamCentreLifecycleCost
              q_top cap mb j tail
                (Lax3Proofs.RamDriverDescend.expandRowSum O Xm 0 tail)
                (W k) (Kl (j + 1) (W k)) (Ksc j (W k)) φ ≤ Ks j (W k) := by
          intro k hk tail Xm am Mm htail hrows
          exact le_trans
            (streamCentreLifecycleCost_le_diagonal q_top cap mb j
                (Ksc j (W k)) φ htail hrows)
            (hKs j hjell (W k))
        obtain ⟨σ₃, hr₃, Xmem₃, asg₃, M₃, hstable₃, htable₃, hout₃⟩ :=
          (streamCentreLoopStep
            (Kinner := fun k => Kl (j + 1) (W k))
            (Kb := fun k => Katom (W k))
            (Ki := fun k => Ki j (W k))
            (Kscatter := fun k => Ksc j (W k))
            (Klife := fun k => Ks j (W k))
            hchild streamInnerFrames_driverAt hcap hcsr hnt hB horderP.centres
            hmb hjell hradix₁.2.1 hradix₁.2.2 rfl
            (fun k hk Xa β hβ sa hsa hcard => by
              have h := hbnd j hjell β hβ sa hsa
              exact ⟨h.1, h.2.1,
                h.2.2 (markSet n Xa).ncard (W k) hcard⟩)
            (fun k hk β hβ => hcostI j hjell β hβ (W k))
            (fun k hk => hKsc j hjell (W k)) hlife hDdead).run hloopInv
        have hmass : (∑ k ∈ Finset.range q, W k) ≤
            Kmass * (Lax3Proofs.Refine.MassWeight.arenaWeight n G M + 1) := by
          exact Lax3Proofs.Refine.CoverActiveBudget.sum_activeBallWeight_le
            horderP hcsr
        have hqweight : q ≤
            Lax3Proofs.Refine.MassWeight.arenaWeight n G M :=
          Lax3Proofs.RamCoverActiveMass.centreCount_le_arenaWeight
            G horderP.centres
        have hcostAll :
            activeOrderCost d D₁ R
                (Lax3Proofs.Refine.MassWeight.arenaWeight n G M) +
              (activeInitCost q +
                ((∑ k ∈ Finset.range q,
                  (streamSearchSortCost (Nat.clog 2 n) (W k) (W k) +
                    Ks j (W k) + 4)) + 6)) ≤
              Kl j (Lax3Proofs.Refine.MassWeight.arenaWeight n G M) :=
          hKl j hjell _ q hqweight W hmass
        have hrun : Run B (streamDriverAt q_top cap mb ell R φ j) σ σ₃
            (Kl j (Lax3Proofs.Refine.MassWeight.arenaWeight n G M)) := by
          rw [streamDriverAt_succ q_top cap mb ell R φ hjell]
          exact (hr₁.seq (hr₂.seq hr₃)).mono (by
            simpa [W, Nat.add_assoc] using hcostAll)
        have hhead₃ : StreamScratchHead B n cap mb j σ₃ :=
          streamScratchHead_of_finalStable horderP.centres hstable₃
        refine ⟨σ₃, _, hrun, le_rfl, ?_, ?_, ?_⟩
        · exact ⟨hstable₃.level, hstable₃.tables, htable₃⟩
        · exact hout₃.trans (hout₂.trans hout₁)
        · exact StreamScratchFrom.of_head_tail hhead₃ hstable₃.scratch
  intro j hj M Gm C D
  exact key (ell - j) j rfl hj M Gm C D

open Classical in
/-- The recursive streamed driver with its ordering phase instantiated by
the compact active-order implementation.  All program phases are concrete;
the remaining premises are graph-theoretic bounds and scalar budget
inequalities. -/
theorem streamLevelAtActive
    {B n q_top cap mb ns nt ell s R d D₁ Kmass : ℕ} {N : ℕ → ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    {Katom : ℕ → ℕ} {Ki Ksc Ks Kl : ℕ → ℕ → ℕ}
    (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ell * (2 * cap + 1))
    (hell : ell = N (2 * s + 2))
    (hB : WordBoundK B n 1 ns cap mb)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T) (hnt : ns ≤ nt)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧
        2 * s + 2 ≤ Bd.ncard ∧
          DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ell, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ sa ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        sa.r + 1 < B ∧ sa.t + n + mb < B ∧
          ∀ x z, x ≤ z → Lax3Proofs.Refine.ScatterDeadTurn.deadAtomKX
            sa.β n x mb z z sa.t ≤ Katom z)
    (hcostI : ∀ j < ell, ∀ β ∈ tablesAt q_top cap mb φ j, ∀ z,
      Katom z * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j z)
    (hKsc : ∀ j < ell, ∀ z,
      Ki j z * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j z)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ell, ∀ z,
      streamCentreLifecycleCost q_top cap mb j z z z
        (Kl (j + 1) z) (Ksc j z) φ ≤ Ks j z)
    (hKbase : ∀ m,
      Lax3Proofs.RamDriverBot.baseCost q_top cap mb ell m φ ≤ Kl ell m)
    (hwidthB : n + activeOrderWidth d D₁ R (n + ns) + 1 < B)
    (hwidthW : activeOrderWidth d D₁ R (n + ns) ≤ nt)
    (hdeg : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (markSet n M)),
      Lax3Proofs.Augmentation.LowDegreeVertices
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) d)
    (hdens : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (markSet n M))
        (D : ℕ → Lax3Proofs.Augmentation.Orientation mm) (i : ℕ), i ≤ R →
      Lax3Proofs.Augmentation.IsAugChain
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) D i →
      (∀ l < i, Lax3Proofs.Augmentation.GreedyFratRound (D l) (D (l + 1))) →
      Lax3Proofs.Augmentation.AugmentedDepthOneDensity D i D₁)
    (hKmass : 1 ≤ Kmass)
    (hdegree : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (markSet n M))
        {D : ℕ → Lax3Proofs.Augmentation.Orientation mm}
        {d₀ k : ℕ} {pi : Equiv.Perm (Fin mm)},
      Lax3Proofs.CoverDegree.AugChainData
          (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) D pi R d₀ k →
        ∀ v : Fin mm,
          (Lax12.ColoringNumbers.wreach
            (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) pi
              (2 * cap) v).ncard ≤ Kmass)
    (hKl : ∀ j < ell, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ k ∈ Finset.range t, bs k) ≤ Kmass * (m + 1) →
      activeOrderCost d D₁ R m +
          (activeInitCost t +
            ((∑ k ∈ Finset.range t,
              (streamSearchSortCost (Nat.clog 2 n) (bs k) (bs k) +
                Ks j (bs k) + 4)) + 6)) ≤ Kl j m) :
    ∀ j ≤ ell, ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (D : Set (Fin n)),
      StreamLevelImplementsAtD B q_top cap mb ns nt ell j φ G O T M Gm C D
        (streamDriverAt q_top cap mb ell R φ j)
        (Kl j (Lax3Proofs.Refine.MassWeight.arenaWeight n G M)) := by
  have hBns : n + ns + 1 < B := by
    have ha := hB.arena
    omega
  refine streamLevelAt hcap hmb hell hB hcsr hnt hQ hbnd hcostI hKsc
    hKmono hKs hKbase ?_ hKl
  intro jd hj M Gm C
  apply activeOrderPhase_weight_spec (R := R) (d := d) (D₁ := D₁)
    (Kmass := Kmass) hcsr hBns
  · exact lt_of_le_of_lt (Nat.add_le_add_right
      (Nat.add_le_add_left
        (activeOrderWidth_mono
          (Lax3Proofs.Refine.MassWeight.arenaWeight_le_root hcsr M)) n) 1) hwidthB
  · exact le_trans
      (activeOrderWidth_mono
        (Lax3Proofs.Refine.MassWeight.arenaWeight_le_root hcsr M)) hwidthW
  · exact hdeg M
  · exact hdens M
  · exact hKmass
  · exact hdegree M

end Lax3Proofs.Refine.CoverActiveStreamDriver
