import Lax3Proofs.Refine.CoverActiveStreamDriver
import Lax3Proofs.Refine.CoverActiveRadixWidth
import Lax3Proofs.Refine.ActiveRoot

/-!
# The streamed active driver at the decoded root

The root computes the radix width once, between the deduplicating decode
and the recursive streamed driver.  The reusable suffix is supplied by the
zeroed initial RAM memory and framed across the decode.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamRoot

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverMember
open Lax3Proofs.RamDriverDedup (dedupNs dedupOffset dedupTarget DedupMem)
open Lax3Proofs.RamDriverWrites
open Lax3Proofs.Refine.DriverRootD
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.CoverActiveStreamScratch
open Lax3Proofs.Refine.CoverActiveStreamInner
open Lax3Proofs.Refine.CoverActiveStreamDriver
open Lax3Proofs.Refine.CoverActiveRadixWidth
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

private theorem scratchName_notMem_decodeComD {a : String}
    (hoff : a ≠ "off") (htgt : a ≠ "tgt") (halv : a ≠ alvName 0)
    (hgam : a ≠ gamName 0) (hmem : a ≠ memName 0) (hdmk : a ≠ "dmk") :
    a ∉ decodeComD.warrs := by
  simp [decodeComD, dedupComL, Lax3Proofs.Refine.BridgeSeamProbe.lwCom,
    Lax3Proofs.RamDriver.decodeCom, Lax3Proofs.RamDriver.readLoop,
    Lax3Proofs.RamDriver.fillCom, Lax3Proofs.RamDriver.fillUpto, Fill.put,
    Lax3Proofs.RamDriverDedup.dedupCom, Lax3Proofs.RamDriverDedup.dedupRow,
    Lax3Proofs.RamDriverDedup.dedupSlot, Lax3Proofs.RamDriverDedup.dedupUnmark,
    Lax3Proofs.RamDriverDedup.dedupZero, Lax3Proofs.RamDriverDedup.dedupHalve,
    Com.warrs, hoff, htgt, halv, hgam, hmem, hdmk]

private theorem cpsName_notMem_decodeComD (d : ℕ) :
    cpsName d ∉ decodeComD.warrs := by
  apply scratchName_notMem_decodeComD <;>
    simp [cpsName, alvName, gamName, memName, String.ext_iff]

private theorem pdsName_notMem_decodeComD (d : ℕ) :
    pdsName d ∉ decodeComD.warrs := by
  apply scratchName_notMem_decodeComD <;>
    simp [pdsName, balAltName, alvName, gamName, memName, String.ext_iff]

private theorem cluName_notMem_decodeComD (d : ℕ) :
    cluName d ∉ decodeComD.warrs := by
  apply scratchName_notMem_decodeComD <;>
    simp [cluName, alvName, gamName, memName, String.ext_iff]

private theorem resName_notMem_decodeComD (d : ℕ) :
    resName d ∉ decodeComD.warrs := by
  apply scratchName_notMem_decodeComD <;>
    simp [resName, alvName, gamName, memName, String.ext_iff]

private theorem batName_notMem_decodeComD (d : ℕ) :
    batName d ∉ decodeComD.warrs := by
  apply scratchName_notMem_decodeComD <;>
    simp [batName, alvName, gamName, memName, String.ext_iff]

private theorem alvSuccName_notMem_decodeComD (d : ℕ) :
    alvName (d + 1) ∉ decodeComD.warrs := by
  apply scratchName_notMem_decodeComD
  · simp [alvName, String.ext_iff]
  · simp [alvName, String.ext_iff]
  · intro h
    have := alvName_inj h
    omega
  · simp [alvName, gamName, String.ext_iff]
  · simp [alvName, memName, String.ext_iff]
  · simp [alvName, String.ext_iff]

private theorem gamSuccName_notMem_decodeComD (d : ℕ) :
    gamName (d + 1) ∉ decodeComD.warrs := by
  apply scratchName_notMem_decodeComD
  · simp [gamName, String.ext_iff]
  · simp [gamName, String.ext_iff]
  · simp [gamName, alvName, String.ext_iff]
  · intro h
    have := gamName_inj h
    omega
  · simp [gamName, memName, String.ext_iff]
  · simp [gamName, String.ext_iff]

private theorem colSuccName_notMem_decodeComD (d s : ℕ) :
    colName (d + 1) s ∉ decodeComD.warrs := by
  apply scratchName_notMem_decodeComD <;>
    simp [colName, alvName, gamName, memName, String.ext_iff]

/-- The composed decode changes only root data and fixed deduplication
scratch, so every reusable streamed row survives it. -/
theorem streamScratchFrom_run_decodeComD
    {B n cap mb ell j K : ℕ} {σ σ' : Env}
    (h : StreamScratchFrom B n cap mb ell j σ)
    (hr : Run B decodeComD σ σ' K) :
    StreamScratchFrom B n cap mb ell j σ' := by
  apply h.run hr
  · intro d _ _; exact cpsName_notMem_decodeComD d
  · intro d _ _; exact cluName_notMem_decodeComD d
  · intro d _ _; exact resName_notMem_decodeComD d
  · intro d _ _; exact batName_notMem_decodeComD d
  · intro d _ _; exact alvSuccName_notMem_decodeComD d
  · intro d _ _; exact gamSuccName_notMem_decodeComD d
  · intro d _ _ s _; exact colSuccName_notMem_decodeComD d s

/-! ## Root program -/

open Classical in
/-- Deduplicate the input CSR, compute its radix width once, run the
streamed recursive driver, and read back the sentence. -/
noncomputable def driverRootStream (q_top cap mb R ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : Com :=
  .seq decodeComD
    (.seq radixWidthCom
      (.seq (streamDriverAt q_top cap mb ell R φ 0)
        (sentenceCom q_top cap mb φ)))

/-- Root memory together with the reusable suffix supplied by fresh RAM
memory.  Unlike a clearing prologue, this clause costs no machine steps. -/
def StreamRootPreD (B n ns W q_top cap mb ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (x : List ℕ) (σ : Env) : Prop :=
  DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧ DepthMem n cap mb σ ∧
    OrderMem B n 0 W σ ∧ DedupMem n σ ∧
    TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ell φ σ ∧
    StreamScratchFrom B n cap mb ell 0 σ ∧ σ.inp = x ∧ σ.out = []

section InitEnv

variable {B n ns W q_top cap mb ell : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {x : List ℕ} {σ : Env}

private theorem zeroArray_initEnv {a : String} {k : ℕ}
    (h : σ.arrs a = arrOf k (fun _ => 0)) :
    (initEnv (Lax3Proofs.Refine.BridgeSeamProbe.extOf σ) x).arrs a =
      arrOf k (fun _ => 0) := by
  rw [Lax3Proofs.Refine.BridgeSeamProbe.arrs_initEnv,
    Lax3Proofs.Refine.BridgeSeamProbe.extOf, h, length_arrOf]
  simp [arrOf, List.map_const']

/-- Every reusable streamed row transfers to the zero-filled arrays of a
fresh machine environment with the same allocation descriptor. -/
theorem streamScratchFrom_initEnv (hB : 0 < B)
    (h : StreamScratchFrom B n cap mb ell 0 σ) :
    StreamScratchFrom B n cap mb ell 0
      (initEnv (Lax3Proofs.Refine.BridgeSeamProbe.extOf σ) x) := by
  intro d hd0 hdell
  have hh := h d hd0 hdell
  exact {
    mask_zero := zeroArray_initEnv hh.mask_zero
    dist_words := fun _ hv =>
      Lax3Proofs.Refine.BridgeSeamProbe.mem_initEnv_lt hB hv
    cluster_zero := zeroArray_initEnv hh.cluster_zero
    retained_zero := zeroArray_initEnv hh.retained_zero
    batch_zero := zeroArray_initEnv hh.batch_zero
    child_zero := zeroArray_initEnv hh.child_zero
    game_zero := zeroArray_initEnv hh.game_zero
    colours_zero := fun s hs => zeroArray_initEnv (hh.colours_zero s hs) }

/-- The complete streamed root precondition is available at the compiler's
fresh initial environment; all arrays retain their prescribed lengths and
start zero, while the live-width scalar correctly starts at zero. -/
theorem streamRootPreD_initEnv (hB : 0 < B)
    (h : StreamRootPreD B n ns W q_top cap mb ell φ x σ) :
    StreamRootPreD B n ns W q_top cap mb ell φ x
      (initEnv (Lax3Proofs.Refine.BridgeSeamProbe.extOf σ) x) := by
  obtain ⟨hdm, hmem, hdep, hord, hdd, htsz, hbarr, hscratch, -, -⟩ := h
  exact ⟨
    Lax3Proofs.Refine.DriverRootD.decodeMem_of_zero
      (Lax3Proofs.Refine.BridgeSeamProbe.decodeMem_initEnv hdm),
    Lax3Proofs.Refine.BridgeSeamProbe.levelMem_initEnv hB hmem,
    Lax3Proofs.Refine.BridgeSeamProbe.depthMem_initEnv hdep,
    Lax3Proofs.Refine.BridgeSeamProbe.orderMem_initEnv_of hB hord,
    Lax3Proofs.Refine.BridgeSeamProbe.dedupMem_initEnv hdd,
    Lax3Proofs.Refine.BridgeSeamProbe.tablesSized_initEnv htsz,
    Lax3Proofs.Refine.BridgeSeamProbe.baseArrs_initEnv hbarr,
    streamScratchFrom_initEnv hB hscratch, rfl, rfl⟩

end InitEnv

section Correct

variable {n ns : ℕ} {B q_top cap mb R ell W Kd Kl Ks Kmass : ℕ}
  {G : SimpleGraph (Fin n)} {x : List ℕ} {φ : Lax3.FirstOrder.FO 0}

open Classical in
/-- Root composition from a domain-aware streamed level contract. -/
theorem driverStream_correct
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top)
    (hB : WordBoundK B n 1 ns cap mb) (hKmass : 1 ≤ Kmass)
    (hxB : ∀ v ∈ x, v < B) (hWB : W < B) (hnsW : ns ≤ W)
    (hdec : DecodeImplementsDL B x G ns W Kd)
    (hlev : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      (∀ v < n, M v ≠ 0) →
      StreamLevelImplementsAtD B q_top cap mb (dedupNs x) W ell 0 φ G
        (dedupOffset x) (dedupTarget x) M Gm C ∅
        (streamDriverAt q_top cap mb ell R φ 0) Kl)
    (hsent : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      SentenceImplements B q_top cap mb (dedupNs x) W φ G
        (dedupOffset x) (dedupTarget x) M Gm C Ks) :
    Spec B (StreamRootPreD B n ns W q_top cap mb ell φ x)
      (driverRootStream q_top cap mb R ell φ)
      (fun _ σ' => σ'.out =
        [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kd + (radixWidthCost n + (Kl + Ks))) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hdm, hmem, hdep, hord₀, hdmem, htsz, hbarr, hscratch,
      hinp, hout⟩ := hσ
  obtain ⟨σ₁, hrun₁, hout₁, hcsrD, hsimpD, hnsle, hpadD, hn₁, hoff₁,
      htgt₁, hm₁, hordmem₁, hdmem₁, ⟨M, hM₁, hMone⟩,
      ⟨Gm, hGm₁, hGmone⟩,
      ⟨Mem, hMem₁, hMemid, hMnum₁⟩⟩ :=
    (hdec hxB hB.succ_lt hB.ns_lt hWB hnsW).run
      ⟨hdm, hord₀, hdmem, hinp, hout⟩
  have hBD : WordBoundK B n 1 (dedupNs x) cap mb :=
    wordBoundK_anti hnsle hB
  have hdouble : ∀ p < n, p + p < B := by
    intro p hp
    have ha := hB.arena
    omega
  obtain ⟨σ₂, hrunᵣ, hn₂, hbits₂, hpow₂⟩ :=
    (radixWidthCom_double_spec hB.one_lt hB.n_lt hdouble).run hn₁
  have hfaᵣ : ∀ a, σ₂.arrs a = σ₁.arrs a := fun a =>
    hrunᵣ.frame_arr a (by
      simp [radixWidthCom, radixWidthTurn, Com.warrs])
  have hfvᵣ : ∀ y, y ≠ "rsbits" → y ≠ "rspow" →
      σ₂.vars y = σ₁.vars y := fun y hb hp =>
    hrunᵣ.frame_var y (by
      simp [radixWidthCom, radixWidthTurn, Com.wvars, hb, hp])
  have houtᵣ : σ₂.out = σ₁.out :=
    hrunᵣ.out_eq (by
      simp [radixWidthCom, radixWidthTurn, Com.NoWrite])
  have hTB : ∀ z < W, dedupTarget x z < B := fun z hz => by
    rcases lt_or_ge z (dedupNs x) with h | h
    · exact lt_trans (hcsrD.target_lt z h) hBD.n_lt
    · rw [Lax3Proofs.RamDriverDedup.dedupTarget_eq_zero h]
      have := hB.one_lt
      omega
  have hmem₂ : LevelMem B n cap mb σ₂ := levelMem_run hrunᵣ
    (levelMem_run hrun₁ hmem)
  have hdep₂ : DepthMem n cap mb σ₂ := (hdep.run hrun₁).run hrunᵣ
  have htsz₂ : TablesSized q_top cap mb φ n σ₂ := (htsz.run hrun₁).run hrunᵣ
  have hbarr₂ : BaseArrs B q_top cap mb ell φ σ₂ := (hbarr.run hrun₁).run hrunᵣ
  have hscratch₂ : StreamScratchFrom B n cap mb ell 0 σ₂ :=
    (streamScratchFrom_run_decodeComD hscratch hrun₁).congr hfaᵣ
  have hradix₂ : StreamRadixReady B n σ₂ :=
    ⟨hbits₂,
      lt_of_le_of_lt (clog_two_le_self n) hBD.n_lt,
      Nat.le_pow_clog (by omega) n⟩
  have hordmem₂ : OrderMem B n (dedupNs x) W σ₂ := by
    obtain ⟨hle, hlw, hsz, helm, hbh, hooff, hnoff, hstf, hsta,
      hstd, hste, hitg, hntg⟩ := hordmem₁
    refine ⟨hle, ?_, hsz.run hrunᵣ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [hfvᵣ "lw" (by decide) (by decide)]
    all_goals first | rwa [hfaᵣ] | exact run_mem_arrs_lt hrunᵣ _ hitg |
      exact run_mem_arrs_lt hrunᵣ _ hntg
  have hMpos : ∀ v < n, M v ≠ 0 := fun v hv => by
    rw [hMone v hv]
    omega
  have hMB : ∀ z < n, M z < B := fun z hz => by
    rw [hMone z hz]
    exact hB.one_lt
  have hGmB : ∀ z < n, Gm z < B := fun z hz => by
    rw [hGmone z hz]
    exact hB.one_lt
  have hcolempty : ∀ c < sigL cap mb 0,
      σ₂.arrs (colName 0 c) = arrOf n (fun _ => 0) := by
    intro c hc
    exact absurd hc (by rw [sigL_zero]; omega)
  have hcolbit : ∀ c < sigL cap mb 0, ∀ z < n,
      (fun _ _ => 0 : ℕ → ℕ → ℕ) c z ≤ 1 := by
    intro c hc
    exact absurd hc (by rw [sigL_zero]; omega)
  have hMG : masked G M = G :=
    Lax3Proofs.RamElim.masked_of_all_alive G hMpos
  have hGmG : masked G Gm = G :=
    Lax3Proofs.RamElim.masked_of_all_alive G
      (fun v hv => by rw [hGmone v hv]; omega)
  have hplay₀ : PlayRec B cap G 0 M Gm σ₂ := playRec_zero cap G hMG hGmG
  have hpadD' : ∀ z, dedupNs x ≤ z → z < W → dedupTarget x z = 0 :=
    fun z hz _ => Lax3Proofs.RamDriverDedup.dedupTarget_eq_zero hz
  have hmemcl₀ : ∃ Mem' mmj, σ₂.arrs (memName 0) = arrOf n Mem' ∧
      σ₂.vars (mnumName 0) = mmj ∧ MemEnum n mmj Mem' M ∧
        ∀ z < mmj, Mem' z < B := by
    refine ⟨Mem, n, (hfaᵣ _).trans hMem₁,
      (hfvᵣ _ (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff])).trans hMnum₁,
      ⟨fun k hk => by rw [hMemid k hk]; exact hk,
        fun i k hik hk => by
          rw [hMemid i (by omega), hMemid k hk]
          exact hik,
        fun k hk => by rw [hMemid k hk]; exact hMpos k hk,
        fun a ha _ => ⟨a, ha, hMemid a ha⟩⟩,
      fun z hz => by rw [hMemid z hz]; exact lt_trans hz hB.n_lt⟩
  obtain ⟨σ₃, hrun₃, ⟨⟨hpre₃, -, htab₃⟩, hout₃, hscratch₃⟩⟩ :=
    (hlev M Gm (fun _ _ => 0) hMpos
        (fun v hv => absurd hv (Set.notMem_empty v)) hcolbit).run
      (σ := σ₂)
      ⟨⟨by exact hn₂,
          (hfaᵣ _).trans hoff₁, (hfaᵣ _).trans htgt₁,
          (hfaᵣ _).trans hM₁, (hfaᵣ _).trans hGm₁,
          hcolempty, hMB, hGmB, hcolbit, hmem₂, hdep₂,
          by rw [hfvᵣ "m" (by decide) (by decide)]; exact hm₁,
          hordmem₂, hpadD', hTB, hmemcl₀⟩,
        htsz₂, hbarr₂, hplay₀,
        fun i hi => by
          obtain ⟨g, hg⟩ := htsz₂.get 0 hi
          exact ⟨g, hg, fun v hv => absurd hv (Set.notMem_empty v),
            fun v hv => absurd hv (Set.notMem_empty v)⟩,
        hscratch₂, hradix₂⟩
  obtain ⟨σ₄, hrun₄, hcond, hout₄⟩ :=
    (hsent M Gm (fun _ _ => 0) hBD hMpos).run (σ := σ₃)
      ⟨hpre₃, htab₃.tableInv (fun v => Or.inl (hMpos (v : ℕ) v.isLt)),
        by rw [hout₃, houtᵣ, hout₁]⟩
  refine ⟨σ₄, _, ?_, le_rfl, ?_⟩
  · simpa [driverRootStream, Nat.add_assoc] using
      hrun₁.seq (hrunᵣ.seq (hrun₃.seq hrun₄))
  · rw [hout₄]
    congr 1
    refine if_congr ?_ rfl rfl
    have hglue := sat_iff_eval_sentence (mb := mb) (cap := cap) hrank
      (masked G M) (colRead n (fun _ _ => 0) (sigL cap mb 0)) hcond
    exact hglue.symm.trans (by rw [hMG])

end Correct

section Concrete

variable {n : ℕ} {B q_top cap mb ns W ell s R d D₁ Kmass : ℕ}
  {N : ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
  {x : List ℕ} {Katom : ℕ → ℕ} {Katom₀ Kdec Ksent : ℕ}
  {Ki Ksc Ks Kl : ℕ → ℕ → ℕ}

open Classical in
/-- The concrete streamed root decides the encoded graph sentence.  All
four phases are executable terms; the remaining premises are the
nowhere-dense parameter bounds and scalar cost inequalities. -/
theorem driverRootStream_decides_sentence
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
    (hbnd : ∀ j < ell, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ sa ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        sa.r + 1 < B ∧ sa.t + n + mb < B ∧
          ∀ a z, a ≤ z → Lax3Proofs.Refine.ScatterDeadTurn.deadAtomKX
            sa.β n a mb z z sa.t ≤ Katom z)
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
    (hwidthB : n + Lax3Proofs.Refine.OrderActiveBudget.activeOrderWidth
      d D₁ R (n + ns) + 1 < B)
    (hwidthW : Lax3Proofs.Refine.OrderActiveBudget.activeOrderWidth
      d D₁ R (n + ns) ≤ W)
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
    (hKl : ∀ j < ell, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ k ∈ Finset.range t, bs k) ≤ Kmass * (m + 1) →
      Lax3Proofs.Refine.OrderActiveBudget.activeOrderCost d D₁ R m +
          (Lax3Proofs.Refine.CoverActiveInit.activeInitCost t +
            ((∑ k ∈ Finset.range t,
              (Lax3Proofs.Refine.CoverActiveStreamLifecycle.streamSearchSortCost
                  (Nat.clog 2 n) (bs k) (bs k) +
                Ks j (bs k) + 4)) + 6)) ≤ Kl j m)
    (hKdec : Lax3Proofs.RamDriverIO.decodeCost n ns +
      Lax3Proofs.RamDriverDedup.dedupCost n ns + 4 ≤ Kdec)
    (hatoms : ∀ sa ∈
      (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      sa.r + 1 < B ∧ sa.t < B ∧
        Lax3Proofs.RamDriverIO.atomCost n (dedupNs x) sa.t ≤ Katom₀)
    (hKsent : Katom₀ *
        (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (Lax3Proofs.RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent) :
    Spec B (StreamRootPreD B n ns W q_top cap mb ell φ x)
      (driverRootStream q_top cap mb R ell φ)
      (fun _ σ' => σ'.out =
        [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (radixWidthCost n +
        (Kl 0 (n + dedupNs x) + Ksent))) := by
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact Lax3Proofs.RamDriverDedup.dedupNs_le hx.vertexCount_eq
      hx.offset_zero hx.offset_last hx.offset_mono
  have hBD : WordBoundK B n 1 (dedupNs x) cap mb :=
    wordBoundK_anti hnsle hB
  have hnsleW' : dedupNs x ≤ W := le_trans hnsle hnsW
  have hwidthB' : n + Lax3Proofs.Refine.OrderActiveBudget.activeOrderWidth
      d D₁ R (n + dedupNs x) + 1 < B :=
    lt_of_le_of_lt (Nat.add_le_add_right
      (Nat.add_le_add_left
        (Lax3Proofs.Refine.OrderActiveBudget.activeOrderWidth_mono
          (Nat.add_le_add_left hnsle n)) n) 1) hwidthB
  have hwidthW' : Lax3Proofs.Refine.OrderActiveBudget.activeOrderWidth
      d D₁ R (n + dedupNs x) ≤ W :=
    le_trans (Lax3Proofs.Refine.OrderActiveBudget.activeOrderWidth_mono
      (Nat.add_le_add_left hnsle n)) hwidthW
  refine driverStream_correct hrank hB hKmass hxB hWB hnsW
    (decodeImplementsDL hx hns (by rw [decodeDLCost]; omega))
    (fun M Gm C hall => ?_)
    (fun M Gm C => Lax3Proofs.RamDriverIO.sentenceImplements hrank
      (Lax3Proofs.RamDriverDedup.csrGraph_dedup hx) hatoms hKsent)
  have h := streamLevelAtActive (ns := dedupNs x) (nt := W)
    (O := dedupOffset x) (T := dedupTarget x) hcap hmb hell hBD
    (Lax3Proofs.RamDriverDedup.csrSimple_dedup hx) hnsleW' hQ hbnd hcostI
    hKsc hKmono hKs hKbase hwidthB' hwidthW' hdeg hdens hKmass hdegree hKl
    0 (Nat.zero_le ell) M Gm C ∅
  rwa [Lax3Proofs.Refine.MassWeight.arenaWeight_root
    (Lax3Proofs.RamDriverDedup.csrSimple_dedup hx) hall] at h

end Concrete

end Lax3Proofs.Refine.CoverActiveStreamRoot
