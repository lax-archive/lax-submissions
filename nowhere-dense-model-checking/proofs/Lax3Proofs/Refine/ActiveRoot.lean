import Lax3Proofs.Refine.ActiveLevel
import Lax3Proofs.Refine.DriverRootD

/-!
# Active phases at the decoded root

This is the root composition for the compact active recursive driver.  It
uses the landed deduplicating decode, runs `driverAtA` with the concrete
active ordering and cover, and then reuses the landed sentence readback.
-/

namespace Lax3Proofs.Refine.ActiveRoot

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverMember
open Lax3Proofs.RamDriverDedup (dedupNs dedupOffset dedupTarget DedupMem)
open Lax3Proofs.Refine.ActiveLevel
open Lax3Proofs.Refine.DriverRootD
open Lax3Proofs.Refine.OrderActiveDriver
open Lax3Proofs.Refine.OrderActiveBudget
open Lax3Proofs.Refine.CoverActiveDriver
open Lax3Proofs.Refine.CoverActiveBudget
open Lax13Proofs.Imp Lax13Proofs.Reasoning

open Classical in
/-- Deduplicate the input CSR, run the compact active recursive driver, and
read back the sentence. -/
noncomputable def driverRootActive (q_top cap mb R ℓ : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : Com :=
  .seq decodeComD
    (.seq (driverAtA q_top cap mb ℓ φ
      (fun j => activeOrderPhase j R) (fun j => activeCoverPhase j cap) 0)
      (sentenceCom q_top cap mb φ))

section Correct

variable {n ns : ℕ} {B q_top cap mb R ℓ W Kd Kl Ks Kmass : ℕ}
  {G : SimpleGraph (Fin n)} {x : List ℕ} {φ : Lax3.FirstOrder.FO 0}

open Classical in
/-- Root composition from a domain-aware active level contract.  The proof
is the decoded-root composition, with the level program changed from the
carrier recursion to `driverAtA`. -/
theorem driverActive_correct (hrank : Lax3.FirstOrder.rank φ ≤ q_top)
    (hB : WordBoundK B n Kmass ns cap mb) (hxB : ∀ v ∈ x, v < B) (hWB : W < B)
    (hnsW : ns ≤ W)
    (hdec : DecodeImplementsDL B x G ns W Kd)
    (hlev : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ), (∀ v < n, M v ≠ 0) →
      LevelImplementsDA B q_top cap mb ℓ W (dedupNs x) 0 φ G
        (dedupOffset x) (dedupTarget x) M Gm C ∅
        (fun j => activeOrderPhase j R) (fun j => activeCoverPhase j cap) Kl)
    (hsent : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      SentenceImplements B q_top cap mb (dedupNs x) W φ G
        (dedupOffset x) (dedupTarget x) M Gm C Ks) :
    Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧
        DepthMem n cap mb σ ∧ OrderMem B n 0 W σ ∧ DedupMem n σ ∧
        TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
        σ.inp = x ∧ σ.out = [])
      (driverRootActive q_top cap mb R ℓ φ)
      (fun _ σ' => σ'.out =
        [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kd + (Kl + Ks)) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hdm, hmem, hdep, hord0, hdmem, htsz, hbarr, hinp, hout⟩ := hσ
  obtain ⟨σ₁, hrun₁, hout₁, hcsrD, hsimpD, hnsle, hpadD, hn₁, hoff₁, htgt₁, hm₁,
      hordmem₁, hdmem₁, ⟨M, hM₁, hMone⟩, ⟨Gm, hGm₁, hGmone⟩,
      ⟨Mem, hMem₁, hMemid, hMnum₁⟩⟩ :=
    (hdec hxB hB.succ_lt hB.ns_lt hWB hnsW).run
      ⟨hdm, hord0, hdmem, hinp, hout⟩
  have hBD : WordBoundK B n Kmass (dedupNs x) cap mb := wordBoundK_anti hnsle hB
  have hTB : ∀ z < W, dedupTarget x z < B := fun z hz => by
    rcases lt_or_ge z (dedupNs x) with h | h
    · exact lt_trans (hcsrD.target_lt z h) hBD.n_lt
    · rw [Lax3Proofs.RamDriverDedup.dedupTarget_eq_zero h]
      have := hB.one_lt
      omega
  have hmem₁ : LevelMem B n cap mb σ₁ := levelMem_run hrun₁ hmem
  have hdep₁ : DepthMem n cap mb σ₁ := hdep.run hrun₁
  have htsz₁ : TablesSized q_top cap mb φ n σ₁ := htsz.run hrun₁
  have hbarr₁ : BaseArrs B q_top cap mb ℓ φ σ₁ := hbarr.run hrun₁
  have hMpos : ∀ v < n, M v ≠ 0 := fun v hv => by rw [hMone v hv]; omega
  have hMB : ∀ z < n, M z < B := fun z hz => by rw [hMone z hz]; exact hB.one_lt
  have hGmB : ∀ z < n, Gm z < B := fun z hz => by rw [hGmone z hz]; exact hB.one_lt
  have hcolempty : ∀ c < sigL cap mb 0,
      σ₁.arrs (colName 0 c) = arrOf n (fun _ => 0) := by
    intro c hc
    exact absurd hc (by rw [sigL_zero]; omega)
  have hcolbit : ∀ c < sigL cap mb 0, ∀ z < n,
      (fun _ _ => 0 : ℕ → ℕ → ℕ) c z ≤ 1 := by
    intro c hc
    exact absurd hc (by rw [sigL_zero]; omega)
  have hMG : masked G M = G := Lax3Proofs.RamElim.masked_of_all_alive G hMpos
  have hGmG : masked G Gm = G :=
    Lax3Proofs.RamElim.masked_of_all_alive G
      (fun v hv => by rw [hGmone v hv]; omega)
  have hplay₀ : PlayRec B cap G 0 M Gm σ₁ := playRec_zero cap G hMG hGmG
  have hpadD' : ∀ z, dedupNs x ≤ z → z < W → dedupTarget x z = 0 :=
    fun z hz _ => Lax3Proofs.RamDriverDedup.dedupTarget_eq_zero hz
  have hmemcl₀ : ∃ Mem' mmj, σ₁.arrs (memName 0) = arrOf n Mem' ∧
      σ₁.vars (mnumName 0) = mmj ∧ MemEnum n mmj Mem' M ∧
        ∀ z < mmj, Mem' z < B := by
    refine ⟨Mem, n, hMem₁, hMnum₁, ⟨fun k hk => by rw [hMemid k hk]; exact hk,
      fun i k hik hk => by
        rw [hMemid i (by omega), hMemid k hk]
        exact hik,
      fun k hk => by rw [hMemid k hk]; exact hMpos k hk,
      fun a ha _ => ⟨a, ha, hMemid a ha⟩⟩, fun z hz => by
        rw [hMemid z hz]
        exact lt_trans hz hB.n_lt⟩
  obtain ⟨σ₂, hrun₂, ⟨hpre₂, -, htab₂⟩, hout₂⟩ :=
    (hlev M Gm (fun _ _ => 0) hMpos
        (fun v hv => absurd hv (Set.notMem_empty v)) hcolbit).run
      (σ := σ₁) ⟨⟨hn₁, hoff₁, htgt₁, hM₁, hGm₁, hcolempty, hMB, hGmB,
        hcolbit, hmem₁, hdep₁, hm₁, hordmem₁, hpadD', hTB, hmemcl₀⟩,
        htsz₁, hbarr₁, hplay₀,
        fun i hi => by
          obtain ⟨g, hg⟩ := htsz₁.get 0 hi
          exact ⟨g, hg, fun v hv => absurd hv (Set.notMem_empty v),
            fun v hv => absurd hv (Set.notMem_empty v)⟩⟩
  obtain ⟨σ₃, hrun₃, hcond, hout₃⟩ :=
    (hsent M Gm (fun _ _ => 0) hBD hMpos).run (σ := σ₂)
      ⟨hpre₂, htab₂.tableInv (fun v => Or.inl (hMpos (v : ℕ) v.isLt)),
        by rw [hout₂, hout₁]⟩
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono le_rfl, le_rfl, ?_⟩
  rw [hout₃]
  congr 1
  refine if_congr ?_ rfl rfl
  have hglue := sat_iff_eval_sentence (mb := mb) (cap := cap) hrank (masked G M)
    (colRead n (fun _ _ => 0) (sigL cap mb 0)) hcond
  exact hglue.symm.trans (by rw [hMG])

end Correct

section Main

variable {n : ℕ} {B q_top cap mb ns W ℓ s R d D₁ Kmass : ℕ}
  {N : ℕ → ℕ} {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
  {x : List ℕ} {Kb : ℕ → ℕ} {Kb₀ Kdec Ksent : ℕ}
  {Ki Ksc Ks Kl : ℕ → ℕ → ℕ}

open Classical in
/-- The concrete active root decides the input sentence.  Both carrier
phases and the recursive driver are executable terms; the remaining
hypotheses are the nowhere-dense graph bounds and scalar cost inequalities
that will be closed by the campaign's parameter layer. -/
theorem driverRootActive_decides_sentence
    (hx : EncodesGraph x n G) (hns : ns = 2 * edgeCount x)
    (hxB : ∀ v ∈ x, v < B)
    (hrank : Lax3.FirstOrder.rank φ ≤ q_top)
    (hcap : cap = rhoMinus 0 q_top)
    (hmb : mb = ℓ * (2 * cap + 1)) (hℓ : ℓ = N (2 * s + 2))
    (hB : WordBoundK B n Kmass ns cap mb) (hWB : W < B) (hnsW : ns ≤ W)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧
        2 * s + 2 ≤ Bd.ncard ∧ DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hbnd : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧ ∀ z,
          Lax3Proofs.Refine.ScatterDeadTurn.deadAtomKBlk
            σs.β z mb z z σs.t ≤ Kb z)
    (hcostI : ∀ j < ℓ, ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ z, Kb z * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki j z)
    (hKsc : ∀ j < ℓ, ∀ z,
      Ki j z * (tablesAt q_top cap mb φ j).length + 1 ≤ Ksc j z)
    (hKmono : ∀ j, Monotone (Kl j))
    (hKs : ∀ j < ℓ, ∀ t : ℕ,
      Lax3Proofs.RamDriverRoot.turnCostSize n (dedupNs x) cap mb q_top j φ
        (Ksc j t) t (Kl (j + 1) t) ≤ Ks j t)
    (hKbase : ∀ m, Lax3Proofs.RamDriverBot.baseCost q_top cap mb ℓ m φ ≤ Kl ℓ m)
    (hwidthB : n + activeOrderWidth d D₁ R (n + ns) + 1 < B)
    (hwidthW : activeOrderWidth d D₁ R (n + ns) ≤ W)
    (hdeg : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M)),
      Lax3Proofs.Augmentation.LowDegreeVertices
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) d)
    (hdens : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M))
        (D : ℕ → Lax3Proofs.Augmentation.Orientation mm) (i : ℕ), i ≤ R →
      Lax3Proofs.Augmentation.IsAugChain
        (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) D i →
      (∀ l < i, Lax3Proofs.Augmentation.GreedyFratRound (D l) (D (l + 1))) →
      Lax3Proofs.Augmentation.AugmentedDepthOneDensity D i D₁)
    (hKmass : 1 ≤ Kmass)
    (hdegree : ∀ (M : ℕ → ℕ) {mm : ℕ} {Mem : ℕ → ℕ}
        (hml : Lax3Proofs.Refine.ScatterBlock.MemList n mm Mem
          (Lax3Proofs.RamDriverCluster.markSet n M))
        {D : ℕ → Lax3Proofs.Augmentation.Orientation mm}
        {d₀ k : ℕ} {pi : Equiv.Perm (Fin mm)},
      Lax3Proofs.CoverDegree.AugChainData
          (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) D pi R d₀ k →
        ∀ v : Fin mm,
          (Lax12.ColoringNumbers.wreach
            (Lax3Proofs.Refine.ElimCompact.memGraph G M hml) pi (2 * cap) v).ncard ≤ Kmass)
    (hKl : ∀ j < ℓ, ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      activeOrderCost d D₁ R m +
          (activeCoverCost n Kmass m +
            ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6)) ≤ Kl j m)
    (hKdec : Lax3Proofs.RamDriverIO.decodeCost n ns +
      Lax3Proofs.RamDriverDedup.dedupCost n ns + 4 ≤ Kdec)
    (hatoms : ∀ sa ∈
      (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2,
      sa.r + 1 < B ∧ sa.t < B ∧
        Lax3Proofs.RamDriverIO.atomCost n (dedupNs x) sa.t ≤ Kb₀)
    (hKsent : Kb₀ *
        (bcAtomsOf₀ q_top (Reduction.toDistFO (L := sigL cap mb 0) φ)).2.length + 1 +
      (1 + (Lax3Proofs.RamDriverIO.sentenceExpr q_top cap mb φ).size) ≤ Ksent) :
    Spec B (fun σ => DecodeMem n ns W σ ∧ LevelMem B n cap mb σ ∧
        DepthMem n cap mb σ ∧ OrderMem B n 0 W σ ∧ DedupMem n σ ∧
        TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
        σ.inp = x ∧ σ.out = [])
      (driverRootActive q_top cap mb R ℓ φ)
      (fun _ σ' => σ'.out =
        [if Lax3.FirstOrder.Sat G Fin.elim0 φ then 1 else 0])
      (Kdec + (Kl 0 (n + dedupNs x) + Ksent)) := by
  have hnsle : dedupNs x ≤ ns := by
    rw [hns]
    exact Lax3Proofs.RamDriverDedup.dedupNs_le hx.vertexCount_eq hx.offset_zero
      hx.offset_last hx.offset_mono
  have hBD : WordBoundK B n Kmass (dedupNs x) cap mb := wordBoundK_anti hnsle hB
  have hwidthB' : n + activeOrderWidth d D₁ R (n + dedupNs x) + 1 < B :=
    lt_of_le_of_lt (Nat.add_lt_add_right
      (Nat.add_le_add_left (activeOrderWidth_mono
        (Nat.add_le_add_left hnsle n)) n) 1) hwidthB
  have hwidthW' : activeOrderWidth d D₁ R (n + dedupNs x) ≤ W :=
    le_trans (activeOrderWidth_mono (Nat.add_le_add_left hnsle n)) hwidthW
  refine driverActive_correct hrank hB hxB hWB hnsW
    (decodeImplementsDL hx hns (by rw [decodeDLCost]; omega))
    (fun M Gm C hall => ?_)
    (fun M Gm C => Lax3Proofs.RamDriverIO.sentenceImplements hrank
      (Lax3Proofs.RamDriverDedup.csrGraph_dedup hx) hatoms hKsent)
  have h := levelAtActive (ns := dedupNs x) (O := dedupOffset x)
    (T := dedupTarget x) hcap hmb hℓ hBD
    (Lax3Proofs.RamDriverDedup.csrSimple_dedup hx) hQ hbnd hcostI hKsc
    hKmono hKs hKbase hwidthB' hwidthW' hdeg hdens hKmass hdegree hKl
    0 (Nat.zero_le ℓ) M Gm C ∅
  rwa [Lax3Proofs.Refine.MassWeight.arenaWeight_root
    (Lax3Proofs.RamDriverDedup.csrSimple_dedup hx) hall] at h

end Main

/-! ## Axiom audit -/

#print axioms driverActive_correct
#print axioms driverRootActive_decides_sentence

end Lax3Proofs.Refine.ActiveRoot
