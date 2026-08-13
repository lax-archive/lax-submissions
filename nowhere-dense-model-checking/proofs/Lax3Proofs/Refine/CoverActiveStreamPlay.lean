import Lax3Proofs.Refine.CoverActiveStreamChildEnum
import Lax3Proofs.Refine.CoverActiveBudget

/-!
# Executable descent from one streamed cover row

This module joins the row-local streamed leaves at the first point where they
form a genuine recursive descent.  The level arena is the ambient mask `A₀`
stored at `alvName j`; the progressively depleted cover-search mask stored at
raw `"alv"` is only framed.  The command installs the row connector, loads
the row, builds its retained cache, marks the cached batch, and constructs the
child masks and exact member list.  Its postcondition constructs the successor
`PlayRec`; it does not assume one.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamPlay

open Finset
open Lax3.ColoredGraphs
open Lax11.GraphEncoding
open Lax3Proofs.RamBfs (CsrGraph WD masked)
open Lax3Proofs.RamCover
open Lax3Proofs.RamCoverActive
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.CoverActiveStreamLoad
open Lax3Proofs.Refine.CoverActiveStreamMask
open Lax3Proofs.Refine.CoverActiveStreamBatch
open Lax3Proofs.Refine.CoverActiveStreamChild
open Lax3Proofs.Refine.CoverActiveBudget
open Lax3Proofs.Refine.MassMath (clusterAt)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Program, charge, and exported state -/

/-- Install the connector named by the current streamed row. -/
def streamConnectorCom (j : ℕ) : Com :=
  .assign (ctrName j) (.get "ord" (.var "c"))

/-- Restore the resident-row length after the retained parent search.  The
loader has already copied this length to `bq`, and both the cache and batch
passes frame that count, whereas the BFS cache legitimately uses `tail` as a
queue counter. -/
def streamRestoreTailCom : Com :=
  .assign "tail" (.var "bq")

/-- One complete row-local descent, stopping immediately before enumeration. -/
def streamPlayCom (cap j : ℕ) : Com :=
  .seq (streamConnectorCom j)
    (.seq (streamClusterLoadCom "xmem" j)
      (.seq (streamRetainCom j)
        (.seq (cacheRoundCom cap j)
          (.seq (streamBatchCachedCom cap j)
            (.seq streamRestoreTailCom (streamChildFilterCom j))))))

/-- Exact compositional charge.  `bw` pays both the row and vertex support of
the retained parent search; later it is instantiated by `activeBallWeight`. -/
def streamPlayCost (tail bw cap j : ℕ) : ℕ :=
  3 + streamClusterLoadCost tail + streamBlockAndCost tail +
    cacheRoundCost tail bw bw + streamBatchCachedCost cap j +
      2 + streamChildFilterCost tail

/-- The exact input expected by `streamChildEnumStep`, produced by executable
descent rather than by an assumed successor record. -/
structure StreamPlayOut {n : ℕ} (B ns nt na q cap mb j c tail bits : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem : ℕ → ℕ)
    (mm : ℕ) (σ : Env) : Prop where
  child : StreamChildOut B ns nt na q cap j c tail bits G A₀ π centre O T
    Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem mm σ
  play : PlayRec B cap G (j + 1) Alv Gam σ
  batch_nonempty : (markSet n Wa ∩ markSet n Xa).Nonempty
  batch_card : (markSet n Wa).ncard ≤ mb
  wa_alloc : ∃ g, σ.arrs "wa" = arrOf mb g

/-! ## Small write-set facts -/

theorem streamBatch_frame_arr {cap j : ℕ} {a : String}
    (ha : a ≠ batName j) : a ∉ (streamBatchCachedCom cap j).warrs := by
  intro h
  simp only [streamBatchCachedCom, Com.warrs, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · exact ha h
  · obtain ⟨b, -, hb⟩ := RamDriverFrames.mem_warrs_foldRange _ _ h
    rw [warrs_streamMarkParentsCom] at hb
    exact ha (List.eq_of_mem_singleton hb)

theorem streamBatch_wvars {cap j : ℕ} {y : String}
    (h : y ∈ (streamBatchCachedCom cap j).wvars) : y ∈ descendScalars := by
  simp only [streamBatchCachedCom, Com.wvars, List.mem_append,
    List.not_mem_nil] at h
  rcases h with h | h
  · exact False.elim h
  obtain ⟨a, -, ha⟩ := Lax3Proofs.RamDriverDescend.mem_wvars_foldRange _ _ h
  exact mem_wvars_streamMarkParentsCom ha

theorem streamBatch_frame_var {cap j : ℕ} {y : String}
    (hpc : y ≠ "pc") (hplen : y ≠ "plen") (hpi : y ≠ "pi") :
    y ∉ (streamBatchCachedCom cap j).wvars := by
  intro h
  simp only [streamBatchCachedCom, Com.wvars, List.mem_append,
    List.not_mem_nil] at h
  rcases h with h | h
  · exact False.elim h
  obtain ⟨a, -, ha⟩ := Lax3Proofs.RamDriverDescend.mem_wvars_foldRange _ _ h
  simp [streamMarkParentsCom, streamMarkParentStep, Com.wvars,
    hpc, hplen, hpi] at ha

/-! ## Exact executable composition -/

/-- **A streamed row constructs the next recorded game position.**

The cache support is the natural-number presentation of the ambient cluster,
so both of its budgets are paid by one `activeBallWeight`.  The command never
scans the carrier, reads a cover offset, or uses the progressive scratch mask
as the recursive arena. -/
theorem streamPlayStep
    {B n ns nt na q cap mb ell j c tail bits d : ℕ}
    {G : SimpleGraph (Fin n)}
    {A₀ O T centre Xmem asg M Gm : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)}
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : CsrGraph G ns O T) (hnt : ns ≤ nt)
    (hB : WordBoundK B n d ns cap mb)
    (hmb : mb = ell * (2 * cap + 1)) (hjl : j < ell)
    (hA₀B : ∀ z, z < n → A₀ z < B)
    (hGmB : ∀ z, z < n → Gm z < B) :
    Spec B
      (fun σ =>
        StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
            Xmem asg M σ ∧
        PlayRec B cap G j A₀ Gm σ ∧
        σ.arrs (alvName j) = arrOf n A₀ ∧
        σ.arrs (gamName j) = arrOf n Gm ∧
        σ.arrs (cluName j) = arrOf n (fun _ => 0) ∧
        σ.arrs (resName j) = arrOf n (fun _ => 0) ∧
        σ.arrs (batName j) = arrOf n (fun _ => 0) ∧
        σ.arrs (alvName (j + 1)) = arrOf n (fun _ => 0) ∧
        σ.arrs (gamName (j + 1)) = arrOf n (fun _ => 0) ∧
        (∃ g, σ.arrs (memName (j + 1)) = arrOf n g) ∧
        (∃ g, σ.arrs (pdsName j) = arrOf n g) ∧
        (∃ g, σ.arrs (parName j) = arrOf n g) ∧
        (∃ g, σ.arrs "par" = arrOf n g) ∧
        (∃ g, σ.arrs "path" = arrOf (2 * cap + 1) g) ∧
        ∃ g, σ.arrs "wa" = arrOf mb g)
      (streamPlayCom cap j)
      (fun _ σ' => ∃ Xa Mm Ra Wa Alv Gam Mem mm,
        StreamPlayOut B ns nt na q cap mb j c tail bits G A₀ π centre O T
          Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem mm σ')
      (streamPlayCost tail
        (activeBallWeight n G A₀ π centre O cap c) cap j) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hsorted, hplay, hambient, hgam, hclu₀, hres₀, hbat₀,
    halv₀, hgam₀, hmem₀, hpds₀, hparj₀, hpar₀, hpath₀, hwa₀⟩ := hσ
  have hcq : c < q := by
    have := hsorted.row.state.pos_le
    omega
  have hcN : c < n := lt_of_lt_of_le hcq hcentres.count_le
  have hvN : centre c < n := hcentres.centre_lt c hcq
  let v : Fin n := ⟨centre c, hvN⟩
  have hA₀v : A₀ (v : ℕ) ≠ 0 := by
    change A₀ (centre c) ≠ 0
    exact hcentres.alive c hcq
  have hec : (Expr.get "ord" (.var "c")).evalB B σ = some (centre c) := by
    apply evalB_get
    · apply evalB_var
      rw [hsorted.centre_var]
      exact lt_trans hcN hB.n_lt
    · rw [hsorted.centre_arr, hsorted.centre_var, getElem?_arrOf centre hcN]
    · exact lt_trans hvN hB.n_lt
  let σ₁ := σ.setVar (ctrName j) (centre c)
  have hr₁ : Run B (streamConnectorCom j) σ σ₁ 3 := by
    exact (Run.assign hec).mono (by simp [Expr.size])
  have harr₁ : ∀ a : String, σ₁.arrs a = σ.arrs a := by
    intro a
    simp [σ₁]
  have hvar₁ : ∀ y : String, y ≠ ctrName j → σ₁.vars y = σ.vars y := by
    intro y hy
    simp [σ₁, hy]
  have hctr₁ : σ₁.vars (ctrName j) = (v : ℕ) := by
    simp [σ₁, v]
  have hsorted₁ :
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
        Xmem asg M σ₁ := by
    refine ⟨hsorted.row,
      by simpa [σ₁] using hsorted.n_var,
      by simpa [σ₁] using hsorted.q_var,
      by simpa [σ₁] using hsorted.centre_var,
      by simpa [σ₁] using hsorted.pointer_var,
      by simpa [σ₁] using hsorted.tail_var,
      by simpa [σ₁] using hsorted.bits_var,
      by simpa [σ₁] using hsorted.centre_arr,
      by simpa [σ₁] using hsorted.off_arr,
      by simpa [σ₁] using hsorted.target_arr,
      by simpa [σ₁] using hsorted.mask_arr,
      by simpa [σ₁] using hsorted.row_arr,
      hsorted.row_fit,
      by simpa [σ₁] using hsorted.asg_arr,
      by simpa [σ₁] using hsorted.dist_clean,
      ?_, ?_, hsorted.mask_bound⟩
    · obtain ⟨Q, hQ⟩ := hsorted.queue_arr
      exact ⟨Q, by simpa [σ₁] using hQ⟩
    · obtain ⟨QD, hQD⟩ := hsorted.qdist_arr
      exact ⟨QD, by simpa [σ₁] using hQD⟩
  obtain ⟨σ₂, hr₂, ⟨Xa, Mm, hload₂⟩, hfv₂, hfa₂, -, -⟩ :=
    ((streamClusterLoadStep (j := j) hB.one_lt hB.n_lt hA₀B).frame).run
      (σ := σ₁) ⟨hsorted₁, by simpa [σ₁] using hambient,
        by simpa [σ₁] using hclu₀, by simpa [σ₁] using hmem₀⟩
  obtain ⟨σ₃, hr₃, ⟨Ra, hret₃⟩, hfv₃, hfa₃, -, -⟩ :=
    ((streamRetainStep (j := j) hB.one_lt hB.n_lt).frame).run
      (σ := σ₂) ⟨hload₂, by
        rw [hfa₂ (resName j) (by
          simp [streamClusterLoadCom, streamLoadSlot, Com.warrs,
            resName, cluName, memName, String.ext_iff]), harr₁]
        exact hres₀⟩
  have hvX : v ∈ markSet n Xa := by
    rw [hret₃.loaded.cluster_set]
    change InCluster (masked G A₀) π cap (centre c) (centre c)
    exact ⟨hvN, hvN, self_mem_wreach (masked G A₀) π (2 * cap) v⟩
  have hXv : Xa (v : ℕ) ≠ 0 := hvX
  have hRv : Ra (v : ℕ) ≠ 0 := by
    rw [hret₃.retained_val (v : ℕ) v.isLt]
    exact Nat.mul_ne_zero hA₀v hXv
  have hRaX : ∀ z, z < n → Ra z ≠ 0 → Xa z ≠ 0 := by
    intro z hz hR hX
    rw [hret₃.retained_val z hz, hX, Nat.mul_zero] at hR
    exact hR rfl
  have hRaA : ∀ z, z < n → Ra z ≠ 0 → A₀ z ≠ 0 := by
    intro z hz hR hA
    rw [hret₃.retained_val z hz, hA, Nat.zero_mul] at hR
    exact hR rfl
  have hRcov : ∀ z, z < n → Ra z ≠ 0 → WD G Ra (2 * cap) (v : ℕ) z := by
    intro z hz hR
    have hzcl : InCluster (masked G A₀) π cap (centre c) z := by
      have hzX : (⟨z, hz⟩ : Fin n) ∈ markSet n Xa := hRaX z hz hR
      rw [hret₃.loaded.cluster_set] at hzX
      exact hzX
    obtain ⟨p, hp, hps⟩ :=
      exists_walk_support_inCluster (A := masked G A₀) (π := π) hvN hz hzcl
    have hpR : ∀ y ∈ p.support, Ra (y : ℕ) ≠ 0 := by
      intro y hy
      have hycl : y ∈ clusterAt G A₀ π centre cap c := hps y hy
      have hyA : A₀ (y : ℕ) ≠ 0 :=
        Lax3Proofs.Refine.MassAlive.clusterAt_subset_alive hA₀v hycl
      have hyX : Xa (y : ℕ) ≠ 0 := by
        change (y : Fin n) ∈ markSet n Xa
        rw [hret₃.loaded.cluster_set]
        exact hycl
      rw [hret₃.retained_val _ y.isLt]
      exact Nat.mul_ne_zero hyA hyX
    obtain ⟨p', hp'⟩ := walk_masked_of_support p hpR
    exact ⟨v.isLt, hz, p', by rw [hp']; exact hp⟩
  let A : Finset ℕ := activeClusterNat G A₀ π centre cap c
  let bw := activeBallWeight n G A₀ π centre O cap c
  have hA : ∀ z, z < n → Ra z ≠ 0 → WD G Ra (2 * cap) (v : ℕ) z → z ∈ A := by
    intro z hz hR _
    apply Finset.mem_image.mpr
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    apply mem_activeClusterFin.mpr
    rw [← hret₃.loaded.cluster_set]
    exact hRaX z hz hR
  have hbw : (∑ z ∈ A, Csr.rowLen O z) ≤ bw := by
    exact activeClusterNat_rows_le_weight (n := n) (G := G) (A₀ := A₀)
      (π := π) (centre := centre) (O := O) (r := cap) c
  have hnb : A.card ≤ bw := by
    exact activeClusterNat_card_le_weight (n := n) (G := G) (A₀ := A₀)
      (π := π) (centre := centre) (O := O) (r := cap) c
  obtain ⟨rounds, hrec, hle, hplayR, hcached⟩ := hplay
  have hex : ∀ a : ℕ, ∃ (u : Fin n) (Ga : ℕ → ℕ), a < j →
      σ.vars (ctrName a) = (u : ℕ) ∧ σ.arrs (gamName a) = arrOf n Ga ∧
        ∀ z, z < n → Ga z < B := by
    intro a
    by_cases ha : a < j
    · obtain ⟨u, Ga, hctr, hga, hgaB⟩ := hrec.get a ha
      exact ⟨u, Ga, fun _ => ⟨hctr, hga, hgaB⟩⟩
    · exact ⟨v, fun _ => 0, fun hcon => absurd hcon ha⟩
  choose U Games hUG using hex
  have hav₂ : ∀ a : String, a ≠ cluName j → a ≠ memName (j + 1) →
      σ₂.arrs a = σ₁.arrs a := by
    intro a hclu hmem
    exact hfa₂ a (by
      simp [streamClusterLoadCom, streamLoadSlot, Com.warrs, hclu, hmem])
  have hvv₂ : ∀ y : String, y ≠ "p" → y ≠ "bq" →
      σ₂.vars y = σ₁.vars y := by
    intro y hp hbq
    exact hfv₂ y (by
      simp [streamClusterLoadCom, streamLoadSlot, Com.wvars, hp, hbq])
  have hav₃ : ∀ a : String, a ≠ resName j → σ₃.arrs a = σ₂.arrs a := by
    intro a hres
    exact hfa₃ a (by
      simp [streamRetainCom, streamBlockAndCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.warrs, hres])
  have hvv₃ : ∀ y : String, y ≠ "p" → y ≠ "pend" → y ≠ "cw" →
      σ₃.vars y = σ₂.vars y := by
    intro y hp hpend hcw
    exact hfv₃ y (by
      simp [streamRetainCom, streamBlockAndCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.wvars, hp, hpend, hcw])
  have hctr₃ : σ₃.vars (ctrName j) = (v : ℕ) := by
    rw [hvv₃ _ (by simp [ctrName, String.ext_iff])
      (by simp [ctrName, String.ext_iff])
      (by simp [ctrName, String.ext_iff]),
      hvv₂ _ (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff])]
    exact hctr₁
  have hcached₃ : CachedRounds cap G j A₀ σ₃ := by
    refine hcached.congr ?_ ?_ ?_ ?_
    · intro a ha
      rw [hvv₃ _ (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff]),
        hvv₂ _ (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff]),
        hvar₁ _ (ctrName_ne (by omega))]
    · intro a ha
      have hne : resName a ≠ resName j := by
        intro he
        have : a = j := prefixed_inj (p := "res") (by simpa only [resName] using he)
        omega
      rw [hav₃ _ hne,
        hav₂ _ (by simp [resName, cluName, String.ext_iff])
          (by simp [resName, memName, String.ext_iff]), harr₁]
    · intro a ha
      rw [hav₃ _ (by simp [gamName, resName, String.ext_iff]),
        hav₂ _ (by simp [gamName, cluName, String.ext_iff])
          (by simp [gamName, memName, String.ext_iff]), harr₁]
    · intro a ha
      rw [hav₃ _ (by simp [parName, balName, resName, String.ext_iff]),
        hav₂ _ (by simp [parName, balName, cluName, String.ext_iff])
          (by simp [parName, balName, memName, String.ext_iff]), harr₁]
  obtain ⟨σ₄, hr₄, ⟨-, D, P, hpar₄, htree₄⟩, hfv₄, hfa₄, -, -⟩ :=
    ((cacheRoundCom_specW (j := j) (G := G) (O := O) (T := T)
      (R := Ra) (X := Xa) (Mem := Mm) hcsr hnt hB v.isLt hRv
      hret₃.loaded.member_enum hRaX hret₃.retained_bound (A := A) hA hbw hnb).frame).run
      (σ := σ₃)
      ⟨hret₃.loaded.sorted.n_var, hctr₃, hret₃.loaded.member_count,
        hret₃.loaded.member_arr, hret₃.loaded.sorted.off_arr,
        hret₃.loaded.sorted.target_arr, hret₃.retained_arr,
        exists_arrOf_run (hr₁.seq (hr₂.seq hr₃)) hpds₀,
        hret₃.loaded.sorted.queue_arr, hret₃.loaded.sorted.qdist_arr,
        exists_arrOf_run (hr₁.seq (hr₂.seq hr₃)) hparj₀⟩
  have hav₄ : ∀ a : String, a ≠ balAltName j → a ≠ balName j →
      a ≠ "q" → a ≠ "qd" → σ₄.arrs a = σ₃.arrs a := by
    intro a hba hbl hq hqd
    exact hfa₄ a (fun hc => by
      rcases mem_warrs_cacheRoundCom hc with h | h | h | h
      · exact hba h
      · exact hbl h
      · exact hq h
      · exact hqd h)
  have hvv₄ : ∀ y : String, y ≠ mnumName (j + 1) → y ∉ descendScalars →
      σ₄.vars y = σ₃.vars y := by
    intro y hmm hs
    exact hfv₄ y (fun hc => by
      rcases mem_wvars_cacheRoundCom hc with h | h
      · exact hmm h
      · exact hs h)
  have hcached₄ : CachedRounds cap G j A₀ σ₄ :=
    cachedRounds_cacheRound_run hcached₃ hr₄
  have henv₄ : BatchEnv cap nt j O T U Games v σ₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hvv₄ "n" (by simp [mnumName, String.ext_iff]) (by decide)]
      exact hret₃.loaded.sorted.n_var
    · rw [hav₄ "off" (by simp [balAltName, String.ext_iff])
        (by simp [balName, String.ext_iff]) (by decide) (by decide)]
      exact hret₃.loaded.sorted.off_arr
    · rw [hav₄ "tgt" (by simp [balAltName, String.ext_iff])
        (by simp [balName, String.ext_iff]) (by decide) (by decide)]
      exact hret₃.loaded.sorted.target_arr
    · exact ⟨M, (hav₄ "alv" (by simp [balAltName, String.ext_iff])
        (by simp [balName, String.ext_iff]) (by decide) (by decide)).trans
          hret₃.loaded.sorted.mask_arr⟩
    · obtain ⟨D₀, hD₀, -⟩ := hret₃.loaded.sorted.dist_clean
      exact exists_arrOf_run hr₄ ⟨D₀, hD₀⟩
    · exact exists_arrOf_run hr₄ hret₃.loaded.sorted.queue_arr
    · exact exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) hpar₀
    · exact exists_arrOf_run (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) hpath₀
    · rw [hvv₄ _ (by simp [ctrName, mnumName, String.ext_iff])
        (ctrName_notMem_descendScalars j)]
      exact hctr₃
    · intro a ha
      rw [hvv₄ _ (by simp [ctrName, mnumName, String.ext_iff])
          (ctrName_notMem_descendScalars a),
        hvv₃ _ (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff]),
        hvv₂ _ (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff]),
        hvar₁ _ (ctrName_ne (by omega))]
      exact (hUG a ha).1
    · intro a ha
      rw [hav₄ _ (by simp [gamName, balAltName, String.ext_iff])
          (by simp [gamName, balName, String.ext_iff])
          (by simp [gamName, String.ext_iff])
          (by simp [gamName, String.ext_iff]),
        hav₃ _ (by simp [gamName, resName, String.ext_iff]),
        hav₂ _ (by simp [gamName, cluName, String.ext_iff])
          (by simp [gamName, memName, String.ext_iff]), harr₁]
      exact (hUG a ha).2.1
  have hclu₄ : σ₄.arrs (cluName j) = arrOf n Xa := by
    rw [hav₄ _ (by simp [cluName, balAltName, String.ext_iff])
      (by simp [cluName, balName, String.ext_iff])
      (by simp [cluName, String.ext_iff])
      (by simp [cluName, String.ext_iff])]
    exact hret₃.loaded.cluster_arr
  have hbat₄ : σ₄.arrs (batName j) = arrOf n (fun _ => 0) := by
    rw [hav₄ _ (by simp [batName, balAltName, String.ext_iff])
        (by simp [batName, balName, String.ext_iff])
        (by simp [batName, String.ext_iff])
        (by simp [batName, String.ext_iff]),
      hav₃ _ (by simp [batName, resName, String.ext_iff]),
      hav₂ _ (by simp [batName, cluName, String.ext_iff])
        (by simp [batName, memName, String.ext_iff]), harr₁]
    exact hbat₀
  obtain ⟨σ₅, hr₅,
      ⟨henv₅, hcached₅, hclu₅, Wa, hbat₅, hWaB, hWsub, hvW,
        hWcard, hWwalk, hWaSup⟩, hfv₅, hfa₅, -, -⟩ :=
    ((streamBatchCachedCom_spec (G := G) hB (U := U) (Gam := Games)
      (M := A₀) (Xa := Xa) (Xmem := Xmem) (v := v) hA₀v
      hret₃.loaded.cluster_bit hXv
      (Lax3Proofs.Refine.CoverActiveStreamMask.StreamLoadOut.cluster_supported
        hret₃.loaded)).frame).run
      (σ := σ₄) ⟨henv₄, hcached₄, hclu₄, hbat₄⟩
  have hav₅ : ∀ a : String, a ≠ batName j → σ₅.arrs a = σ₄.arrs a := by
    intro a ha
    exact hfa₅ a (streamBatch_frame_arr ha)
  have hvv₅ : ∀ y : String, y ∉ descendScalars → σ₅.vars y = σ₄.vars y := by
    intro y hy
    exact hfv₅ y (fun hc => hy (streamBatch_wvars hc))
  have hbq₅ : σ₅.vars "bq" = tail := by
    rw [hfv₅ "bq" (streamBatch_frame_var (by decide) (by decide) (by decide)),
      hfv₄ "bq" (bq_notMem_wvars_cacheRoundCom cap j)]
    exact hret₃.loaded.member_count
  have htailB : tail < B := lt_of_le_of_lt hsorted.row.tail_le hB.n_lt
  have ebq₅ : (Expr.var "bq").evalB B σ₅ = some tail := by
    have h := evalB_var (B := B) (x := "bq") (σ := σ₅) (by rw [hbq₅]; exact htailB)
    rwa [hbq₅] at h
  let σ₅t := σ₅.setVar "tail" tail
  have hr₅t : Run B streamRestoreTailCom σ₅ σ₅t 2 := by
    exact (Run.assign ebq₅).mono (by simp [Expr.size])
  have harr₅t : ∀ a : String, σ₅t.arrs a = σ₅.arrs a := by
    intro a
    simp [σ₅t]
  have hvar₅t : ∀ y : String, y ≠ "tail" → σ₅t.vars y = σ₅.vars y := by
    intro y hy
    simp [σ₅t, hy]
  have hsorted₅ :
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
        Xmem asg M σ₅t := by
    refine ⟨hret₃.loaded.sorted.row,
      (hvar₅t "n" (by decide)).trans ((hvv₅ "n" (by decide)).trans
        ((hvv₄ "n" (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret₃.loaded.sorted.n_var)),
      (hvar₅t "qn" (by decide)).trans ((hvv₅ "qn" (by decide)).trans
        ((hvv₄ "qn" (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret₃.loaded.sorted.q_var)),
      (hvar₅t "c" (by decide)).trans ((hvv₅ "c" (by decide)).trans
        ((hvv₄ "c" (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret₃.loaded.sorted.centre_var)),
      (hvar₅t "xp" (by decide)).trans ((hvv₅ "xp" (by decide)).trans
        ((hvv₄ "xp" (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret₃.loaded.sorted.pointer_var)),
      by simp [σ₅t],
      (hvar₅t "rsbits" (by decide)).trans ((hvv₅ "rsbits" (by decide)).trans
        ((hvv₄ "rsbits" (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret₃.loaded.sorted.bits_var)),
      (harr₅t "ord").trans ((hav₅ "ord" (by simp [batName, String.ext_iff])).trans
        ((hav₄ "ord" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide)).trans
          hret₃.loaded.sorted.centre_arr)),
      (harr₅t "off").trans ((hav₅ "off" (by simp [batName, String.ext_iff])).trans
        ((hav₄ "off" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide)).trans
          hret₃.loaded.sorted.off_arr)),
      (harr₅t "tgt").trans ((hav₅ "tgt" (by simp [batName, String.ext_iff])).trans
        ((hav₄ "tgt" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide)).trans
          hret₃.loaded.sorted.target_arr)),
      (harr₅t "alv").trans ((hav₅ "alv" (by simp [batName, String.ext_iff])).trans
        ((hav₄ "alv" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide)).trans
          hret₃.loaded.sorted.mask_arr)),
      (harr₅t "xmem").trans ((hav₅ "xmem" (by simp [batName, String.ext_iff])).trans
        ((hav₄ "xmem" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide)).trans
          hret₃.loaded.sorted.row_arr)),
      hret₃.loaded.sorted.row_fit,
      (harr₅t "asg").trans ((hav₅ "asg" (by simp [batName, String.ext_iff])).trans
        ((hav₄ "asg" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide)).trans
          hret₃.loaded.sorted.asg_arr)),
      ?_,
      exists_arrOf_run (hr₄.seq (hr₅.seq hr₅t)) hret₃.loaded.sorted.queue_arr,
      exists_arrOf_run (hr₄.seq (hr₅.seq hr₅t)) hret₃.loaded.sorted.qdist_arr,
      hret₃.loaded.sorted.mask_bound⟩
    apply Lax3Proofs.Refine.CoverActiveTurn.distClean_of_arrs_eq
      hret₃.loaded.sorted.dist_clean
    exact (harr₅t "dist").trans
      ((hav₅ "dist" (by simp [batName, String.ext_iff])).trans
        (hav₄ "dist" (by simp [balAltName, String.ext_iff])
          (by simp [balName, String.ext_iff]) (by decide) (by decide)))
  have hload₅ :
      StreamLoadOut B ns nt na q cap j c tail bits G A₀ π centre O T
        Xmem asg M Xa Mm σ₅t := by
    refine ⟨hsorted₅, ?_, hret₃.loaded.ambient_bound, hclu₅,
      hret₃.loaded.cluster_bit, hret₃.loaded.cluster_set, ?_, ?_,
      hret₃.loaded.member_enum⟩
    · exact (harr₅t (alvName j)).trans ((hav₅ (alvName j) (by
          simp [alvName, batName, String.ext_iff])).trans
        ((hav₄ (alvName j) (by simp [alvName, balAltName, String.ext_iff])
          (by simp [alvName, balName, String.ext_iff])
          (by simp [alvName, String.ext_iff])
          (by simp [alvName, String.ext_iff])).trans hret₃.loaded.ambient_arr))
    · exact (harr₅t (memName (j + 1))).trans ((hav₅ (memName (j + 1)) (by
          simp [memName, batName, String.ext_iff])).trans
        ((hav₄ (memName (j + 1))
          (by simp [memName, balAltName, String.ext_iff])
          (by simp [memName, balName, String.ext_iff])
          (by simp [memName, String.ext_iff])
          (by simp [memName, String.ext_iff])).trans hret₃.loaded.member_arr))
    · exact (hvar₅t "bq" (by decide)).trans hbq₅
  have hret₅ :
      StreamRetainOut B ns nt na q cap j c tail bits G A₀ π centre O T
        Xmem asg M Xa Mm Ra σ₅t := by
    refine ⟨hload₅, ?_, hret₃.retained_val, hret₃.retained_bound,
      hret₃.retained_supported⟩
    exact (harr₅t (resName j)).trans ((hav₅ (resName j) (by
        simp [resName, batName, String.ext_iff])).trans
      ((hav₄ (resName j) (by simp [resName, balAltName, String.ext_iff])
        (by simp [resName, balName, String.ext_iff])
        (by simp [resName, String.ext_iff])
        (by simp [resName, String.ext_iff])).trans hret₃.retained_arr))
  have hgam₅ : σ₅t.arrs (gamName j) = arrOf n Gm := by
    rw [harr₅t, hav₅ _ (by simp [gamName, batName, String.ext_iff]),
      hav₄ _ (by simp [gamName, balAltName, String.ext_iff])
        (by simp [gamName, balName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [gamName, String.ext_iff]),
      hav₃ _ (by simp [gamName, resName, String.ext_iff]),
      hav₂ _ (by simp [gamName, cluName, String.ext_iff])
        (by simp [gamName, memName, String.ext_iff]), harr₁]
    exact hgam
  have halv₅ : σ₅t.arrs (alvName (j + 1)) = arrOf n (fun _ => 0) := by
    rw [harr₅t, hav₅ _ (by simp [alvName, batName, String.ext_iff]),
      hav₄ _ (by simp [alvName, balAltName, String.ext_iff])
        (by simp [alvName, balName, String.ext_iff])
        (by simp [alvName, String.ext_iff])
        (by simp [alvName, String.ext_iff]),
      hav₃ _ (by simp [alvName, resName, String.ext_iff]),
      hav₂ _ (by simp [alvName, cluName, String.ext_iff])
        (by simp [alvName, memName, String.ext_iff]), harr₁]
    exact halv₀
  have hgam₅' : σ₅t.arrs (gamName (j + 1)) = arrOf n (fun _ => 0) := by
    rw [harr₅t, hav₅ _ (by simp [gamName, batName, String.ext_iff]),
      hav₄ _ (by simp [gamName, balAltName, String.ext_iff])
        (by simp [gamName, balName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [gamName, String.ext_iff]),
      hav₃ _ (by simp [gamName, resName, String.ext_iff]),
      hav₂ _ (by simp [gamName, cluName, String.ext_iff])
        (by simp [gamName, memName, String.ext_iff]), harr₁]
    exact hgam₀
  obtain ⟨σ₆, hr₆, ⟨Alv, Gam, Mem, mm, hchild₆⟩,
      hfv₆, hfa₆, -, -⟩ :=
    ((streamChildFilterStep (G := G) hB.one_lt hB.n_lt hWaB hGmB
      hWaSup).frame).run (σ := σ₅t)
      ⟨hret₅, by simpa [σ₅t] using hbat₅, hgam₅, halv₅, hgam₅'⟩
  have hav₆ : ∀ a : String, a ≠ alvName (j + 1) →
      a ≠ gamName (j + 1) → a ≠ memName (j + 1) →
      σ₆.arrs a = σ₅t.arrs a := by
    intro a ha hg hm
    exact hfa₆ a (by
      simp [streamChildFilterCom, streamChildGameCom, streamBlockSubCom,
        streamBlockAndSubCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.warrs,
        RamDriverFrames.warrs_memFilterCom, ha, hg, hm])
  have hvv₆ : ∀ y : String, y ≠ "p" → y ≠ "pend" → y ≠ "cw" →
      y ≠ "mk" → y ≠ mnumName (j + 1) → y ≠ "mv" →
      σ₆.vars y = σ₅t.vars y := by
    intro y hp he hc hmk hmm hmv
    exact hfv₆ y (by
      simp [streamChildFilterCom, streamChildGameCom, streamBlockSubCom,
        streamBlockAndSubCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.wvars,
        RamDriverFrames.wvars_memFilterCom, hp, he, hc, hmk, hmm, hmv])
  have hfv : ∀ y : String, y ≠ ctrName j → y ≠ mnumName (j + 1) →
      y ≠ "cw" → y ∉ descendScalars → σ₆.vars y = σ.vars y := by
    intro y hctr hmm hcw hs
    have hp : y ≠ "p" := fun h => hs (h.symm ▸ (by decide))
    have hpend : y ≠ "pend" := fun h => hs (h.symm ▸ (by decide))
    have hmk : y ≠ "mk" := fun h => hs (h.symm ▸ (by decide))
    have hmv : y ≠ "mv" := fun h => hs (h.symm ▸ (by decide))
    have htail : y ≠ "tail" := fun h => hs (h.symm ▸ (by decide))
    have hbq : y ≠ "bq" := fun h => hs (h.symm ▸ (by decide))
    rw [hvv₆ y hp hpend hcw hmk hmm hmv, hvar₅t y htail,
      hvv₅ y hs, hvv₄ y hmm hs, hvv₃ y hp hpend hcw,
      hvv₂ y hp hbq, hvar₁ y hctr]
  have hfa : ∀ a : String,
      a ≠ cluName j → a ≠ memName (j + 1) → a ≠ resName j →
      a ≠ balAltName j → a ≠ balName j → a ≠ "q" → a ≠ "qd" →
      a ≠ batName j → a ≠ alvName (j + 1) →
      a ≠ gamName (j + 1) → σ₆.arrs a = σ.arrs a := by
    intro a hclu hmem hres hba hbl hq hqd hbat halv hgam'
    rw [hav₆ a halv hgam' hmem, harr₅t a, hav₅ a hbat,
      hav₄ a hba hbl hq hqd, hav₃ a hres, hav₂ a hclu hmem,
      harr₁ a]
  have hvOld : ∀ a < j, σ₆.vars (ctrName a) = σ.vars (ctrName a) := by
    intro a ha
    exact hfv (ctrName a) (ctrName_ne (by omega))
      (by simp [ctrName, mnumName, String.ext_iff])
      (by simp [ctrName, String.ext_iff]) (ctrName_notMem_descendScalars a)
  have hrOld : ∀ a < j, σ₆.arrs (resName a) = σ.arrs (resName a) := by
    intro a ha
    have hres : resName a ≠ resName j := by
      intro he
      have : a = j := prefixed_inj (p := "res") (by simpa only [resName] using he)
      omega
    exact hfa (resName a)
      (by simp [resName, cluName, String.ext_iff])
      (by simp [resName, memName, String.ext_iff]) hres
      (by simp [resName, balAltName, String.ext_iff])
      (by simp [resName, balName, String.ext_iff])
      (by simp [resName, String.ext_iff]) (by simp [resName, String.ext_iff])
      (by simp [resName, batName, String.ext_iff])
      (by simp [resName, alvName, String.ext_iff])
      (by simp [resName, gamName, String.ext_iff])
  have haOld : ∀ a < j, σ₆.arrs (gamName a) = σ.arrs (gamName a) := by
    intro a ha
    have hgame : gamName a ≠ gamName (j + 1) := by
      intro he
      have : a = j + 1 := prefixed_inj (p := "gam") (by simpa only [gamName] using he)
      omega
    exact hfa (gamName a)
      (by simp [gamName, cluName, String.ext_iff])
      (by simp [gamName, memName, String.ext_iff])
      (by simp [gamName, resName, String.ext_iff])
      (by simp [gamName, balAltName, String.ext_iff])
      (by simp [gamName, balName, String.ext_iff])
      (by simp [gamName, String.ext_iff]) (by simp [gamName, String.ext_iff])
      (by simp [gamName, batName, String.ext_iff])
      (by simp [gamName, alvName, String.ext_iff]) hgame
  have hpOld : ∀ a < j, σ₆.arrs (parName a) = σ.arrs (parName a) := by
    intro a ha
    have hpar : parName a ≠ balName j := by
      intro he
      have : a = j := prefixed_inj (p := "bal")
        (by simpa only [parName, balName] using he)
      omega
    exact hfa (parName a)
      (by simp [parName, balName, cluName, String.ext_iff])
      (by simp [parName, balName, memName, String.ext_iff])
      (by simp [parName, balName, resName, String.ext_iff])
      (by simp [parName, balName, balAltName, String.ext_iff]) hpar
      (by simp [parName, balName, String.ext_iff])
      (by simp [parName, balName, String.ext_iff])
      (by simp [parName, balName, batName, String.ext_iff])
      (by simp [parName, balName, alvName, String.ext_iff])
      (by simp [parName, balName, gamName, String.ext_iff])
  have hctr₆ : σ₆.vars (ctrName j) = (v : ℕ) := by
    rw [hvv₆ _ (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, mnumName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]),
      hvar₅t _ (by simp [ctrName, String.ext_iff]),
      hvv₅ _ (ctrName_notMem_descendScalars j),
      hvv₄ _ (by simp [ctrName, mnumName, String.ext_iff])
        (ctrName_notMem_descendScalars j)]
    exact hctr₃
  have hpar₆ : σ₆.arrs (parName j) = arrOf n P := by
    rw [hav₆ _ (by simp [parName, balName, alvName, String.ext_iff])
        (by simp [parName, balName, gamName, String.ext_iff])
        (by simp [parName, balName, memName, String.ext_iff]),
      harr₅t, hav₅ _ (by simp [parName, balName, batName, String.ext_iff])]
    exact hpar₄
  have hRA : masked G Ra ≤ masked G A₀ := by
    intro x y hxy
    rw [RamBfs.masked_adj] at hxy ⊢
    exact ⟨hxy.1, hRaA _ x.isLt hxy.2.1, hRaA _ y.isLt hxy.2.2⟩
  have hRGm : masked G Ra ≤ masked G Gm := le_trans hRA hle
  have hAlvA : ∀ z, z < n → Alv z ≠ 0 → A₀ z ≠ 0 := by
    intro z hz hAz
    exact ((hchild₆.masks.child_point ⟨z, hz⟩).mp hAz).1
  have hAlvR : ∀ z, z < n → Alv z ≠ 0 → Ra z ≠ 0 := by
    intro z hz hAz hRz
    rw [hchild₆.masks.child_val z hz, hRz, Nat.zero_mul] at hAz
    exact hAz rfl
  have hXballA : markSet n Xa ⊆ ball (masked G A₀) (2 * cap) v := by
    rw [hchild₆.cluster_set]
    have h := RamCover.inCluster_subset_ball (masked G A₀) π (r := cap) hvN
    rwa [show (⟨centre c, hvN⟩ : Fin n) = v from rfl] at h
  have hXballG : markSet n Xa ⊆ ball (masked G Gm) (2 * cap) v := by
    intro z hz
    exact Lax3Proofs.WalkDistance.ball_mono_graph v hle (hXballA hz)
  have hWwalkRec : ∀ (u : Fin n) (A' : SimpleGraph (Fin n)),
      RecordedRound B G σ j u A' → WithinDist A' (2 * cap) u v →
      ∃ p : A'.Walk u v, p.length ≤ 2 * cap ∧
        {z | z ∈ p.support} ∩ markSet n Xa ⊆ markSet n Wa := by
    intro u A' hround hwd
    obtain ⟨a, haj, hua, Ga', hGa', -, hAeq⟩ := hround
    have hUa : u = U a := Fin.ext (by rw [← hua, (hUG a haj).1])
    have hGeq : masked G Ga' = masked G (Games a) :=
      masked_congr (fun k hk =>
        eq_of_arrOf_eq (hGa'.symm.trans (hUG a haj).2.1) hk)
    subst hAeq
    subst hUa
    rw [hGeq] at hwd ⊢
    exact hWwalk a haj hwd
  have hplay₆ : PlayRec B cap G (j + 1) Alv Gam σ₆ := by
    refine playRec_succ (X := markSet n Xa) (W := markSet n Wa)
      (⟨rounds, hrec, hle, hplayR, hcached⟩ : PlayRec B cap G j A₀ Gm σ)
      hvOld hrOld haOld hpOld hAlvA hctr₆ hchild₆.masks.parent_game_arr
      hGmB hchild₆.masks.retained_arr hpar₆ htree₄ hRcov hRGm hAlvR
      hXballG hvW hWwalkRec ?_ ?_
    · rw [hchild₆.masks.game_graph]
    · rw [hchild₆.masks.child_graph, hchild₆.masks.game_graph]
      exact Evaluator.deleteVerts_mono_graph
        (Evaluator.deleteVerts_mono_graph hle)
  have hnonempty : (markSet n Wa ∩ markSet n Xa).Nonempty :=
    ⟨v, hvW, hvX⟩
  have hcard : (markSet n Wa).ncard ≤ mb := by
    refine le_trans hWcard ?_
    rw [hmb]
    calc
      1 + j * (2 * cap + 1) ≤ (j + 1) * (2 * cap + 1) := by
        rw [Nat.add_mul, one_mul]
        omega
      _ ≤ ell * (2 * cap + 1) := Nat.mul_le_mul_right _ (by omega)
  have hrun : Run B (streamPlayCom cap j) σ σ₆
      (3 + (streamClusterLoadCost tail +
        (streamBlockAndCost tail +
          (cacheRoundCost tail bw bw +
            (streamBatchCachedCost cap j + (2 + streamChildFilterCost tail)))))) :=
    hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₅t.seq hr₆)))))
  refine ⟨σ₆, _, hrun, ?_, Xa, Mm, Ra, Wa, Alv, Gam, Mem, mm, ?_⟩
  · simp [streamPlayCost, bw]
    omega
  · exact ⟨hchild₆, hplay₆, hnonempty, hcard,
      exists_arrOf_run hrun hwa₀⟩

#print axioms streamPlayStep

end Lax3Proofs.Refine.CoverActiveStreamPlay
