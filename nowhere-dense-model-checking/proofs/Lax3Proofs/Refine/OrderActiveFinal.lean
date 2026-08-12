import Lax3Proofs.Refine.OrderActiveRun
import Lax3Proofs.Refine.OrderActiveRank

/-!
# Finalizing the compact active ordering

The augmentation fold ends with an oriented compact CSR.  This file supplies
the two seams needed by the final phase: expose that CSR to the resident
symmetrizer, and lift an arbitrary compact graph back through the member
embedding so the resident elimination wrapper can consume it without a
carrier-sized copy.
-/

namespace Lax3Proofs.Refine.OrderActiveFinal

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Augmentation (Orientation IsAugChain GreedyFratRound
  AugmentedDepthOneDensity LowDegreeVertices budget)
open Lax3Proofs.RamBfs (masked_adj)
open Lax3Proofs.RamCoverActive (CentresBy)
open Lax3Proofs.RamDriver (ordName exists_arrOf)
open Lax3Proofs.RamDriverCluster (markSet mem_markSet)
open Lax3Proofs.RamElim (CsrSimple InCsr)
open Lax3Proofs.Refine.ScatterBlock (MemList renEnv_arrs renEnv_vars)
open Lax3Proofs.Refine.ElimCompact (memEmb memEmb_injective memGraph run_length)
open Lax3Proofs.Refine.ElimCompactWalks (memEmb_mem_markSet)
open Lax3Proofs.Refine.SymCompact (SymMemPost symCompactCost prep_bounds_of_inCsr)
open Lax3Proofs.Refine.CompactPreps (symPreps)
open Lax3Proofs.Refine.OrderActiveWork
open Lax3Proofs.Refine.OrderActiveChain
open Lax3Proofs.Refine.OrderActiveInit (csrSimple_congr_offsets)
open Lax3Proofs.Refine.OrderActiveElim (ElimOrderData elimWorkCom elimWorkCost
  elimWork_spec)
open Lax3Proofs.Refine.OrderActiveRank (memberOrdCom memberOrdCom_spec)
open Lax3Proofs.Refine.OrderActiveMath (activePerm activeCentre centresBy_activeCentre)
open Lax3Proofs.Refine.OrderActiveTail

/-- The resident size invariant and live in-CSR prefixes give precisely the
entry surface of compact symmetrization. -/
theorem symWorkEntry_of_sized {n mm W kd : ℕ} {IO IT : ℕ → ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm) (hkd : σ.vars "kd" = kd)
    (hmn : mm ≤ n) (hkdW : kd ≤ W) (hsz : ActiveOrderSized n W σ)
    (hio : ∀ i, i ≤ mm → (σ.arrs "ioff").getD i 0 = IO i)
    (hit : ∀ z, z < kd → (σ.arrs "itg").getD z 0 = IT z) :
    ∃ T₀ : ℕ → ℕ, SymWorkEntryC n mm W W kd IO IT T₀ σ := by
  classical
  have get (a : String) (k : ℕ) (h : (a, k) ∈ activeOrderLayout n W) :
      ∃ g, σ.arrs a = arrOf k g := hsz.get h
  obtain ⟨iog, hiog⟩ := get "ioff" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨itg, hitg⟩ := get "itg" W (by simp [activeOrderLayout])
  obtain ⟨dog, hdog⟩ := get "doff" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨dtg, hdtg⟩ := get "dtg" W (by simp [activeOrderLayout])
  obtain ⟨oog, hoog⟩ := get "ooff" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨ofg, hofg⟩ := get "ofl" n (by simp [activeOrderLayout])
  obtain ⟨otg, hotg⟩ := get "otg" W (by simp [activeOrderLayout])
  obtain ⟨gof, hgof⟩ := get "gof" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨gtg, hgtg⟩ := get "gtg" W (by simp [activeOrderLayout])
  have hioP : ∀ i ≤ mm, iog i = IO i := by
    intro i hi
    have h := hio i hi
    rwa [hiog, getD_arrOf iog (by omega)] at h
  have hitP : ∀ z < kd, itg z = IT z := by
    intro z hz
    have h := hit z hz
    rwa [hitg, getD_arrOf itg (lt_of_lt_of_le hz hkdW)] at h
  refine ⟨gtg, ?_⟩
  rw [SymWorkEntryC, Lax3Proofs.Refine.SymCompact.SymEntryC]
  refine ⟨?_, ?_, ?_, hmn, hkdW, ⟨iog, ?_, hioP⟩, ⟨itg, ?_, hitP⟩,
    ⟨dog, ?_⟩, ⟨dtg, ?_⟩, ⟨oog, ?_⟩, ⟨ofg, ?_⟩, ⟨otg, ?_⟩,
    ⟨gof, ?_⟩, ?_⟩
  · simpa only [renEnv_vars] using hn
  · simpa only [renEnv_vars] using hmm
  · simpa only [renEnv_vars] using hkd
  · simpa [renEnv_arrs, engineWorkSwap] using hiog
  · simpa [renEnv_arrs, engineWorkSwap] using hitg
  · simpa [renEnv_arrs, engineWorkSwap] using hdog
  · simpa [renEnv_arrs, engineWorkSwap] using hdtg
  · simpa [renEnv_arrs, engineWorkSwap] using hoog
  · simpa [renEnv_arrs, engineWorkSwap] using hofg
  · simpa [renEnv_arrs, engineWorkSwap] using hotg
  · simpa [renEnv_arrs, engineWorkSwap] using hgof
  · simpa [renEnv_arrs, engineWorkSwap] using hgtg

/-- The member embedding as a `Function.Embedding`, for graph transport. -/
def memberEmbedding {n mm : ℕ} {Mem : ℕ → ℕ} {X : Set (Fin n)}
    (hml : MemList n mm Mem X) : Fin mm ↪ Fin n :=
  ⟨memEmb hml, memEmb_injective hml⟩

/-- Put a compact graph back on the ambient carrier, with no extra edges. -/
def memberLiftGraph {n mm : ℕ} {Mem : ℕ → ℕ} {X : Set (Fin n)}
    (hml : MemList n mm Mem X) (H : SimpleGraph (Fin mm)) : SimpleGraph (Fin n) :=
  H.map (memberEmbedding hml)

/-- Compacting the lifted graph through the same member list recovers the
original compact graph.  The mask is harmless because every member is live. -/
theorem memGraph_memberLiftGraph {n mm : ℕ} {M Mem : ℕ → ℕ}
    {hml : MemList n mm Mem (markSet n M)} (H : SimpleGraph (Fin mm)) :
    memGraph (memberLiftGraph hml H) M hml = H := by
  ext i j
  rw [Lax3Proofs.Refine.ElimCompact.memGraph_adj, masked_adj]
  constructor
  · rintro ⟨hadj, -, -⟩
    rw [memberLiftGraph, SimpleGraph.map_adj] at hadj
    obtain ⟨u, v, huv, hui, hvj⟩ := hadj
    have hui' : u = i := (memberEmbedding hml).injective hui
    have hvj' : v = j := (memberEmbedding hml).injective hvj
    simpa [hui', hvj'] using huv
  · intro hij
    refine ⟨?_, ?_, ?_⟩
    · rw [memberLiftGraph, SimpleGraph.map_adj]
      exact ⟨i, j, hij, rfl, rfl⟩
    · exact mem_markSet.mp (memEmb_mem_markSet hml i)
    · exact mem_markSet.mp (memEmb_mem_markSet hml j)

/-! ## The final compact phase -/

/-- Symmetrize the last orientation, eliminate the resulting undirected
compact graph, and invert its rank into the depth's carrier-sized order
array.  Every loop is bounded by the active carrier or its live slots. -/
def activeFinishCom (j : ℕ) : Com :=
  .seq symCompactWorkCom (.seq elimWorkCom (memberOrdCom (ordName j)))

def activeFinishCost (mm m : ℕ) : ℕ :=
  (symCompactCost mm m + 2) + (elimWorkCost mm (m + m) + (13 * mm + 6))

/-- A centre array may change outside its live prefix without changing the
active ordering it represents. -/
theorem centresBy_congr_prefix {n q : ℕ} {M c c' : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} (h : CentresBy n q M π c)
    (hc : ∀ k < q, c' k = c k) : CentresBy n q M π c' where
  count_le := h.count_le
  centre_lt k hk := by rw [hc k hk]; exact h.centre_lt k hk
  alive k hk := by rw [hc k hk]; exact h.alive k hk
  rank_mono i k hik hk := by
    rw [hc i (by omega), hc k hk]
    exact h.rank_mono i k hik hk
  complete v hv hMv := by
    obtain ⟨k, hk, hkv⟩ := h.complete v hv hMv
    exact ⟨k, hk, by rw [hc k hk, hkv]⟩

/-- Finish an `R`-round active fold.  The returned permutation is exactly the
second elimination's compact rank, its centre array enumerates the live
carrier vertices, and the six facts required by `CoverDegree` are retained as
one `AugChainData` certificate. -/
theorem activeFinish_spec {B n mm cs W w d D₁ d₀ R j : ℕ}
    {H : SimpleGraph (Fin mm)} {M Mem : ℕ → ℕ}
    {σ : Env} (hml : MemList n mm Mem (markSet n M))
    (hmn : mm ≤ n) (hwW : w ≤ W) (hB : mm + w + 1 < B) (hnB : n < B)
    (hd₀d : d₀ ≤ d)
    (hdens : ∀ (D : ℕ → Orientation mm) (i : ℕ), i ≤ R →
      IsAugChain H D i →
      (∀ l < i, GreedyFratRound (D l) (D (l + 1))) →
      AugmentedDepthOneDensity D i D₁)
    (hcap : activeChainWidthE mm cs d D₁ R ≤ w)
    (hmin₀ : ∀ k', LowDegreeVertices H k' → d₀ ≤ k')
    (hord : ∃ g, σ.arrs (ordName j) = arrOf n g)
    (hI : ActiveFoldInv n mm W w d₀ H Mem R σ) :
    ∃ (σ' : Env) (m : ℕ) (D : ℕ → Orientation mm) (k : ℕ)
        (πm : Equiv.Perm (Fin mm)) (centre : ℕ → ℕ),
      Run B (activeFinishCom j) σ σ' (activeFinishCost mm m) ∧
      m ≤ w ∧
      σ'.arrs (ordName j) = arrOf n centre ∧
      CentresBy n mm M (activePerm hml πm) centre ∧
      Lax3Proofs.CoverDegree.AugChainData H D πm R d₀ k ∧
      ActiveOrderSized n W σ' ∧
      σ'.vars "n" = n ∧ σ'.vars "mm" = mm ∧
      σ'.arrs "mem" = arrOf n Mem ∧
      σ'.arrs "off" = σ.arrs "off" ∧ σ'.arrs "tgt" = σ.arrs "tgt" ∧
      ActiveZeroTail mm σ σ' := by
  classical
  obtain ⟨hn, hmm, hmem, hsz, D, m, IO, IT, hchain, hgreedy, hD₀, hin,
    hmw, hkd, hio, hit⟩ := hI
  have hDR : (D R).InDegLE (budget d D₁ R) :=
    Lax3Proofs.Augmentation.greedy_chain_inDegLE hchain
      (hdens D R le_rfl hchain hgreedy) hgreedy
      (fun v => (hD₀ v).trans hd₀d) R le_rfl
  have hmArc : m ≤ mm * budget d D₁ R :=
    Lax3Proofs.Refine.AugCompact.arcs_le_compact hin hDR
  have htwo : 2 * budget d D₁ R ≤ (budget d D₁ R + 1) ^ 2 := by
    nlinarith
  have hsymSlots : m + m ≤ mm * (budget d D₁ R + 1) ^ 2 := by
    calc
      m + m = 2 * m := by omega
      _ ≤ 2 * (mm * budget d D₁ R) := Nat.mul_le_mul_left 2 hmArc
      _ = mm * (2 * budget d D₁ R) := by ring
      _ ≤ mm * (budget d D₁ R + 1) ^ 2 := Nat.mul_le_mul_left mm htwo
  have hbaseWidth : mm * (budget d D₁ R + 1) ^ 2 ≤ w := by
    simp only [activeChainWidthE] at hcap
    omega
  have hfitw : m + m ≤ w := hsymSlots.trans hbaseWidth
  have hfitW : m + m ≤ W := hfitw.trans hwW
  have hmB : m < B := lt_of_le_of_lt hmw (by omega)
  have hmmB : mm < B := by omega
  have hsymB : m + m < B := lt_of_le_of_lt hfitw (by omega)
  obtain ⟨hIOB, hITB⟩ := prep_bounds_of_inCsr hin hmB hmmB
  obtain ⟨T₀, hent⟩ :=
    symWorkEntry_of_sized hn hmm hkd hmn (hmw.trans hwW) hsz hio hit
  obtain ⟨σs, rs, hsym, -, htailS, hns, hoffS, htgtS⟩ :=
    symCompactWork_spec (symPreps B n mm W W m) hin le_rfl (hmw.trans hwW)
      hfitW hnB hsymB (by omega) hmB hIOB hITB hent
  have hszs : ActiveOrderSized n W σs := hsz.run rs
  obtain ⟨SO, ST, hSO, hST, hcsrS, -⟩ := hsym
  have hSO' : ∀ i, i ≤ mm → (σs.arrs "gof").getD i 0 = SO i := by
    simpa only [SymWorkPost, SymMemPost, renEnv_arrs, engineWorkSwap_off] using hSO
  have hST' : σs.arrs "gtg" = arrOf W ST := by
    simpa only [SymWorkPost, SymMemPost, renEnv_arrs, engineWorkSwap_tgt] using hST
  obtain ⟨SOf, hSOf⟩ :=
    hszs.get (p := ("gof", n + 1)) (by simp [activeOrderLayout])
  have hSOfSO : ∀ i, i ≤ mm → SOf i = SO i := by
    intro i hi
    have h := hSO' i hi
    rwa [hSOf, getD_arrOf SOf (by omega)] at h
  have hcsrS' : CsrSimple (D R).toGraph (m + m) SOf ST :=
    csrSimple_congr_offsets hcsrS hSOfSO
  have hnS : σs.vars "n" = n := hns
  have hmmS : σs.vars "mm" = mm := by
    rw [rs.frame_var "mm" (by decide), hmm]
  have hmemS : σs.arrs "mem" = arrOf n Mem := by
    rw [rs.frame_arr "mem" (by decide), hmem]
  have getS (a : String) (k : ℕ) (ha : (a, k) ∈ activeOrderLayout n W) :
      ∃ g, σs.arrs a = arrOf k g := hszs.get ha
  let Gup : SimpleGraph (Fin n) := memberLiftGraph hml (D R).toGraph
  have hlift : memGraph Gup M hml = (D R).toGraph :=
    memGraph_memberLiftGraph (M := M) (hml := hml) (D R).toGraph
  have hcsrLift : CsrSimple (memGraph Gup M hml) (m + m) SOf ST := by
    rw [hlift]
    exact hcsrS'
  obtain ⟨σe, re, -, hdata, hnE, hmmE, hoffE, htgtE, htailE⟩ :=
    elimWork_spec (G := Gup) hml hcsrLift (by omega) hnB hfitW hnS hmmS
      hSOf hST' hmemS
      (getS "ork" n (by simp [activeOrderLayout]))
      (getS "alv" n (by simp [activeOrderLayout]))
      (getS "deg" n (by simp [activeOrderLayout]))
      (getS "elm" n (by simp [activeOrderLayout]))
      (getS "rnk" n (by simp [activeOrderLayout]))
      (getS "idg" n (by simp [activeOrderLayout]))
      (getS "bh" (n + 1) (by simp [activeOrderLayout]))
      (getS "bv" (n + W + 1) (by simp [activeOrderLayout]))
      (getS "bn" (n + W + 1) (by simp [activeOrderLayout]))
      (getS "ioff" (n + 1) (by simp [activeOrderLayout]))
      (getS "ifl" n (by simp [activeOrderLayout]))
      (getS "itg" W (by simp [activeOrderLayout]))
  obtain ⟨RR, k, hrnkE, hRRlt, hRRinj, hback, hmink⟩ := hdata
  rw [hlift] at hback hmink
  have hmemE : σe.arrs "mem" = arrOf n Mem := by
    rw [re.frame_arr "mem" (by decide), hmemS]
  have hordLen : (σe.arrs (ordName j)).length = n := by
    rw [run_length (rs.seq re) (ordName j)]
    obtain ⟨g, hg⟩ := hord
    rw [hg, length_arrOf]
  obtain ⟨ord₀, hordE⟩ := exists_arrOf hordLen
  have hRRinj' : ∀ v < mm, ∀ u < mm, RR v = RR u → v = u := by
    intro v hv u hu heq
    exact congrArg Fin.val (hRRinj (a₁ := ⟨v, hv⟩) (a₂ := ⟨u, hu⟩) heq)
  obtain ⟨σo, ro, -, -, -, πm, centre, hordO, hcentre, hπrank⟩ :=
    (memberOrdCom_spec (B := B) (R := RR) (Mem := Mem) (ordName j)
      (by simp [ordName, String.ext_iff]) (by simp [ordName, String.ext_iff])
      hmn hnB hRRlt hRRinj' (fun v hv => hml.lt v hv)).run
      ⟨hmmE, hrnkE, hmemE, ord₀, hordE⟩
  have hrankFun : (fun v : Fin mm => ((πm v : Fin mm) : ℕ)) =
      (fun v : Fin mm => RR (v : ℕ)) := by
    funext v
    exact hπrank v
  have hbackπ : Lax3Proofs.Augmentation.BackDegLE (D R).toGraph
      (fun v : Fin mm => ((πm v : Fin mm) : ℕ)) k := by
    rw [hrankFun]
    exact hback
  have hdataOut : Lax3Proofs.CoverDegree.AugChainData H D πm R d₀ k :=
    ⟨hchain, hgreedy, hD₀, hmin₀, hbackπ, hmink⟩
  have hcentres : CentresBy n mm M (activePerm hml πm) centre :=
    centresBy_congr_prefix (centresBy_activeCentre hml πm) hcentre
  have rAll : Run B (activeFinishCom j) σ σo (activeFinishCost mm m) := by
    simpa only [activeFinishCom, activeFinishCost] using rs.seq (re.seq ro)
  have htailO : ActiveZeroTail mm σe σo := by
    apply ActiveZeroTail.of_frame
    intro a ha
    apply ro.frame_arr a
    simp only [activeZeroNames, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [memberOrdCom, Com.warrs, ordName, String.ext_iff]
  have htailAll : ActiveZeroTail mm σ σo :=
    ActiveZeroTail.trans (ActiveZeroTail.trans htailS htailE) htailO
  refine ⟨σo, m, D, k, πm, centre, rAll, hmw, hordO, hcentres, hdataOut,
    hsz.run rAll, ?_, ?_, ?_, ?_, ?_, htailAll⟩
  · rw [ro.frame_var "n" (by simp [memberOrdCom, Com.wvars]), hnE]
  · rw [ro.frame_var "mm" (by simp [memberOrdCom, Com.wvars]), hmmE]
  · rw [ro.frame_arr "mem" (by
      simp [memberOrdCom, Com.warrs, ordName, String.ext_iff]), hmemE]
  · rw [ro.frame_arr "off" (by
      simp [memberOrdCom, Com.warrs, ordName, String.ext_iff]), hoffE, hoffS]
  · rw [ro.frame_arr "tgt" (by
      simp [memberOrdCom, Com.warrs, ordName, String.ext_iff]), htgtE, htgtS]

/-! ## Axioms -/

#print axioms symWorkEntry_of_sized
#print axioms memGraph_memberLiftGraph
#print axioms activeFinish_spec

end Lax3Proofs.Refine.OrderActiveFinal
