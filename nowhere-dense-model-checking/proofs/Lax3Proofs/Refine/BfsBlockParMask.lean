import Lax3Proofs.Refine.BfsBlockMask
import Lax3Proofs.Refine.BfsBlockPar

/-!
The parent-recording block search, with its distance-scratch contract
restricted to the live support of the current mask.

`BfsBlockPar` removes the carrier-sized fill and charge once the distance
array is globally clean.  A recursive cover turn has a sharper fact: only
the cells in its current cluster have been cleared.  This file combines the
parent invariant with `BfsBlockMask.FrontierM`, so the engine reads, writes,
and restores exactly those cells while retaining a parent tree for later
descendants.
-/

namespace Lax3Proofs.Refine.BfsBlockParMask

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamBfsPaths
open Lax3Proofs.Refine.BfsBlock Lax3Proofs.Refine.BfsBlockMask
open Lax3Proofs.Refine.BfsBlockPar

variable {n ns nt d s : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}
variable {D Q P : ℕ → ℕ} {head tail : ℕ}

/-! ### The mask-scoped parent frontier -/

/-- `FrontierM` together with parent clauses at discovered live cells. -/
structure ParFrontierM {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d s : ℕ)
    (D Q P : ℕ → ℕ) (head tail : ℕ) : Prop where
  base : FrontierM G M d s D Q head tail
  root : P s = s
  pdist : ∀ w < n, M w ≠ 0 → w ≠ s → D w ≤ d → D (P w) + 1 = D w
  padj : ∀ w < n, M w ≠ 0 → w ≠ s → D w ≤ d → MAdj G M (P w) w

namespace ParFrontierM

/-- A live vertex relaxed by the search still carries the sentinel. -/
theorem sentinel_of_relax (hF : FrontierM G M d s D Q head tail) (hht : head < tail)
    {w : ℕ} (hadj : MAdj G M (Q head) w) (hlt : D (Q head) + 1 < D w) :
    D w = d + 1 := by
  have hw : w < n := hadj.lt_right
  have hmw : M w ≠ 0 := hadj.alive_right
  have hcapw : D w ≤ d + 1 := hF.cap w hw hmw
  have hnq : ∀ i < tail, Q i ≠ w := by
    intro i hi hqi
    have h := hF.qcap i hi head le_rfl hht
    rw [hqi] at h
    omega
  by_contra hne
  obtain ⟨i, hi, hqi⟩ := hF.qall w hw hmw (by omega)
  exact hnq i hi hqi

/-- Relax one live vertex and record the expanding vertex as its parent. -/
theorem relax (hF : ParFrontierM G M d s D Q P head tail) (hht : head < tail)
    {w : ℕ} (hadj : MAdj G M (Q head) w) (hlt : D (Q head) + 1 < D w) :
    ParFrontierM G M d s (upd D w (D (Q head) + 1)) (upd Q tail w)
      (upd P w (Q head)) head (tail + 1) := by
  have hdw : D w = d + 1 := sentinel_of_relax hF.base hht hadj hlt
  have hws : s ≠ w := by
    intro hse
    rw [← hse, hF.base.src] at hdw
    omega
  have hwv : w ≠ Q head := by
    intro hwe
    rw [hwe] at hlt
    omega
  refine ⟨hF.base.relax hht hadj hlt, (upd_of_ne _ hws).trans hF.root,
    fun z hz hmz hzs hzd => ?_, fun z hz hmz hzs hzd => ?_⟩
  · by_cases hzw : z = w
    · subst hzw
      rw [upd_self, upd_self, upd_of_ne _ (Ne.symm hwv)]
    · rw [upd_of_ne _ hzw] at hzd ⊢
      have hpz : P z ≠ w := by
        intro hpe
        have hp := hF.pdist z hz hmz hzs hzd
        rw [hpe, hdw] at hp
        omega
      rw [upd_of_ne _ hzw, upd_of_ne _ hpz]
      exact hF.pdist z hz hmz hzs hzd
  · by_cases hzw : z = w
    · subst hzw
      rw [upd_self]
      exact hadj
    · rw [upd_of_ne _ hzw] at hzd
      rw [upd_of_ne _ hzw]
      exact hF.padj z hz hmz hzs hzd

/-- A live source seeds both the queue and the parent tree. -/
theorem seed_alive (G : SimpleGraph (Fin n)) (M : ℕ → ℕ) (d : ℕ) (hs : s < n)
    (hms : M s ≠ 0) {g Q p : ℕ → ℕ}
    (hg : ∀ j < n, M j ≠ 0 → g j = d + 1) (hQ : Q 0 = s) :
    ParFrontierM G M d s (upd g s 0) Q (upd p s s) 0 1 := by
  have hval : ∀ z, z < n → M z ≠ 0 → z ≠ s → upd g s 0 z = d + 1 :=
    fun z hz hmz hzs => by rw [upd_of_ne _ hzs]; exact hg z hz hmz
  exact ⟨frontierM_seed_alive G M d hs hms hg hQ, upd_self ..,
    fun z hz hmz hzs hzd => by rw [hval z hz hmz hzs] at hzd; omega,
    fun z hz hmz hzs hzd => by rw [hval z hz hmz hzs] at hzd; omega⟩

/-- Complete the physical mask-scoped search to a total ghost distance
labelling by assigning the sentinel to every dead cell. -/
def ghostDist (d : ℕ) (M D : ℕ → ℕ) (w : ℕ) : ℕ :=
  if M w = 0 then d + 1 else D w

/-- The completed mask-scoped frontier retains a full `ParTree`.  The source
is live in every cache built by the driver, so the ghost labelling agrees
with the physical source cell. -/
theorem tree (hF : ParFrontierM G M d s D Q P tail tail) (hs : s < n)
    (hms : M s ≠ 0) : ParTree G M d s (ghostDist d M D) P := by
  refine ⟨?_, ?_, hF.root, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hmw : M w = 0
    · simp [ghostDist, hmw]
    · simpa [ghostDist, hmw] using hF.base.cap w hw hmw
  · simp [ghostDist, hms, hF.base.src]
  · intro w hw hdw
    have hmw : M w ≠ 0 := by
      intro hm
      simp [ghostDist, hm] at hdw
    simpa [ghostDist, hmw] using hF.base.sound w hw hmw (by
      simpa [ghostDist, hmw] using hdw)
  · intro k hk w hwd
    by_cases hws : w = s
    · subst hws
      simp [ghostDist, hms, hF.base.src]
    · have hmw : M w ≠ 0 := alive_of_wd hwd (Ne.symm hws)
      simpa [ghostDist, hmw] using hF.base.complete k hk w hwd
  · intro w hw hws hdw
    have hmw : M w ≠ 0 := by
      intro hm
      simp [ghostDist, hm] at hdw
    have hdw' : D w ≤ d := by simpa [ghostDist, hmw] using hdw
    have hadj := hF.padj w hw hmw hws hdw'
    have hmp : M (P w) ≠ 0 := hadj.alive_left
    simpa [ghostDist, hmw, hmp] using hF.pdist w hw hmw hws hdw'
  · intro w hw hws hdw
    have hmw : M w ≠ 0 := by
      intro hm
      simp [ghostDist, hm] at hdw
    exact hF.padj w hw hmw hws (by simpa [ghostDist, hmw] using hdw)

end ParFrontierM

/-! ### The parent-recording scan -/

/-- The block scan invariant with both the narrowed frontier and the parent
array carried through the machine state. -/
def ScanInvParM {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ)
    (nt d s head v dv sc₀ : ℕ) (O T Q₀ : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ D Q P, SearchEnvPar n nt s O T M D Q P τ ∧
    ParFrontierM G M d s D Q P head (τ.vars "tail") ∧
    τ.vars "head" = head ∧ head < τ.vars "tail" ∧ Q head = v ∧ D v = dv ∧
    τ.vars "v" = v ∧ τ.vars "dv" = dv ∧ τ.vars "dn" = dv + 1 ∧
    τ.vars "jend" = O (v + 1) ∧ O v ≤ τ.vars "j" ∧ τ.vars "j" ≤ O (v + 1) ∧
    τ.vars "sc" = sc₀ + (τ.vars "j" - O v) ∧
    (∀ j', O v ≤ j' → j' < τ.vars "j" → M (T j') ≠ 0 → D (T j') ≤ dv + 1) ∧
    (∀ i < head, Q i = Q₀ i)

/-- One parent-recording slot, with every distance assertion restricted to
the branch where the target is live. -/
theorem scanSlotParM_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B)
    (hMB : ∀ z < n, M z < B) {head v dv sc₀ : ℕ} (hv : v < n)
    (hsc₀ : sc₀ + Csr.rowLen O v ≤ ns) {Q₀ : ℕ → ℕ} {τ : Env}
    (hI : ScanInvParM G M nt d s head v dv sc₀ O T Q₀ τ)
    (hjlt : τ.vars "j" < O (v + 1)) :
    ∃ τ' K, Run B scanSlotPar τ τ' K ∧ K ≤ 44 ∧
      ScanInvParM G M nt d s head v dv sc₀ O T Q₀ τ' ∧
      τ'.vars "j" = τ.vars "j" + 1 := by
  obtain ⟨D, Q, P, ⟨⟨hn, hsrc, hoff, htgt, halv, hdist, hq⟩, hpar⟩, hF,
    hhead, hht, hqv, hDv, hvv, hdvv, hdnv, hje, hj₁, hj₂, hsc, hscan, hq₀⟩ := hI
  obtain ⟨hvn', hdvle, hmv⟩ := hF.base.qmem head hht
  rw [hqv] at hvn' hdvle hmv
  rw [hDv] at hdvle
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hjns : τ.vars "j" < ns := by omega
  have hwn : T (τ.vars "j") < n := hcsr.target_lt' hv hjlt
  have hrj : (τ.arrs "tgt").getD (τ.vars "j") 0 = T (τ.vars "j") := by
    rw [htgt, getD_arrOf T (by omega)]
  have hrj' : (τ.arrs "tgt")[τ.vars "j"]?.getD 0 = T (τ.vars "j") := by
    rw [← List.getD_eq_getElem?_getD]
    exact hrj
  have hjlen : τ.vars "j" < (τ.arrs "tgt").length := by
    rw [htgt, length_arrOf]
    omega
  have hwB : (τ.arrs "tgt").getD (τ.vars "j") 0 < B := by rw [hrj]; omega
  have halvlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "alv").length := by
    rw [hrj, halv, length_arrOf]
    exact hwn
  have halvv : (τ.arrs "alv").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0 =
      M (T (τ.vars "j")) := by rw [hrj, halv, getD_arrOf M hwn]
  have halvB : (τ.arrs "alv").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0 < B := by
    rw [halvv]
    exact hMB _ hwn
  have hdistlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "dist").length := by
    rw [hrj, hdist, length_arrOf]
    exact hwn
  have hparlen : (τ.arrs "tgt").getD (τ.vars "j") 0 < (τ.arrs "par").length := by
    rw [hrj, hpar, length_arrOf]
    exact hwn
  have hdistv : (τ.arrs "dist").getD ((τ.arrs "tgt").getD (τ.vars "j") 0) 0 =
      D (T (τ.vars "j")) := by rw [hrj, hdist, getD_arrOf D hwn]
  have hqlen : (τ.arrs "q").length = n := by rw [hq, length_arrOf]
  have hscB : τ.vars "sc" + 1 < B := by omega
  have hjB : τ.vars "j" + 1 < B := by omega
  have hdnB : τ.vars "dn" < B := by omega
  have hvB : τ.vars "v" < B := by omega
  have hMw : M (T (τ.vars "j")) < B := hMB _ hwn
  have htlB : τ.vars "tail" ≤ n := hF.base.tl
  have hbrAlv :
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "alv").getD
        ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0 =
        M (T (τ.vars "j")) := by
    rw [arrs_setVar, vars_setVar]
    simpa using halvv
  have hbrDist :
      ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).arrs "dist").getD
        ((τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "w") 0 =
        D (T (τ.vars "j")) := by
    rw [arrs_setVar, vars_setVar]
    simpa using hdistv
  have hbrDn :
      (τ.setVar "w" ((τ.arrs "tgt").getD (τ.vars "j") 0)).vars "dn" = dv + 1 := by
    simpa using hdnv
  have hroom : dv + 1 < D (T (τ.vars "j")) → τ.vars "tail" < n := by
    intro hlt'
    refine hF.base.tail_lt hwn ?_
    intro i hi hqi
    have hc := hF.base.qcap i hi head le_rfl hht
    rw [hqi, hqv, hDv] at hc
    omega
  have hvne : dv + 1 < D (T (τ.vars "j")) → v ≠ T (τ.vars "j") := by
    intro hlt' hve
    rw [← hve, hDv] at hlt'
    omega
  run_vcg
  · have hmw : M (T (τ.vars "j")) ≠ 0 := by omega
    have hlt' : dv + 1 < D (T (τ.vars "j")) := by omega
    have hadj : MAdj G M (Q head) (T (τ.vars "j")) := by
      rw [hqv]
      exact hcsr.madj_of_slot hv hj₁ hjlt hmv hmw
    have hltq : D (Q head) + 1 < D (T (τ.vars "j")) := by
      rw [hqv, hDv]
      exact hlt'
    have hrelax := hF.relax hht hadj hltq
    rw [hqv, hDv] at hrelax
    refine ⟨⟨upd D (T (τ.vars "j")) (dv + 1),
      upd Q (τ.vars "tail") (T (τ.vars "j")), upd P (T (τ.vars "j")) v,
      ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
          by simp [halv], by simp [hdist, hrj', hdnv, set_arrOf_eq_upd],
          by simp [hq, hrj', set_arrOf_eq_upd]⟩,
        by simp [hpar, hrj', hvv, set_arrOf_eq_upd]⟩,
      by simpa using hrelax, by simp [hhead], by simp; omega,
      (upd_of_ne _ (show head ≠ τ.vars "tail" by omega)).trans hqv,
      (upd_of_ne _ (hvne hlt')).trans hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_,
      fun i hi => (upd_of_ne _ (by omega)).trans (hq₀ i hi)⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    by_cases hje' : T j' = T (τ.vars "j")
    · rw [hje', upd_self]
    · rw [upd_of_ne _ hje']
      rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
      · exact hscan j' hj₁' hlt'' hmj'
      · exact absurd (show j' = τ.vars "j" by simp at hj₂'; omega)
          (by rintro rfl; exact hje' rfl)
  · refine ⟨⟨D, Q, P, ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩, by simp [hpar]⟩,
      by simpa using hF, by simp [hhead], by simp [hht], by simp [hqv], hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
    · exact hscan j' hj₁' hlt'' hmj'
    · have hj : j' = τ.vars "j" := by simp at hj₂'; omega
      subst hj
      omega
  · refine ⟨⟨D, Q, P, ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
        by simp [halv], by simp [hdist], by simp [hq]⟩, by simp [hpar]⟩,
      by simpa using hF, by simp [hhead], by simp [hht], by simp [hqv], hDv,
      by simp [hvv], by simp [hdvv], by simp [hdnv], by simp [hje], by simp; omega,
      by simp; omega, by simp [hsc]; omega, ?_, hq₀⟩, by simp⟩
    intro j' hj₁' hj₂' hmj'
    simp only [vars_setVar] at hj₂'
    rcases Nat.lt_or_ge j' (τ.vars "j") with hlt'' | hge''
    · exact hscan j' hj₁' hlt'' hmj'
    · have hj : j' = τ.vars "j" := by simp at hj₂'; omega
      subst hj
      omega
  · rw [hbrDist]
    have hmw : M (T (τ.vars "j")) ≠ 0 := by omega
    have hcap := hF.base.cap _ hwn hmw
    omega

/-- Scan the whole adjacency block of the current queue vertex. -/
theorem scanParM_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B)
    (hMB : ∀ z < n, M z < B) {head v dv sc₀ : ℕ} (hv : v < n)
    (hsc₀ : sc₀ + Csr.rowLen O v ≤ ns) {Q₀ : ℕ → ℕ} :
    Spec B
      (fun τ => ScanInvParM G M nt d s head v dv sc₀ O T Q₀ τ ∧ τ.vars "j" = O v)
      (Csr.scan "j" "jend" scanSlotPar)
      (fun _ τ' => ScanInvParM G M nt d s head v dv sc₀ O T Q₀ τ' ∧
        τ'.vars "j" = O (v + 1))
      (48 * Csr.rowLen O v + 4) := by
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  refine Csr.rowScan_spec B (48 * Csr.rowLen O v + 4) (O (v + 1)) 44
    "j" "jend" scanSlotPar (ScanInvParM G M nt d s head v dv sc₀ O T Q₀)
    (by omega) (fun σ hσ => ?_) (fun σ hσ hlt => ?_)
    (fun _ hσ => hσ.1) (fun σ hσ => by rw [hσ.2]; omega)
  · obtain ⟨D, Q, P, -, -, -, -, -, -, -, -, -, hje, -, hjle, -, -, -⟩ := hσ
    exact ⟨hje, hjle⟩
  · obtain ⟨σ', K', hr, hK, hI', hj'⟩ :=
      scanSlotParM_run hcsr hnB hnsB hnt hdB hMB hv hsc₀ hσ hlt
    exact ⟨σ', K', hr, hI', hj', hK⟩

/-! ### Emptying the queue -/

/-- The parent search loop at the narrowed frontier. -/
def DrainInvParM {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ → ℕ)
    (nt d s : ℕ) (O T : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ D Q P, SearchEnvPar n nt s O T M D Q P τ ∧
    ParFrontierM G M d s D Q P (τ.vars "head") (τ.vars "tail") ∧
    τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen O (Q i)

/-- Take one vertex off the queue and scan its whole adjacency block. -/
theorem expandRowParM_run {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B)
    (hMB : ∀ z < n, M z < B) {D Q P : ℕ → ℕ} {τ : Env}
    (hse : SearchEnvPar n nt s O T M D Q P τ)
    (hF : ParFrontierM G M d s D Q P (τ.vars "head") (τ.vars "tail"))
    (hht : τ.vars "head" < τ.vars "tail")
    (hsum : τ.vars "sc" = ∑ i ∈ Finset.range (τ.vars "head"), Csr.rowLen O (Q i)) :
    ∃ τ' K, Run B expandRowPar τ τ' K ∧
      K ≤ 48 * Csr.rowLen O (Q (τ.vars "head")) + 30 ∧
      DrainInvParM G M nt d s O T τ' ∧
      τ'.vars "head" = τ.vars "head" + 1 ∧
      τ'.vars "sc" = τ.vars "sc" + Csr.rowLen O (Q (τ.vars "head")) := by
  obtain ⟨⟨hn, hsrc, hoff, htgt, halv, hdist, hq⟩, hpar⟩ := id hse
  have htln := hF.base.tl
  have hhn : τ.vars "head" < n := by omega
  obtain ⟨v, hvdef⟩ : ∃ v, Q (τ.vars "head") = v := ⟨_, rfl⟩
  rw [hvdef]
  obtain ⟨hvn, hdvd, hmv⟩ := hF.base.qmem _ hht
  rw [hvdef] at hvn hdvd hmv
  have hrow : Csr.rowLen O v = O (v + 1) - O v := rfl
  have hns : O (v + 1) ≤ ns := hcsr.le_ns (by omega)
  have hov : O v ≤ O (v + 1) := hcsr.mono v hvn
  have hsc₀ : τ.vars "sc" + Csr.rowLen O v ≤ ns := by
    have hstep : ∑ i ∈ Finset.range (τ.vars "head" + 1), Csr.rowLen O (Q i) ≤ ns :=
      hcsr.sum_rowLen_queue (fun i hi => (hF.base.qmem i (by omega)).1)
        (fun i hi j hj hqe => hF.base.qinj i (by omega) j (by omega) hqe)
    rw [Finset.sum_range_succ, hvdef] at hstep
    omega
  have hcsrRel : CsrWide.CsrW "off" "tgt" n ns nt n O T τ :=
    ⟨hoff, htgt, fun i hi => hcsr.mono i hi, hcsr.last, hnt,
      fun p hp => hcsr.target_lt p hp⟩
  have hrv : (τ.arrs "q").getD (τ.vars "head") 0 = v := by
    rw [hq, getD_arrOf Q hhn, hvdef]
  have hrv' : (τ.arrs "q")[τ.vars "head"]?.getD 0 = v := by
    rw [← List.getD_eq_getElem?_getD]
    exact hrv
  have hqlen : τ.vars "head" < (τ.arrs "q").length := by
    rw [hq, length_arrOf]
    omega
  have hvB : (τ.arrs "q").getD (τ.vars "head") 0 < B := by rw [hrv]; omega
  have hdlen :
      ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") <
        ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").length := by
    rw [arrs_setVar, vars_setVar, hdist, length_arrOf]
    simpa [hrv'] using hvn
  have hdval :
      ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
        ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0 = D v := by
    rw [arrs_setVar, vars_setVar]
    simp only [hrv, hdist]
    exact getD_arrOf D hvn
  have hdval' :
      (τ.arrs "dist")[(τ.arrs "q")[τ.vars "head"]?.getD 0]?.getD 0 = D v := by
    rw [hrv', ← List.getD_eq_getElem?_getD, hdist, getD_arrOf D hvn]
  have hdB' :
      ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
        ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0 < B := by
    rw [hdval]
    omega
  have hdvB :
      ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).setVar "dv"
        (((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).arrs "dist").getD
          ((τ.setVar "v" ((τ.arrs "q").getD (τ.vars "head") 0)).vars "v") 0)).vars
        "dv" = D v := by
    simp [hdval']
  have hheadB : τ.vars "head" + 1 < B := by omega
  have hscanSpec : Spec B
      (fun σ => ScanInvParM G M nt d s (τ.vars "head") v (D v) (τ.vars "sc") O T Q σ ∧
        σ.vars "j" = O v)
      (Csr.scan "j" "jend" scanSlotPar)
      (fun _ σ' =>
        DrainInvParM G M nt d s O T (σ'.setVar "head" (τ.vars "head" + 1)) ∧
        σ'.vars "head" = τ.vars "head" ∧
        σ'.vars "sc" = τ.vars "sc" + Csr.rowLen O v ∧ σ'.vars "head" + 1 < B)
      (48 * Csr.rowLen O v + 4) :=
    (scanParM_spec hcsr hnB hnsB hnt hdB hMB hvn hsc₀ (Q₀ := Q)).post
      fun _ σ' _ hQ => by
        obtain ⟨⟨D', Q', P', hse', hF', hhead', hht', hqv', hDv', hvv', hdvv',
          hdnv', hje', hjge', hjle', hsc', hscanned, hq₀'⟩, hj₄⟩ := hQ
        obtain ⟨⟨hn', hsrc', hoff', htgt', halv', hdist', hq'⟩, hpar'⟩ := id hse'
        have hscv : σ'.vars "sc" = τ.vars "sc" + Csr.rowLen O v := by
          rw [hsc', hj₄, hrow]
        refine ⟨⟨D', Q', P',
          ⟨⟨by simp [hn'], by simp [hsrc'], by simp [hoff'], by simp [htgt'],
              by simp [halv'], by simp [hdist'], by simp [hq']⟩, by simp [hpar']⟩,
            ?_, ?_⟩, hhead', hscv, by omega⟩
        · refine ⟨⟨hF'.base.cap, hF'.base.src, hF'.base.sound, by simp; omega,
            by simpa using hF'.base.tl, by simpa using hF'.base.qmem,
            by simpa using hF'.base.qall, by simpa using hF'.base.qinj,
            by simpa using hF'.base.qmono, ?_, ?_⟩,
            hF'.root, hF'.pdist, hF'.padj⟩
          · intro i hi j hj₁ hj₂
            simp at hi hj₁ hj₂
            exact hF'.base.qcap i hi j (by omega) hj₂
          · intro i hi z hz
            simp at hi
            rcases Nat.lt_or_ge i (τ.vars "head") with hlt | hge
            · exact hF'.base.exp i hlt z hz
            · have hie : i = τ.vars "head" := by omega
              subst hie
              rw [hqv'] at hz ⊢
              rw [hDv']
              obtain ⟨j', hj'₁, hj'₂, hj'₃⟩ := hcsr.slot_of_madj hz
              rw [← hj'₃]
              exact hscanned j' hj'₁ (by rw [hj₄]; exact hj'₂)
                (by rw [hj'₃]; exact hz.alive_right)
        · show σ'.vars "sc" =
            ∑ i ∈ Finset.range (τ.vars "head" + 1), Csr.rowLen O (Q' i)
          rw [Finset.sum_range_succ,
            Finset.sum_congr rfl fun i hi => by rw [hq₀' i (Finset.mem_range.1 hi)],
            ← hsum, hqv', hscv]
  run_vcg [CsrWide.loadRow_spec B n ns nt n "off" "tgt" "v" "j" "jend" O T
      (by decide) (by decide), hscanSpec]
  · simp_all
  · exact ⟨⟨by simpa using hcsrRel, by omega, hnsB⟩,
      by simp [hrv']; omega, by simp [hrv']; omega⟩
  · obtain ⟨-, -, -, rfl⟩ :=
      ‹CsrWide.LoadRowPostW "off" "tgt" "v" "j" "jend" n ns nt n O T _ _›
    refine ⟨⟨D, Q, P,
      ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt],
          by simp [halv], by simp [hdist], by simp [hq]⟩, by simp [hpar]⟩,
      by simpa using hF, by simp, by simpa using hht, hvdef, rfl, by simp [hrv'],
      by simp [hdval'], by simp [hdval'], by simp [hrv'], by simp [hrv'],
      by simpa [hrv'] using hov, by simp [hrv'], ?_, fun i _ => rfl⟩,
      by simp [hrv']⟩
    intro j' h₁ h₂ h₃
    simp [hrv'] at h₂
    omega

/-- Drain the parent-recording queue while charging only the containing
ball's block weight and cardinality. -/
theorem drainParM_ball {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B)
    (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb)
    {τ : Env} (hI : DrainInvParM G M nt d s O T τ) :
    ∃ τ' K, Run B bfsParDrain τ τ' K ∧ DrainInvParM G M nt d s O T τ' ∧
      τ'.vars "head" = τ'.vars "tail" ∧
      K + BallPotPar bw nb τ' ≤ BallPotPar bw nb τ + 4 := by
  refine Queue.drain_run B n n "q" "head" "tail" expandRowPar
    (DrainInvParM G M nt d s O T) (BallPotPar bw nb) (fun σ hσ => ?_) hnB
      (fun σ hσ hlt => ?_) hI
  · obtain ⟨D₁, Q₁, P₁, ⟨⟨-, -, -, -, -, -, hq⟩, -⟩, hFr, -⟩ := hσ
    exact ⟨Q₁, σ.vars "head", σ.vars "tail", hq, rfl, rfl,
      hFr.base.hd, hFr.base.tl, fun i hi => (hFr.base.qmem i hi).1⟩
  · obtain ⟨D₁, Q₁, P₁, hse, hFr, hsum⟩ := hσ
    obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ :=
      expandRowParM_run hcsr hnB hnsB hnt hdB hMB hse hFr hlt hsum
    refine ⟨σ', K, hrun, hI', ?_⟩
    obtain ⟨D₂, Q₂, P₂, -, hFr', hsum'⟩ := hI'
    have hsc₂ : σ'.vars "sc" ≤ bw := by
      rw [hsum']
      exact le_trans (sum_rowLen_head_leM hFr'.base hFr'.base.hd hA) hbw
    have htail₂ : σ'.vars "tail" ≤ nb :=
      le_trans (tail_le_cardM hFr'.base hA) hnb
    have hsc₁ : σ.vars "sc" ≤ bw := by
      rw [hsum]
      exact le_trans (sum_rowLen_head_leM hFr.base hFr.base.hd hA) hbw
    have htail₁ : σ.vars "tail" ≤ nb :=
      le_trans (tail_le_cardM hFr.base hA) hnb
    have hhd := hFr'.base.hd
    have hhd₀ := hFr.base.hd
    simp only [BallPotPar]
    omega

/-! ### Seed and reusable engine -/

/-- Seed a live source into a distance array that is clean only on the
current mask. -/
theorem seedSrcParM_run {B : ℕ} (hs : s < n) (hms : M s ≠ 0) (hnB : n < B)
    (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B) {g g' g'' : ℕ → ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hsrc : σ.vars "src" = s)
    (hoff : σ.arrs "off" = arrOf (n + 1) O) (htgt : σ.arrs "tgt" = arrOf nt T)
    (halv : σ.arrs "alv" = arrOf n M) (hdist : σ.arrs "dist" = arrOf n g)
    (hgd : ∀ j < n, M j ≠ 0 → g j = d + 1)
    (hq : σ.arrs "q" = arrOf n g') (hpar : σ.arrs "par" = arrOf n g'') :
    ∃ σ' K, Run B seedSrcPar σ σ' K ∧ K ≤ 24 ∧
      DrainInvParM G M nt d s O T σ' ∧ σ'.vars "head" = 0 ∧ σ'.vars "sc" = 0 := by
  have hsB : σ.vars "src" < B := by rw [hsrc]; omega
  have hdlen : σ.vars "src" < (σ.arrs "dist").length := by
    rw [hdist, length_arrOf, hsrc]
    exact hs
  have hplen : σ.vars "src" < (σ.arrs "par").length := by
    rw [hpar, length_arrOf, hsrc]
    exact hs
  have hqlen : (σ.arrs "q").length = n := by rw [hq, length_arrOf]
  have halvlen : (σ.arrs "alv").length = n := by rw [halv, length_arrOf]
  have halvv : (σ.arrs "alv").getD (σ.vars "src") 0 = M s := by
    rw [halv, hsrc, getD_arrOf M hs]
  have halvv' : (σ.arrs "alv")[σ.vars "src"]?.getD 0 = M s := by
    rw [← List.getD_eq_getElem?_getD]
    exact halvv
  have hMs : M s < B := hMB s hs
  have hpos : 0 < M s := Nat.pos_of_ne_zero hms
  run_vcg
  · refine ⟨⟨upd g s 0, upd g' 0 s, upd g'' s s,
      ⟨⟨by simp [hn], by simp [hsrc], by simp [hoff], by simp [htgt], by simp [halv],
          by simp [hdist, hsrc, set_arrOf_eq_upd],
          by simp [hq, hsrc, set_arrOf_eq_upd]⟩,
        by simp [hpar, hsrc, set_arrOf_eq_upd]⟩, ?_, by simp⟩, by simp, by simp⟩
    have hF := ParFrontierM.seed_alive G M d hs hms (p := g'') hgd (upd_self g' 0 s)
    simpa using hF
  · omega

/-- Parent-recording breadth-first search on one live mask, retaining a
shortest-path tree while restoring the distance scratch on that mask. -/
theorem bfsBlockParM_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n)
    (hms : M s ≠ 0) (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt)
    (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs "alv" = arrOf n M ∧ DistClean n d M σ ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g) ∧
        (∃ g, σ.arrs "par" = arrOf n g))
      (bfsBlockParCom d)
      (fun _ σ' => DistClean n d M σ' ∧
        ∃ D P, σ'.arrs "par" = arrOf n P ∧ ParTree G M d s D P)
      (bfsBlockParK bw nb) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hsrc, hoff, htgt, halv, ⟨D₀, hdist, hclean⟩,
    ⟨g₁, hq⟩, ⟨g₂, hqd⟩, ⟨g₃, hpar⟩⟩ := hσ
  obtain ⟨σ₁, K₁, hrun₁, hK₁, hI₁, hhead₁, hsc₁⟩ :=
    seedSrcParM_run (G := G) (O := O) (T := T) (nt := nt) hs hms hnB hdB hMB
      hn hsrc hoff htgt halv hdist hclean hq hpar
  obtain ⟨σ₂, K₂, hrun₂, hI₂, hhead₂, hpay⟩ :=
    drainParM_ball hcsr hnB hnsB hnt hdB hMB hA hbw hnb hI₁
  obtain ⟨D, Q, P, ⟨⟨hn₂, hsrc₂, hoff₂, htgt₂, halv₂, hdist₂, hq₂⟩, hpar₂⟩,
    hFr₂, -⟩ := hI₂
  rw [hhead₂] at hFr₂
  have hqd₂ : σ₂.arrs "qd" = arrOf n g₂ := by
    rw [hrun₂.frame_arr "qd" (by
        simp [bfsParDrain, expandRowPar, scanSlotPar, Csr.loadRow, Csr.scan,
          Queue.drain, Com.warrs]),
      hrun₁.frame_arr "qd" (by simp [seedSrcPar, Com.warrs])]
    exact hqd
  have htl : σ₂.vars "tail" ≤ n := hFr₂.base.tl
  have hqn : ∀ i, i < σ₂.vars "tail" → Q i < n :=
    fun i hi => (hFr₂.base.qmem i hi).1
  have hqm : ∀ i, i < σ₂.vars "tail" → M (Q i) ≠ 0 :=
    fun i hi => (hFr₂.base.qmem i hi).2.2
  have hDd : ∀ z, z < n → M z ≠ 0 → D z ≤ d + 1 := hFr₂.base.cap
  have hdisc₀ : ∀ z, z < n → M z ≠ 0 → D z ≤ d →
      z = s ∨ ∃ j, j < σ₂.vars "tail" ∧ Q j = z := by
    intro z hz hmz hzd
    obtain ⟨i, hi, hqi⟩ := hFr₂.base.qall z hz hmz hzd
    exact Or.inr ⟨i, hi, hqi⟩
  have hTree : ParTree G M d s (ParFrontierM.ghostDist d M D) P :=
    hFr₂.tree hs hms
  obtain ⟨σ₃, K₃, hrun₃, hK₃, hdist₃, hq₃, QD, hqd₃, hcopy₃⟩ :=
    unwindM_run (O := O) (T := T) (nt := nt) (M := M) hs hnB hdB htl hqn hqm
      (fun i hi j hj => hFr₂.base.qinj i hi j hj) hDd hdisc₀ hn₂ hsrc₂ rfl
      hoff₂ htgt₂ halv₂ hdist₂ hq₂ hqd₂
  have hpar₃ : σ₃.arrs "par" = arrOf n P := by
    rw [hrun₃.frame_arr "par" (by simp [unwind, unwindSlot, Csr.scan, Com.warrs])]
    exact hpar₂
  obtain ⟨D₁, Q₁, P₁, -, hFr₁, -⟩ := hI₁
  have htail₁ : σ₁.vars "tail" ≤ nb :=
    le_trans (tail_le_cardM hFr₁.base hA) hnb
  have htail₂ : σ₂.vars "tail" ≤ nb :=
    le_trans (tail_le_cardM hFr₂.base hA) hnb
  have hpot₁ : BallPotPar bw nb σ₁ = 48 * bw + 44 * nb := by
    simp only [BallPotPar, hhead₁, hsc₁]
    omega
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_, le_rfl,
    hdist₃, ParFrontierM.ghostDist d M D, P, hpar₃, hTree⟩
  rw [hpot₁] at hpay
  simp only [bfsBlockParK]
  omega

/-- The mask-scoped parent engine at the pinned target-array width. -/
theorem bfsBlockParM_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n)
    (hms : M s ≠ 0) (hnB : n < B) (hnsB : ns < B)
    (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧ DistClean n d M σ ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g) ∧
        (∃ g, σ.arrs "par" = arrOf n g))
      (bfsBlockParCom d)
      (fun _ σ' => DistClean n d M σ' ∧
        ∃ D P, σ'.arrs "par" = arrOf n P ∧ ParTree G M d s D P)
      (bfsBlockParK bw nb) :=
  bfsBlockParM_specW hcsr hs hms hnB hnsB le_rfl hdB hMB hA hbw hnb

end Lax3Proofs.Refine.BfsBlockParMask
