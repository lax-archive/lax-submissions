import Lax3Proofs.RamBfsPaths
import Lax3Proofs.Refine.BfsBlock

/-!
The parent-recording breadth-first search, charged to the block that contains
its ball.

`RamBfsPaths.bfsParCom` records exactly the shortest-path tree the splitter
driver needs, but its initial carrier fill and carrier-sized potential make it
unsuitable inside every cover turn.  `BfsBlock` already removes both costs for
the non-parent search: the distance array enters clean, the queue is charged to
the ball, and an unwind restores every touched cell.  This file performs the
same assembly around the landed parent-recording seed and drain.

The parent array is not unwound.  Its useful exit reading is independent of the
scratch distance array: there exists a distance labelling with which it is a
`RamBfsPaths.ParTree`.  Thus the distance scratch is reusable immediately while
the tree remains available to later descendants.
-/

namespace Lax3Proofs.Refine.BfsBlockPar

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamBfsPaths
open Lax3Proofs.Refine.BfsBlock

variable {n ns nt d s : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}

/-! ### Program and charge -/

/-- Parent-recording search with no carrier fill and with the block-engine
unwind restoring the distance scratch. -/
def bfsBlockParCom (d : ℕ) : Com :=
  .seq seedSrcPar (.seq bfsParDrain (unwind d))

/-- The parent store adds four units per scanned slot and four units per
queued vertex to `BfsBlock.bfsBlockK`. -/
def bfsBlockParK (bw nb : ℕ) : ℕ := 48 * bw + 84 * nb + 64

theorem bfsBlockParK_mono {bw bw' nb nb' : ℕ} (hb : bw ≤ bw') (hn : nb ≤ nb') :
    bfsBlockParK bw nb ≤ bfsBlockParK bw' nb' := by
  simp only [bfsBlockParK]
  omega

/-! ### The parent drain, charged to the ball -/

/-- The parent-search potential with the carrier bounds replaced by the
caller's ball weight and cardinality. -/
def BallPotPar (bw nb : ℕ) (τ : Env) : ℕ :=
  48 * (bw - τ.vars "sc") + 44 * (nb - τ.vars "tail") +
    44 * (τ.vars "tail" - τ.vars "head")

/-- Empty the parent-recording queue while paying only for a finite set that
contains the searched ball. -/
theorem drainPar_ball {B : ℕ} (hcsr : CsrGraph G ns O T) (hnB : n < B) (hnsB : ns < B)
    (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb)
    {τ : Env} (hI : DrainInvPar G M nt d s O T τ) :
    ∃ τ' K, Run B bfsParDrain τ τ' K ∧ DrainInvPar G M nt d s O T τ' ∧
      τ'.vars "head" = τ'.vars "tail" ∧
      K + BallPotPar bw nb τ' ≤ BallPotPar bw nb τ + 4 := by
  refine Queue.drain_run B n n "q" "head" "tail" expandRowPar
    (DrainInvPar G M nt d s O T) (BallPotPar bw nb) (fun σ hσ => ?_) hnB
      (fun σ hσ hlt => ?_) hI
  · obtain ⟨D₁, Q₁, P₁, ⟨⟨-, -, -, -, -, -, hq⟩, -⟩, hFr, -⟩ := hσ
    exact ⟨Q₁, σ.vars "head", σ.vars "tail", hq, rfl, rfl, hFr.base.hd,
      hFr.base.tl, fun i hi => (hFr.base.qmem i hi).1⟩
  · obtain ⟨D₁, Q₁, P₁, hse, hFr, hsum⟩ := hσ
    obtain ⟨σ', K, hrun, hK, hI', hhead', hsc'⟩ :=
      expandRowPar_run hcsr hnB hnsB hnt hdB hMB hse hFr hlt hsum
    refine ⟨σ', K, hrun, hI', ?_⟩
    obtain ⟨D₂, Q₂, P₂, -, hFr', hsum'⟩ := hI'
    set r := Csr.rowLen O (Q₁ (σ.vars "head")) with hr
    have hsc₂ : σ'.vars "sc" ≤ bw := by
      rw [hsum']
      exact le_trans (sum_rowLen_head_le hFr'.base hFr'.base.hd hA) hbw
    have htail₂ : σ'.vars "tail" ≤ nb :=
      le_trans (tail_le_card hFr'.base hA) hnb
    have hsc₁ : σ.vars "sc" ≤ bw := by
      rw [hsum]
      exact le_trans (sum_rowLen_head_le hFr.base hFr.base.hd hA) hbw
    have htail₁ : σ.vars "tail" ≤ nb :=
      le_trans (tail_le_card hFr.base hA) hnb
    have hhd := hFr'.base.hd
    have hhd₀ := hFr.base.hd
    simp only [BallPotPar]
    omega

/-! ### The reusable parent-tree engine -/

/-- Search one block-sized ball, retain its shortest-path parent tree, and
restore the distance scratch to the sentinel everywhere.  The ghost distance
labelling in the postcondition is the one present just before the unwind; only
the parent array remains materialised. -/
theorem bfsBlockPar_specW {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hnt : ns ≤ nt) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs "alv" = arrOf n M ∧ σ.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g) ∧
        (∃ g, σ.arrs "par" = arrOf n g))
      (bfsBlockParCom d)
      (fun _ σ' => σ'.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        ∃ D P, σ'.arrs "par" = arrOf n P ∧ ParTree G M d s D P)
      (bfsBlockParK bw nb) := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hn, hsrc, hoff, htgt, halv, hdist, ⟨g₁, hq⟩, ⟨g₂, hqd⟩, ⟨g₃, hpar⟩⟩ := hσ
  obtain ⟨σ₁, K₁, hrun₁, hK₁, hI₁, hhead₁, hsc₁⟩ :=
    seedSrcPar_run (G := G) (O := O) (T := T) (nt := nt) hs hnB hdB hMB hn hsrc hoff htgt
      halv hdist (fun _ _ => rfl) hq hpar
  obtain ⟨σ₂, K₂, hrun₂, hI₂, hhead₂, hpay⟩ :=
    drainPar_ball hcsr hnB hnsB hnt hdB hMB hA hbw hnb hI₁
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
  have hDd : ∀ z, z < n → D z ≤ d + 1 := hFr₂.base.cap
  have hdisc₀ : ∀ z, z < n → D z ≤ d →
      z = s ∨ ∃ j, j < σ₂.vars "tail" ∧ Q j = z := by
    intro z hz hzd
    by_cases hmz : M z = 0
    · refine Or.inl ?_
      by_contra hzs
      exact alive_of_wd (hFr₂.base.sound z hz hzd) (Ne.symm hzs) hmz
    · obtain ⟨i, hi, hqi⟩ := hFr₂.base.qall z hz hmz hzd
      exact Or.inr ⟨i, hi, hqi⟩
  have hTree : ParTree G M d s D P := hFr₂.tree
  obtain ⟨σ₃, K₃, hrun₃, hK₃, hdist₃, hq₃, QD, hqd₃, hcopy₃⟩ :=
    unwind_run (O := O) (T := T) (nt := nt) (M := M) hs hnB hdB htl hqn
      (fun i hi j hj => hFr₂.base.qinj i hi j hj) hDd hdisc₀ hn₂ hsrc₂ rfl hoff₂ htgt₂
      halv₂ hdist₂ hq₂ hqd₂
  have hpar₃ : σ₃.arrs "par" = arrOf n P := by
    rw [hrun₃.frame_arr "par" (by simp [unwind, unwindSlot, Csr.scan, Com.warrs])]
    exact hpar₂
  obtain ⟨D₁, Q₁, P₁, -, hFr₁, -⟩ := hI₁
  have htail₁ : σ₁.vars "tail" ≤ nb :=
    le_trans (tail_le_card hFr₁.base hA) hnb
  have htail₂ : σ₂.vars "tail" ≤ nb :=
    le_trans (tail_le_card hFr₂.base hA) hnb
  have hpot₁ : BallPotPar bw nb σ₁ = 48 * bw + 44 * nb := by
    simp only [BallPotPar, hhead₁, hsc₁]
    omega
  refine ⟨σ₃, _, (hrun₁.seq (hrun₂.seq hrun₃)).mono ?_, le_rfl, hdist₃,
    D, P, hpar₃, hTree⟩
  rw [hpot₁] at hpay
  simp only [bfsBlockParK]
  omega

/-- The engine at the pinned target-array width. -/
theorem bfsBlockPar_spec {B : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n) (hnB : n < B)
    (hnsB : ns < B) (hdB : d + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ} (hA : ∀ v, v < n → M v ≠ 0 → WD G M d s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf ns T ∧
        σ.arrs "alv" = arrOf n M ∧ σ.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g) ∧
        (∃ g, σ.arrs "par" = arrOf n g))
      (bfsBlockParCom d)
      (fun _ σ' => σ'.arrs "dist" = arrOf n (fun _ => d + 1) ∧
        ∃ D P, σ'.arrs "par" = arrOf n P ∧ ParTree G M d s D P)
      (bfsBlockParK bw nb) :=
  bfsBlockPar_specW hcsr hs hnB hnsB le_rfl hdB hMB hA hbw hnb

theorem bfsBlockParK_le_weight (s ds : ℕ) :
    bfsBlockParK ds s ≤ 84 * (s + ds + 1) := by
  simp only [bfsBlockParK]
  omega

end Lax3Proofs.Refine.BfsBlockPar
