import Lax3Proofs.Refine.OrderVirtualEnsure
import Lax3Proofs.Refine.OrderVirtualTurn

/-!
# Amortising the virtual greedy eliminator

The provider regenerates a row only when its vertex is extracted.  We put the
whole future provider charge, together with enough credit for the bucket
insertions caused by that row, on each live vertex.  Separate credits pay for
degree-pointer bumps, stale bucket entries, and occasional compaction of the
fixed linear bucket arena.
-/

namespace Lax3Proofs.Refine.OrderVirtualPotential

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualInit (virtualDegree)
open Lax3Proofs.Refine.OrderVirtualBucket (bucketExtra rebuildBucketsCost)
open Lax3Proofs.Refine.OrderVirtualEnsure
open Lax3Proofs.Refine.OrderVirtualTurn

/-- Credit carried by a vertex until the unique turn that extracts it. -/
noncomputable def rowCredit {n : ℕ} (G : SimpleGraph (Fin n))
    (κ : ℕ → ℕ) (v : ℕ) : ℕ :=
  κ v + 300 * virtualDegree G v + 300

/-- The mathematical presentation of the credits on live vertices. -/
noncomputable def remainingBy {n : ℕ} (G : SimpleGraph (Fin n))
    (κ E : ℕ → ℕ) : ℕ :=
  ∑ v ∈ Finset.range n, if E v = 0 then rowCredit G κ v else 0

/-- The same credit, read directly from the resident elimination mask. -/
noncomputable def remainingCredit {n : ℕ} (G : SimpleGraph (Fin n)) (κ : ℕ → ℕ)
    (σ : Env) : ℕ :=
  ∑ v ∈ Finset.range n,
    if (σ.arrs "elm").getD v 0 = 0 then rowCredit G κ v else 0

/-- Global potential for a virtual elimination. -/
noncomputable def virtualPot {n : ℕ} (G : SimpleGraph (Fin n)) (κ : ℕ → ℕ)
    (σ : Env) : ℕ :=
  80 * (n + 1 - σ.vars "mind") + 80 * σ.vars "ls" +
    150 * σ.vars "sp" + remainingCredit G κ σ

theorem remainingBy_upd_one {n : ℕ} {G : SimpleGraph (Fin n)}
    {κ E : ℕ → ℕ} {w : ℕ} (hw : w < n) (hE : E w = 0) :
    remainingBy G κ (upd E w 1) + rowCredit G κ w = remainingBy G κ E := by
  classical
  let s := Finset.range n
  let f : ℕ → ℕ := fun v => if E v = 0 then rowCredit G κ v else 0
  let g : ℕ → ℕ := fun v => if upd E w 1 v = 0 then rowCredit G κ v else 0
  have hws : w ∈ s := by simpa [s] using hw
  have herase : ∑ v ∈ s.erase w, g v = ∑ v ∈ s.erase w, f v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hvw : v ≠ w := Finset.ne_of_mem_erase hv
    simp [f, g, upd_of_ne _ hvw]
  have hg := Finset.sum_erase_add s g hws
  have hf := Finset.sum_erase_add s f hws
  have hgw : g w = 0 := by simp [g, upd_self]
  have hfw : f w = rowCredit G κ w := by simp [f, hE]
  simp only [remainingBy, s, f, g] at *
  omega

theorem remainingCredit_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    {κ E : ℕ → ℕ} {σ : Env} (helm : σ.arrs "elm" = arrOf n E) :
    remainingCredit G κ σ = remainingBy G κ E := by
  classical
  apply Finset.sum_congr rfl
  intro v hv
  rw [helm, getD_arrOf E (Finset.mem_range.1 hv)]

theorem remainingCredit_congr {n : ℕ} {G : SimpleGraph (Fin n)}
    {κ : ℕ → ℕ} {σ σ' : Env} (helm : σ'.arrs "elm" = σ.arrs "elm") :
    remainingCredit G κ σ' = remainingCredit G κ σ := by
  simp [remainingCredit, helm]

/-- Every core case pays its own machine cost and leaves nine units for the
capacity guard.  Together with the four-unit while test this is the local
amortised inequality used by the loop rule. -/
theorem virtualCoreEffect_pays {n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {κ E D R ID BH BV BN : ℕ → ℕ} {σ σ' : Env} {K : ℕ}
    (hst : VirtualElimSt n G P E D R ID BH BV BN σ)
    (heff : VirtualCoreEffect n G κ E σ σ' K) :
    K + 13 + virtualPot G κ σ' ≤ virtualPot G κ σ := by
  have hmind : σ.vars "mind" ≤ n := hst.2.2.2.2.2.2.2.1
  rcases heff with hbump | hstale | htake
  · have hK := hbump.cost
    have hrem := remainingCredit_congr (G := G) (κ := κ) hbump.elm_eq
    simp only [virtualPot]
    rw [hrem, hbump.mind_eq, hbump.ls_eq, hbump.sp_eq]
    omega
  · have hK := hstale.cost
    have hlspos := hstale.ls_pos
    have hrem := remainingCredit_congr (G := G) (κ := κ) hstale.elm_eq
    simp only [virtualPot]
    rw [hrem, hstale.mind_eq, hstale.ls_eq, hstale.sp_eq]
    omega
  · obtain ⟨w, hwn, hEw, hK, hsp, hls, hcnt, hmind', hkmax, helm'⟩ := htake
    have helm : σ.arrs "elm" = arrOf n E := hst.2.1.elm_eq
    have hrem0 := remainingCredit_eq (G := G) (κ := κ) helm
    have hrem1 := remainingCredit_eq (G := G) (κ := κ) helm'
    have hdrop := remainingBy_upd_one (G := G) (κ := κ) hwn hEw
    simp only [virtualPot, rowCredit]
    rw [hrem0, hrem1, hmind']
    simp only [rowCredit] at hdrop
    omega

/-- Compaction is fully paid by the drop of the bucket-arena pointer. -/
theorem ensureRebuildEffect_pays {n : ℕ} {G : SimpleGraph (Fin n)}
    {κ : ℕ → ℕ} {σ σ' : Env} {K : ℕ}
    (heff : EnsureRebuildEffect n σ σ' K) :
    K + virtualPot G κ σ' ≤ virtualPot G κ σ := by
  have hK := heff.cost
  have hspLarge := heff.old_sp_large
  have hrem := remainingCredit_congr (G := G) (κ := κ) heff.elm_eq
  simp only [virtualPot]
  rw [hrem, heff.mind_eq, heff.ls_eq, heff.sp_eq]
  simp only [rebuildBucketsCost] at hK
  omega

/-- A complete guarded turn. -/
def virtualTurn (provide : Com) : Com :=
  .seq ensureVirtualBuckets (virtualCoreTurn provide)

/-- One guarded turn preserves the virtual elimination invariant and spends
at least its run cost plus the enclosing while guard from the potential. -/
theorem virtualTurn_run {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n (bucketExtra n) G P provide κ)
    (hclosed : EngineClosed P) (hrunClosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B) {σ : Env}
    (hI : VirtualElimInv n G P σ) (hcnt : σ.vars "cnt" < n) :
    ∃ σ' K, Run B (virtualTurn provide) σ σ' K ∧
      VirtualElimInv n G P σ' ∧
      K + 4 + virtualPot G κ σ' ≤ virtualPot G κ σ := by
  obtain ⟨E, D, R, ID, BH, BV, BN, hst⟩ := hI
  obtain ⟨σ₁, K₁, BH₁, BV₁, BN₁, hr₁, hst₁, hroom, hens⟩ :=
    ensureVirtualBuckets_run hrunClosed hB hst
  have hcnt₁ : σ₁.vars "cnt" < n := by
    rcases hens with hskip | hrebuild
    · rw [hskip.state_eq]
      exact hcnt
    · rw [hrebuild.cnt_eq]
      exact hcnt
  obtain ⟨σ₂, K₂, hr₂, hI₂, hcore⟩ :=
    virtualCoreTurn_run hp hclosed hrunClosed hB hst₁
      hcnt₁ hroom
  have hpayCore := virtualCoreEffect_pays hst₁ hcore
  refine ⟨σ₂, K₁ + K₂, (hr₁.seq hr₂), hI₂, ?_⟩
  rcases hens with hskip | hrebuild
  · have hK₁ := hskip.cost
    rw [hskip.state_eq] at hpayCore
    omega
  · have hpayEnsure := ensureRebuildEffect_pays (G := G) (κ := κ) hrebuild
    omega

/-- All per-vertex credits, including those already spent. -/
noncomputable def totalCredit {n : ℕ} (G : SimpleGraph (Fin n))
    (κ : ℕ → ℕ) : ℕ :=
  ∑ v ∈ Finset.range n, rowCredit G κ v

/-- A uniform cap on the potential of every state satisfying the loop
invariant.  The deliberately round coefficient leaves the later provider
instantiations a simple arithmetic obligation. -/
noncomputable def virtualPotCap {n : ℕ} (G : SimpleGraph (Fin n))
    (κ : ℕ → ℕ) : ℕ :=
  totalCredit G κ + 1000 * (n + 1)

theorem remainingCredit_le_total {n : ℕ} {G : SimpleGraph (Fin n)}
    {κ : ℕ → ℕ} {σ : Env} :
    remainingCredit G κ σ ≤ totalCredit G κ := by
  classical
  apply Finset.sum_le_sum
  intro v hv
  split <;> omega

theorem virtualPot_le_cap {n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {κ : ℕ → ℕ} {σ : Env}
    (hI : VirtualElimInv n G P σ) :
    virtualPot G κ σ ≤ virtualPotCap G κ := by
  obtain ⟨E, D, R, ID, BH, BV, BN,
    hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩ := hI
  have hrem := remainingCredit_le_total (G := G) (κ := κ) (σ := σ)
  simp only [virtualPot, virtualPotCap]
  omega

/-- The guarded turn repeated until all vertices have been ranked. -/
def virtualElimWhile (provide : Com) : Com :=
  .while (.lt (.var "cnt") (.var "n")) (virtualTurn provide)

theorem virtualElimWhile_spec {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n (bucketExtra n) G P provide κ)
    (hclosed : EngineClosed P) (hrunClosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B) :
    Spec B (VirtualElimInv n G P)
      (virtualElimWhile provide)
      (fun _ σ' => VirtualElimInv n G P σ' ∧
        (Cond.lt (.var "cnt") (.var "n")).evalB B σ' = some false)
      (virtualPotCap G κ + 4) := by
  refine Spec.while_potential (VirtualElimInv n G P) (virtualPot G κ)
    ?_ ?_ (fun _ h => h) ?_
  · rintro σ ⟨E, D, R, ID, BH, BV, BN, hst⟩
    have hn : σ.vars "n" = n := hst.2.1.n_eq
    have hcnt : σ.vars "cnt" ≤ n := hst.2.2.1.cnt_le
    exact evalB_condLt_vars (by omega) (by omega)
  · intro σ hI hb
    have hcnt : σ.vars "cnt" < n := by
      obtain ⟨E, D, R, ID, BH, BV, BN, hst⟩ := hI
      have ht := lt_of_condLt_true hb
      rw [hst.2.1.n_eq] at ht
      exact ht
    obtain ⟨σ', K, hr, hI', hpay⟩ :=
      virtualTurn_run hp hclosed hrunClosed hB hI hcnt
    refine ⟨σ', K, hr, hI', ?_⟩
    simp only [Cond.size, Expr.size]
    omega
  · intro σ hI
    have hcap := virtualPot_le_cap (κ := κ) hI
    simp only [Cond.size, Expr.size]
    omega

/-! ## Axiom audit -/

#print axioms remainingBy_upd_one
#print axioms virtualCoreEffect_pays
#print axioms ensureRebuildEffect_pays
#print axioms virtualTurn_run
#print axioms virtualElimWhile_spec

end Lax3Proofs.Refine.OrderVirtualPotential
