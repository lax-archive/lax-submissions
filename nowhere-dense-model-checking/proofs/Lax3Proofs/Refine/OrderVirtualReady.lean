import Lax3Proofs.Refine.OrderVirtualInit
import Lax3Proofs.Refine.OrderVirtualBucket

/-!
# Entering virtual elimination

The regenerated-degree pass and the compact bucket rebuild meet here.  The
result is the ordinary mathematical Matula--Beck invariant together with a
carrier-linear resident machine state.  In particular, the rebuilt bucket
relation is weakened from the all-zero elimination mask to the actual mask;
the other elimination arrays and the provider's persistent memory are framed
through the rebuild.
-/

namespace Lax3Proofs.Refine.OrderVirtualReady

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamElim (Elim Buck BuckInv)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualInit
open Lax3Proofs.Refine.OrderVirtualBucket

/-- The initialized state at the exact linear arena width.  The loop scalars
are deliberately not fixed here: the elimination driver initializes them in
its prologue. -/
def VirtualReady (n : ℕ) (G : SimpleGraph (Fin n)) (P : Env → Prop)
    (σ : Env) : Prop :=
  P σ ∧
    ∃ E D R ID BH BV BN,
      EngineArrays n (bucketExtra n) E D R ID BH BV BN σ ∧
      Elim G (fun _ => 1) E D R ID 0 0 0 ∧
      Buck n n E D BH BV BN (σ.vars "sp") (σ.vars "ls") ∧
      (∀ u < n, D u < n) ∧
      σ.vars "i" = n ∧ σ.vars "sp" = n + 1 ∧ σ.vars "ls" = n

private theorem rebuild_wvars_engine :
    ∀ a ∈ rebuildBuckets.wvars, a ∈ engineVarNames := by
  intro a ha
  simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
    Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
    Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put,
    Com.wvars, engineVarNames] at ha ⊢
  tauto

private theorem rebuild_warrs_engine :
    ∀ a ∈ rebuildBuckets.warrs, a ∈ engineArrNames := by
  intro a ha
  simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
    Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
    Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put,
    Com.warrs, engineArrNames] at ha ⊢
  tauto

/-- Rebuilding after the regenerated-degree pass establishes the complete
initial elimination state without changing provider memory or the three
non-degree elimination arrays. -/
theorem rebuild_after_virtual_deg {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} (hclosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B) :
    Spec B
      (fun σ => VirtualDegInv n (bucketExtra n) G P σ ∧ σ.vars "i" = n)
      rebuildBuckets
      (fun _ σ' => VirtualReady n G P σ')
      (rebuildBucketsCost n) := by
  intro σ hpre
  obtain ⟨⟨hP, hile, E, D, R, ID, BH, BV, BN, heng, hzero, hdone⟩, hi⟩ := hpre
  have helim : Elim G (fun _ => 1) E D R ID 0 0 0 :=
    Lax3Proofs.RamElim.Elim.init hzero (by
      intro v
      have hd := hdone (v : ℕ) (by rw [hi]; exact v.isLt)
      rw [virtualDegree_eq v.isLt] at hd
      rw [Lax3Proofs.RamElim.masked_of_all_alive G (by simp)]
      exact hd)
  have hD : ∀ v < n, D v < n := by
    intro v hv
    exact helim.deg_lt hv (hzero v hv)
  obtain ⟨σ', hr, hbuckI, hi'⟩ :=
    (rebuildBuckets_spec (B := B) (n := n) (W := bucketExtra n)
      (by omega) hD).run
      ⟨heng.n_eq, heng.deg_eq, ⟨BH, heng.head_eq⟩,
        ⟨BV, heng.val_eq⟩, ⟨BN, heng.next_eq⟩⟩
  obtain ⟨hn', hdeg', hile', hsp', hls', BH', BV', BN',
    hbh', hbv', hbn', hbuck0⟩ := hbuckI
  have hP' : P σ' := hclosed hr rebuild_wvars_engine rebuild_warrs_engine hP
  have helm' : σ'.arrs "elm" = arrOf n E := by
    rw [hr.frame_arr "elm" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.warrs])]
    exact heng.elm_eq
  have hrnk' : σ'.arrs "rnk" = arrOf n R := by
    rw [hr.frame_arr "rnk" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.warrs])]
    exact heng.rank_eq
  have hidg' : σ'.arrs "idg" = arrOf n ID := by
    rw [hr.frame_arr "idg" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.warrs])]
    exact heng.idg_eq
  refine ⟨σ', hr, hP', E, D, R, ID, BH', BV', BN', ?_, helim,
    ?_, hD, hi', ?_, ?_⟩
  · exact ⟨hn', helm', hdeg', hrnk', hidg', hbh', hbv', hbn'⟩
  · simpa [hi'] using hbuck0.weaken E
  · omega
  · omega

/-! ## Axiom audit -/

#print axioms rebuild_after_virtual_deg

end Lax3Proofs.Refine.OrderVirtualReady
