import Lax3Proofs.Refine.OrderVirtualStamp

/-!
# Successful virtual extraction

Once the bucket head has been popped and capacity has been guarded, a
successful turn stamps the selected vertex, asks the provider for its exact
row, and scans that row.  The terminal hit/miss facts are fed directly into
the landed mathematical `Elim.extract` theorem.
-/

namespace Lax3Proofs.Refine.OrderVirtualTake

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamElim (Elim Buck)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualInit (virtualDegree virtualDegree_eq)
open Lax3Proofs.Refine.OrderVirtualBucket (bucketExtra)
open Lax3Proofs.Refine.OrderVirtualEnsure
open Lax3Proofs.Refine.OrderVirtualStamp
open Lax3Proofs.Refine.OrderVirtualRowRep
open Lax3Proofs.Refine.OrderVirtualElimScan

def virtualElimVertex (provide : Com) : Com :=
  .seq stampVirtualVertex
    (.seq provide
      (.seq (.assign "j" (.lit 0))
        (.seq decVirtualScan
          (.assign "mind" (.sub (.var "mind") (.lit 1))))))

/-- State after the selected bucket head has been removed, but before the
vertex is stamped.  The bucket relation already uses the future elimination
mask: this is exactly the output of `Buck.pop` for a successful head. -/
structure TakePre (n : ℕ) (G : SimpleGraph (Fin n)) (P : Env → Prop)
    (E D R ID BH BV BN : ℕ → ℕ) (w : Fin n) (σ : Env) : Prop where
  persistent : P σ
  arrays : EngineArrays n (bucketExtra n) E D R ID BH BV BN σ
  elim : Elim G (fun _ => 1) E D R ID
    (σ.vars "cnt") (σ.vars "mind") (σ.vars "kmax")
  buckets : Buck n n (upd E (w : ℕ) 1) D BH BV BN
    (σ.vars "sp") (σ.vars "ls")
  degree_lt : ∀ u < n, D u < n
  w_eq : σ.vars "w" = (w : ℕ)
  count_lt : σ.vars "cnt" < n
  alive : E (w : ℕ) = 0
  minimum : D (w : ℕ) = σ.vars "mind"
  room : σ.vars "sp" < 2 * n + 3
  live_slots : σ.vars "ls" + 1 ≤ σ.vars "sp"
  mind_le : σ.vars "mind" ≤ n
  kmax_le : σ.vars "kmax" ≤ n

private theorem scan_wvars_engine :
    ∀ a ∈ decVirtualScan.wvars, a ∈ engineVarNames := by
  intro a ha
  simp [decVirtualScan, decVirtualSlot, Lax3Proofs.RamElim.push,
    Com.wvars, engineVarNames] at ha ⊢
  tauto

private theorem scan_warrs_engine :
    ∀ a ∈ decVirtualScan.warrs, a ∈ engineArrNames := by
  intro a ha
  simp [decVirtualScan, decVirtualSlot, Lax3Proofs.RamElim.push,
    Com.warrs, engineArrNames] at ha ⊢
  tauto

/-- One selected vertex is eliminated in the exact regenerated graph.  The
charge is the provider's actual row charge plus the actual row cardinality;
no carrier-wide term is introduced. -/
theorem virtualElimVertex_spec {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n (bucketExtra n) G P provide κ)
    (hclosed : EngineClosed P) (hrunClosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B)
    {E D R ID BH BV BN : ℕ → ℕ} {w : Fin n} :
    Spec B
      (TakePre n G P E D R ID BH BV BN w)
      (virtualElimVertex provide)
      (fun σ σ' =>
        VirtualElimInv n G P σ' ∧
        σ'.vars "sp" ≤ σ.vars "sp" + virtualDegree G (w : ℕ) ∧
        σ'.vars "ls" ≤ σ.vars "ls" + virtualDegree G (w : ℕ) ∧
        σ'.vars "cnt" = σ.vars "cnt" + 1 ∧
        σ'.vars "mind" = σ.vars "mind" - 1 ∧
        σ'.vars "kmax" = max (σ.vars "kmax") (σ.vars "mind") ∧
        σ'.arrs "elm" = arrOf n (upd E (w : ℕ) 1))
      (κ (w : ℕ) + 47 * virtualDegree G (w : ℕ) + 33) := by
  intro σ hpre
  obtain ⟨hP, heng, helim, hbuck, hD, hwv, hcnt, hEw, hDw,
    hroom, hls, hmind, hkmax⟩ := hpre
  let cv := σ.vars "cnt"
  let mv := σ.vars "mind"
  let kv := σ.vars "kmax"
  obtain ⟨σ₁, hr₁, hs⟩ :=
    (stampVirtualVertex_spec hclosed hB w.isLt hcnt hmind hkmax).run
      ⟨hP, heng, hwv, rfl, rfl, rfl⟩
  obtain ⟨hP₁, heng₁, hw₁, hcnt₁, hmind₁, hkmax₁,
    hsp₁, hls₁, hi₁⟩ := hs
  obtain ⟨σ₂, hr₂, hP₂, heng₂, hstable, tail, A,
    hrow, htail₂, hrow₂⟩ :=
    (hp w (upd E (w : ℕ) 1) D (upd R (w : ℕ) (n - 1 - cv))
      (upd ID (w : ℕ) mv) BH BV BN).run ⟨hP₁, heng₁, hw₁⟩
  have htailDeg : tail = virtualDegree G (w : ℕ) := by
    rw [virtualDegree_eq w.isLt]
    exact hrow.card_eq
  have hjrun : Run B (.assign "j" (.lit 0)) σ₂ (σ₂.setVar "j" 0) 2 := by
    simpa [Expr.size] using
      (Run.assign (B := B) (σ := σ₂) (x := "j") (evalB_lit (by omega : 0 < B)))
  let σ₃ := σ₂.setVar "j" 0
  have hP₃ : P σ₃ := hclosed.setVar (a := "j") (by simp [engineVarNames]) hP₂
  have hsp₂ : σ₂.vars "sp" = σ.vars "sp" := hstable.sp_eq.trans hsp₁
  have hls₂ : σ₂.vars "ls" = σ.vars "ls" := hstable.ls_eq.trans hls₁
  have hbite : ∀ u < n, upd E (w : ℕ) 1 u ≤ 1 := by
    intro u hu
    by_cases huw : u = (w : ℕ)
    · rw [huw, upd_self]
    · rw [upd_of_ne _ huw]
      exact helim.bit u hu
  have hscanI : ScanInv n (bucketExtra n) tail (σ.vars "sp") (σ.vars "ls")
      A (upd E (w : ℕ) 1)
      (upd R (w : ℕ) (n - 1 - cv)) (upd ID (w : ℕ) mv) D σ₃ := by
    refine ⟨D, BH, BV, BN, ?_, ?_, hbite, hD, ?_, ?_, by simp [σ₃], ?_, ?_, ?_, ?_⟩
    · refine ⟨by simp [σ₃, heng₂.n_eq], by simp [σ₃, htail₂],
        by simp [σ₃, hrow₂], by simp [σ₃, heng₂.elm_eq],
        by simp [σ₃, heng₂.deg_eq], by simp [σ₃, heng₂.rank_eq],
        by simp [σ₃, heng₂.idg_eq], by simp [σ₃, heng₂.head_eq],
        by simp [σ₃, heng₂.val_eq], by simp [σ₃, heng₂.next_eq]⟩
    · simpa [σ₃, hsp₂, hls₂] using hbuck
    · intro u hu hh
      exfalso
      exact (hit_zero (E := upd E (w : ℕ) 1) (A := A) (u := u))
        (by simpa [σ₃] using hh)
    · intro u hu hh
      rfl
    · simpa [σ₃, hsp₂, bucketExtra] using
        room_for_row hrow.tail_le hroom
    · simpa [σ₃, hsp₂, hls₂] using hls
    · simp [σ₃, hsp₂]
    · simp [σ₃, hls₂]
  obtain ⟨σ₄, hr₄, hscan₄, hj₄⟩ :=
    (decVirtualScan_spec hrow (by
      rw [Lax3Proofs.Refine.OrderVirtualBucket.bucket_arena_length]
      exact hB)).run
      ⟨hscanI, by simp [σ₃]⟩
  obtain ⟨D', BH', BV', BN', harr₄, hbuck₄, hbit₄, hD₄,
    hhit₄, hmiss₄, hjle₄, hroom₄, hls₄, hspUsed₄,
    hlsUsed₄⟩ := hscan₄
  rw [hj₄] at hhit₄ hmiss₄ hroom₄ hspUsed₄ hlsUsed₄
  obtain ⟨hdec, hkeep⟩ := extract_of_virtual_scan hrow hhit₄ hmiss₄
  have helim' := helim.extract hcnt w.isLt hEw hDw hdec hkeep
  have hP₄ : P σ₄ := hrunClosed hr₄ scan_wvars_engine scan_warrs_engine hP₃
  have hmind₄ : σ₄.vars "mind" = mv := by
    rw [hr₄.frame_var "mind" (by
      simp [decVirtualScan, decVirtualSlot, Lax3Proofs.RamElim.push, Com.wvars]),
      show σ₃.vars "mind" = mv by
        simpa [σ₃, mv] using hstable.mind_eq.trans hmind₁]
  have hmindB₄ : σ₄.vars "mind" < B := by rw [hmind₄]; omega
  have hsubeval : (Expr.sub (.var "mind") (.lit 1)).evalB B σ₄ = some (mv - 1) := by
    have hb : Lax13Proofs.Imp.Bop.sub.apply (σ₄.vars "mind") 1 < B := by
      simp [Lax13Proofs.Imp.Bop.apply, hmind₄]
      omega
    simpa [hmind₄] using
      (evalB_bin (op := Lax13Proofs.Imp.Bop.sub) (evalB_var hmindB₄)
        (evalB_lit (by omega : 1 < B)) hb)
  let σ₅ := σ₄.setVar "mind" (mv - 1)
  have hr₅ : Run B (.assign "mind" (.sub (.var "mind") (.lit 1))) σ₄ σ₅ 4 := by
    simpa [σ₅, Expr.size] using Run.assign hsubeval
  have hP₅ : P σ₅ := hclosed.setVar (a := "mind") (by simp [engineVarNames]) hP₄
  have hcnt₄ : σ₄.vars "cnt" = cv + 1 := by
    rw [hr₄.frame_var "cnt" (by
      simp [decVirtualScan, decVirtualSlot, Lax3Proofs.RamElim.push, Com.wvars])]
    simpa [σ₃] using hstable.cnt_eq.trans hcnt₁
  have hkmax₄ : σ₄.vars "kmax" = max kv mv := by
    rw [hr₄.frame_var "kmax" (by
      simp [decVirtualScan, decVirtualSlot, Lax3Proofs.RamElim.push, Com.wvars])]
    simpa [σ₃] using hstable.kmax_eq.trans hkmax₁
  refine ⟨σ₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hr₁.seq (hr₂.seq (hjrun.seq (hr₄.seq hr₅)))).mono (by
      rw [← htailDeg]
      omega)
  · refine ⟨upd E (w : ℕ) 1, D',
      upd R (w : ℕ) (n - 1 - cv), upd ID (w : ℕ) mv,
      BH', BV', BN', ?_⟩
    refine ⟨hP₅, ?_, ?_, ?_, hD₄, ?_, ?_, ?_, ?_⟩
    · exact ⟨by simp [σ₅, harr₄.n_eq], by simp [σ₅, harr₄.elm_eq],
        by simp [σ₅, harr₄.deg_eq], by simp [σ₅, harr₄.rank_eq],
        by simp [σ₅, harr₄.idg_eq], by simp [σ₅, harr₄.head_eq],
        by simp [σ₅, harr₄.val_eq], by simp [σ₅, harr₄.next_eq]⟩
    · simpa [σ₅, hcnt₄, hkmax₄, hmind₄, cv, mv, kv] using helim'
    · simpa [σ₅] using hbuck₄
    · simp [σ₅] at hroom₄ ⊢
      omega
    · simpa [σ₅] using hls₄
    · simp [σ₅]
      omega
    · simp [σ₅, hkmax₄]
      omega
  · simpa [σ₅, htailDeg] using hspUsed₄
  · simpa [σ₅, htailDeg] using hlsUsed₄
  · simp [σ₅, hcnt₄, cv]
  · simp [σ₅, hmind₄, mv]
  · simp [σ₅, hkmax₄, kv, mv]
  · simp [σ₅, harr₄.elm_eq]

/-! ## Axiom audit -/

#print axioms virtualElimVertex_spec

end Lax3Proofs.Refine.OrderVirtualTake
