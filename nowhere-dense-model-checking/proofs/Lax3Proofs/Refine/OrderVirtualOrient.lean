import Lax3Proofs.Refine.OrderVirtualAssemble

/-!
# One recursively generated augmentation row

The next orientation is never materialised.  For one requested root this
module invokes five providers for the preceding orientation, builds the two
demand sets in reusable buffers, applies the saved-rank guard, and restores
all three stamps before returning the exact new row in `vrow`.
-/

namespace Lax3Proofs.Refine.OrderVirtualOrient

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamAugment
open Lax3Proofs.RamDriverAugment (Emits Guarded Marks valSet valSet_lt)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.OrderVirtualBaseOrient (RankDir orientSet)
open Lax3Proofs.Refine.OrderVirtualAugGuard
open Lax3Proofs.Refine.OrderVirtualInvoke
open Lax3Proofs.Refine.OrderVirtualAssemble

def scanTmp (body : Com) : Com :=
  bufferScan "vtmp" "avj" "avend" "u" body

def emitTmpFresh : Com :=
  scanTmp (virtualFreshGuard (rowFillAct "vrow"))

def stampTmp (s : String) : Com :=
  scanTmp (.store s (.var "u") (.lit 1))

def clearTmp (s : String) : Com :=
  scanTmp (.store s (.var "u") (.lit 0))

def emitTmpAug (dir : RankDir) (rk : String) : Com :=
  scanTmp (virtualAugGuard dir rk (rowFillAct "vrow"))

def clearOutput : Com :=
  bufferScan "vrow" "avj" "avend" "u"
    (.store "ste" (.var "u") (.lit 0))

/-- The accumulation half: copy the old desired row, stamp adjacency and
opposite demand, then scan the two desired-demand generators under the
rank-aware guard. -/
def virtualAugAccumulate (dir : RankDir) (rk : String)
    (base opposite trans oppositeTrans frat : Com) : Com :=
  .seq (virtualInvoke base)
    (.seq emitTmpFresh
      (.seq (stampTmp "sta")
        (.seq (virtualInvoke opposite)
          (.seq (stampTmp "sta")
            (.seq (virtualInvoke oppositeTrans)
              (.seq (stampTmp "std")
                (.seq (virtualInvoke frat)
                  (.seq (stampTmp "std")
                    (.seq (virtualInvoke trans)
                      (.seq (emitTmpAug dir rk)
                        (.seq (virtualInvoke frat)
                          (emitTmpAug dir rk))))))))))))

/-- Regenerate the four stamped source rows and clear exactly their support.
The completed output itself clears the emitted stamp. -/
def virtualAugCleanup (base opposite oppositeTrans frat : Com) : Com :=
  .seq (virtualInvoke base)
    (.seq (clearTmp "sta")
      (.seq (virtualInvoke opposite)
        (.seq (clearTmp "sta")
          (.seq (virtualInvoke oppositeTrans)
            (.seq (clearTmp "std")
              (.seq (virtualInvoke frat)
                (.seq (clearTmp "std")
                  (.seq (.assign "avend" (.var "c")) clearOutput))))))))

/-- Complete provider for either row direction of `augOr D rank`. -/
def virtualAugProvide (dir : RankDir) (rk : String)
    (base opposite trans oppositeTrans frat : Com) : Com :=
  .seq (.assign "avroot" (.var "w"))
    (.seq (.assign "c" (.lit 0))
      (.seq (virtualAugAccumulate dir rk base opposite trans oppositeTrans frat)
        (.seq (virtualAugCleanup base opposite oppositeTrans frat)
          (.seq (.assign "vtail" (.var "c"))
            (.assign "w" (.var "avroot"))))))

/-- Exact semantic charge of the accumulation half.  Row walks retain their
actual cardinalities so summing this cost over all roots can use the global
walk bounds rather than paying `n` once per root. -/
noncomputable def virtualAugAccumulateCost {n : ℕ} (dir : RankDir)
    (D : Orientation n)
    (kbase kopposite ktrans koppositeTrans kfrat : ℕ → ℕ) (w : ℕ) : ℕ :=
  if hw : w < n then
    kbase w + kopposite w + ktrans w + koppositeTrans w + 2 * kfrat w +
      40 * (orientSet dir D ⟨w, hw⟩).card +
      14 * (oppositeOrientSet dir D ⟨w, hw⟩).card +
      42 * (transSet dir D ⟨w, hw⟩).card +
      14 * (oppositeTransSet dir D ⟨w, hw⟩).card +
      56 * (fratNbrs D ⟨w, hw⟩).card + 114
  else 0

@[simp] theorem virtualAugAccumulateCost_of_lt {n : ℕ} (dir : RankDir)
    (D : Orientation n)
    (kbase kopposite ktrans koppositeTrans kfrat : ℕ → ℕ)
    {w : ℕ} (hw : w < n) :
    virtualAugAccumulateCost dir D kbase kopposite ktrans koppositeTrans kfrat w =
      kbase w + kopposite w + ktrans w + koppositeTrans w + 2 * kfrat w +
        40 * (orientSet dir D ⟨w, hw⟩).card +
        14 * (oppositeOrientSet dir D ⟨w, hw⟩).card +
        42 * (transSet dir D ⟨w, hw⟩).card +
        14 * (oppositeTransSet dir D ⟨w, hw⟩).card +
        56 * (fratNbrs D ⟨w, hw⟩).card + 114 := by
  simp [virtualAugAccumulateCost, hw]

/-- Exact semantic charge of support cleanup, including the final emitted
row but no carrier-wide scan. -/
noncomputable def virtualAugCleanupCost {n : ℕ} (dir : RankDir)
    (D : Orientation n) (rank : Fin n → ℕ)
    (kbase kopposite koppositeTrans kfrat : ℕ → ℕ) (w : ℕ) : ℕ :=
  if hw : w < n then
    kbase w + kopposite w + koppositeTrans w + kfrat w +
      14 * (orientSet dir D ⟨w, hw⟩).card +
      14 * (oppositeOrientSet dir D ⟨w, hw⟩).card +
      14 * (oppositeTransSet dir D ⟨w, hw⟩).card +
      14 * (fratNbrs D ⟨w, hw⟩).card +
      14 * (orientSet dir (augOr D rank) ⟨w, hw⟩).card + 80
  else 0

@[simp] theorem virtualAugCleanupCost_of_lt {n : ℕ} (dir : RankDir)
    (D : Orientation n) (rank : Fin n → ℕ)
    (kbase kopposite koppositeTrans kfrat : ℕ → ℕ)
    {w : ℕ} (hw : w < n) :
    virtualAugCleanupCost dir D rank kbase kopposite koppositeTrans kfrat w =
      kbase w + kopposite w + koppositeTrans w + kfrat w +
        14 * (orientSet dir D ⟨w, hw⟩).card +
        14 * (oppositeOrientSet dir D ⟨w, hw⟩).card +
        14 * (oppositeTransSet dir D ⟨w, hw⟩).card +
        14 * (fratNbrs D ⟨w, hw⟩).card +
        14 * (orientSet dir (augOr D rank) ⟨w, hw⟩).card + 80 := by
  simp [virtualAugCleanupCost, hw]

/-- Exact charge of one complete assembled row.  The final `8` is the four
constant-cost scalar assignments around accumulation and cleanup. -/
noncomputable def virtualAugCost {n : ℕ} (dir : RankDir)
    (D : Orientation n) (rank : Fin n → ℕ)
    (kbase kopposite ktrans koppositeTrans kfrat : ℕ → ℕ) (w : ℕ) : ℕ :=
  virtualAugAccumulateCost dir D kbase kopposite ktrans koppositeTrans kfrat w +
    virtualAugCleanupCost dir D rank kbase kopposite koppositeTrans kfrat w + 8

/-! ## Aggregate cost of one virtual augmentation -/

/-- Either direction of an orientation has at most `n * d` row entries
under an in-degree bound.  The outgoing case uses the arc-counting
in/out-degree identity. -/
theorem sum_orientSet_card_le {n d : ℕ} (dir : RankDir)
    {D : Orientation n} (hd : D.InDegLE d) :
    (∑ v : Fin n, (orientSet dir D v).card) ≤ n * d := by
  classical
  cases dir with
  | incoming =>
      simp only [orientSet]
      calc
        (∑ v : Fin n, (D.inN v).card) ≤ ∑ _v : Fin n, d :=
          Finset.sum_le_sum fun v _ => hd v
        _ = n * d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  | outgoing =>
      simp only [orientSet]
      rw [sum_card_outSet]
      calc
        (∑ v : Fin n, (D.inN v).card) ≤ ∑ _v : Fin n, d :=
          Finset.sum_le_sum fun v _ => hd v
        _ = n * d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]

/-- The row direction opposite to `dir` has the same global arc bound. -/
theorem sum_oppositeOrientSet_card_le {n d : ℕ} (dir : RankDir)
    {D : Orientation n} (hd : D.InDegLE d) :
    (∑ v : Fin n, (oppositeOrientSet dir D v).card) ≤ n * d := by
  classical
  cases dir with
  | incoming =>
      simp only [oppositeOrientSet]
      rw [sum_card_outSet]
      calc
        (∑ v : Fin n, (D.inN v).card) ≤ ∑ _v : Fin n, d :=
          Finset.sum_le_sum fun v _ => hd v
        _ = n * d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  | outgoing =>
      simp only [oppositeOrientSet]
      calc
        (∑ v : Fin n, (D.inN v).card) ≤ ∑ _v : Fin n, d :=
          Finset.sum_le_sum fun v _ => hd v
        _ = n * d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]

private theorem sum_transInSet_card_le {n d : ℕ} {D : Orientation n}
    (hd : D.InDegLE d) :
    (∑ v : Fin n,
      (Lax3Proofs.Refine.OrderVirtualBiUnion.transInSet D v).card) ≤
        n * (d * d) := by
  classical
  calc
    (∑ v : Fin n,
        (Lax3Proofs.Refine.OrderVirtualBiUnion.transInSet D v).card)
        ≤ ∑ v : Fin n, ∑ w ∈ D.inN v, (D.inN w).card := by
          apply Finset.sum_le_sum
          intro v _
          exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
            Finset.card_biUnion_le
    _ = Lax3Proofs.Refine.OrderVirtualRows.transInWalkWork D := rfl
    _ ≤ n * (d * d) :=
      Lax3Proofs.Refine.OrderVirtualRows.transInWalkWork_le hd

private theorem sum_transOutSet_card_le {n d : ℕ} {D : Orientation n}
    (hd : D.InDegLE d) :
    (∑ v : Fin n,
      (Lax3Proofs.Refine.OrderVirtualBiUnion.transOutSet D v).card) ≤
        n * (d * d) := by
  classical
  calc
    (∑ v : Fin n,
        (Lax3Proofs.Refine.OrderVirtualBiUnion.transOutSet D v).card)
        ≤ ∑ v : Fin n,
            ∑ w ∈ outSet D v, (outSet D w).card := by
          apply Finset.sum_le_sum
          intro v _
          exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
            Finset.card_biUnion_le
    _ = Lax3Proofs.Refine.OrderVirtualRows.transOutWalkWork D := rfl
    _ ≤ n * (d * d) :=
      Lax3Proofs.Refine.OrderVirtualRows.transOutWalkWork_le hd

/-- Both transitive row families are globally bounded by the number of
directed two-walks. -/
theorem sum_transSet_card_le {n d : ℕ} (dir : RankDir)
    {D : Orientation n} (hd : D.InDegLE d) :
    (∑ v : Fin n, (transSet dir D v).card) ≤ n * (d * d) := by
  cases dir with
  | incoming => exact sum_transInSet_card_le hd
  | outgoing => exact sum_transOutSet_card_le hd

theorem sum_oppositeTransSet_card_le {n d : ℕ} (dir : RankDir)
    {D : Orientation n} (hd : D.InDegLE d) :
    (∑ v : Fin n, (oppositeTransSet dir D v).card) ≤ n * (d * d) := by
  cases dir with
  | incoming => exact sum_transOutSet_card_le hd
  | outgoing => exact sum_transInSet_card_le hd

/-- Exact algebraic expansion of all provider invocations and row scans in
one augmentation round. -/
theorem sum_virtualAugCost_eq {n : ℕ} (dir : RankDir)
    (D : Orientation n) (rank : Fin n → ℕ)
    (kbase kopposite ktrans koppositeTrans kfrat : ℕ → ℕ) :
    (∑ w : Fin n,
      virtualAugCost dir D rank kbase kopposite ktrans koppositeTrans kfrat w) =
      2 * (∑ w : Fin n, kbase w) +
      2 * (∑ w : Fin n, kopposite w) +
      (∑ w : Fin n, ktrans w) +
      2 * (∑ w : Fin n, koppositeTrans w) +
      3 * (∑ w : Fin n, kfrat w) +
      54 * (∑ w : Fin n, (orientSet dir D w).card) +
      28 * (∑ w : Fin n, (oppositeOrientSet dir D w).card) +
      42 * (∑ w : Fin n, (transSet dir D w).card) +
      28 * (∑ w : Fin n, (oppositeTransSet dir D w).card) +
      70 * (∑ w : Fin n, (fratNbrs D w).card) +
      14 * (∑ w : Fin n, (orientSet dir (augOr D rank) w).card) +
      202 * n := by
  classical
  simp only [virtualAugCost, virtualAugAccumulateCost,
    virtualAugCleanupCost, Fin.isLt, dif_pos, Fin.eta,
    Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring_nf
  simp_rw [← Finset.sum_mul]
  ring

/-- Summed cost of a complete virtual augmentation round.  Crucially the
non-provider part is `n` times a function of the old and new in-degree
bounds, rather than `n²`. -/
theorem sum_virtualAugCost_le {n d d' : ℕ} (dir : RankDir)
    {D : Orientation n} {rank : Fin n → ℕ}
    (hd : D.InDegLE d) (hd' : (augOr D rank).InDegLE d')
    (kbase kopposite ktrans koppositeTrans kfrat : ℕ → ℕ) :
    (∑ w : Fin n,
      virtualAugCost dir D rank kbase kopposite ktrans koppositeTrans kfrat w) ≤
      2 * (∑ w : Fin n, kbase w) +
      2 * (∑ w : Fin n, kopposite w) +
      (∑ w : Fin n, ktrans w) +
      2 * (∑ w : Fin n, koppositeTrans w) +
      3 * (∑ w : Fin n, kfrat w) +
      54 * (n * d) + 28 * (n * d) +
      42 * (n * (d * d)) + 28 * (n * (d * d)) +
      70 * (n * (d * d)) + 14 * (n * d') + 202 * n := by
  rw [sum_virtualAugCost_eq]
  have hbase := sum_orientSet_card_le dir hd
  have hopposite := sum_oppositeOrientSet_card_le dir hd
  have htrans := sum_transSet_card_le dir hd
  have hoppositeTrans := sum_oppositeTransSet_card_le dir hd
  have hfrat : (∑ w : Fin n, (fratNbrs D w).card) ≤ n * (d * d) :=
    Lax3Proofs.RamAugment.fratSlots_le hd
  have hout := sum_orientSet_card_le dir hd'
  gcongr

/-- State carried by the emitted-row accumulator.  The abstract set `U` is
represented both by the live prefix of `vrow` and by the emitted stamp. -/
structure AugRowAcc (n W root : ℕ) (P : Env → Prop) (Cap U : Finset ℕ)
    (E D R ID BH BV BN : ℕ → ℕ) (base sigma : Env) : Prop where
  fill : RowFillAcc "vrow" n Cap U sigma
  persistent : P sigma
  engine : EngineArrays n W E D R ID BH BV BN sigma
  stable : ProviderStable base sigma
  root_eq : sigma.vars "w" = root
  saved_root : sigma.vars "avroot" = root
  tmp_length : (sigma.arrs "vtmp").length = n
  save_length : (sigma.arrs "avsave").length = 1

namespace AugRowAcc

def scalarFrames : List String :=
  ["n", "w", "c", "i", "sp", "ls", "cnt", "mind", "kmax", "avroot"]

def arrayFrames : List String :=
  ["vrow", "vtmp", "avsave", "elm", "deg", "rnk", "idg", "bh", "bv", "bn"]

/-- A private assembler pass that frames the accumulator's scalar and array
surface preserves the whole invariant. -/
theorem run_private {B K n W root : ℕ} {P : Env → Prop} {Cap U : Finset ℕ}
    {E D R ID BH BV BN : ℕ → ℕ} {base sigma tau : Env} {c : Com}
    (hclose : AugScratchClosed P)
    (h : AugRowAcc n W root P Cap U E D R ID BH BV BN base sigma)
    (hr : Run B c sigma tau K)
    (hfv : ∀ y ∈ scalarFrames, y ∉ c.wvars)
    (hfa : ∀ a ∈ arrayFrames, a ∉ c.warrs)
    (hvars : ∀ y ∈ c.wvars, y ≠ "n")
    (harrs : ∀ a ∈ c.warrs,
      a ∈ ["vrow", "sta", "std", "ste", "avsave"])
    (hreads : ¬ c.reads) (hwrites : c.NoWrite) :
    AugRowAcc n W root P Cap U E D R ID BH BV BN base tau := by
  have frameVar (y : String) (hy : y ∈ scalarFrames) :
      tau.vars y = sigma.vars y := hr.frame_var y (hfv y hy)
  have frameArr (a : String) (ha : a ∈ arrayFrames) :
      tau.arrs a = sigma.arrs a := hr.frame_arr a (hfa a ha)
  obtain ⟨hsub, A, hA, hc, hnd, hmem⟩ := h.fill
  refine ⟨⟨hsub, A, ?_, ?_, hnd, hmem⟩,
    hclose.run hr hvars harrs hreads hwrites h.persistent, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frameArr "vrow" (by simp [arrayFrames])]
    exact hA
  · rw [frameVar "c" (by simp [scalarFrames])]
    exact hc
  · exact ⟨by rw [frameVar "n" (by simp [scalarFrames])]; exact h.engine.n_eq,
      by rw [frameArr "elm" (by simp [arrayFrames])]; exact h.engine.elm_eq,
      by rw [frameArr "deg" (by simp [arrayFrames])]; exact h.engine.deg_eq,
      by rw [frameArr "rnk" (by simp [arrayFrames])]; exact h.engine.rank_eq,
      by rw [frameArr "idg" (by simp [arrayFrames])]; exact h.engine.idg_eq,
      by rw [frameArr "bh" (by simp [arrayFrames])]; exact h.engine.head_eq,
      by rw [frameArr "bv" (by simp [arrayFrames])]; exact h.engine.val_eq,
      by rw [frameArr "bn" (by simp [arrayFrames])]; exact h.engine.next_eq⟩
  · exact ⟨by rw [frameVar "n" (by simp [scalarFrames])]; exact h.stable.n_eq,
      by rw [frameVar "w" (by simp [scalarFrames])]; exact h.stable.w_eq,
      by rw [frameVar "i" (by simp [scalarFrames])]; exact h.stable.i_eq,
      by rw [frameVar "sp" (by simp [scalarFrames])]; exact h.stable.sp_eq,
      by rw [frameVar "ls" (by simp [scalarFrames])]; exact h.stable.ls_eq,
      by rw [frameVar "cnt" (by simp [scalarFrames])]; exact h.stable.cnt_eq,
      by rw [frameVar "mind" (by simp [scalarFrames])]; exact h.stable.mind_eq,
      by rw [frameVar "kmax" (by simp [scalarFrames])]; exact h.stable.kmax_eq⟩
  · rw [frameVar "w" (by simp [scalarFrames])]
    exact h.root_eq
  · rw [frameVar "avroot" (by simp [scalarFrames])]
    exact h.saved_root
  · rw [frameArr "vtmp" (by simp [arrayFrames])]
    exact h.tmp_length
  · rw [frameArr "avsave" (by simp [arrayFrames])]
    exact h.save_length

/-- A reusable-buffer pass that only stores into one of the three stamp
arrays is private with respect to `AugRowAcc`. -/
theorem run_bufferStore_private {B K n W root b : ℕ}
    {P : Env → Prop} {Cap U : Finset ℕ}
    {E D R ID BH BV BN : ℕ → ℕ} {base sigma tau : Env}
    {src s : String}
    (hclose : AugScratchClosed P)
    (h : AugRowAcc n W root P Cap U E D R ID BH BV BN base sigma)
    (hs : s = "sta" ∨ s = "std" ∨ s = "ste")
    (hr : Run B
      (bufferScan src "avj" "avend" "u"
        (.store s (.var "u") (.lit b))) sigma tau K) :
    AugRowAcc n W root P Cap U E D R ID BH BV BN base tau := by
  rcases hs with rfl | rfl | rfl <;>
    apply run_private hclose h hr <;>
    simp [scalarFrames, arrayFrames, bufferScan,
      Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
      Com.warrs, Com.reads, Com.NoWrite]

theorem stamp_run {B n W root tail : ℕ} {P : Env → Prop}
    {Cap U M : Finset ℕ} {E D R ID BH BV BN A : ℕ → ℕ}
    {base sigma : Env} {S : Finset (Fin n)} {s : String}
    (hclose : AugScratchClosed P) (hs : s = "sta" ∨ s = "std" ∨ s = "ste")
    (hB1 : 1 < B) (hnB : n < B)
    (hrow : SetRowRep S tail A) (hend : sigma.vars "avend" = tail)
    (hsrc : sigma.arrs "vtmp" = arrOf n A)
    (hmarks : Marks s n 1 M (fun _ => 0) sigma)
    (hacc : AugRowAcc n W root P Cap U E D R ID BH BV BN base sigma) :
    ∃ tau K, Run B (stampTmp s) sigma tau K ∧ K ≤ tail * 14 + 6 ∧
      Marks s n 1 (M ∪ valSet S) (fun _ => 0) tau ∧
      AugRowAcc n W root P Cap U E D R ID BH BV BN base tau := by
  have hsv : s ≠ "vtmp" := by
    rintro rfl
    rcases hs with h | h | h <;> contradiction
  obtain ⟨tau, K, hr, hK, hm⟩ :=
    stampBuffer_union_run (B := B) (n := n) (tail := tail) (b := 1)
      (src := "vtmp") (j := "avj") (jend := "avend") (u := "u")
      (s := s) (S := S) (Base := M) (A := A) (sigma := sigma)
      (by decide) (by decide) (by decide) hsv hB1 hnB (by omega)
      hrow hend hsrc hmarks
  exact ⟨tau, K, by simpa [stampTmp, scanTmp] using hr, hK, hm,
    hacc.run_bufferStore_private hclose hs hr⟩

theorem clear_run {B n W root tail : ℕ} {P : Env → Prop}
    {Cap U M : Finset ℕ} {E D R ID BH BV BN A : ℕ → ℕ}
    {base sigma : Env} {S : Finset (Fin n)} {s : String}
    (hclose : AugScratchClosed P) (hs : s = "sta" ∨ s = "std" ∨ s = "ste")
    (hB1 : 1 < B) (hnB : n < B)
    (hrow : SetRowRep S tail A) (hend : sigma.vars "avend" = tail)
    (hsrc : sigma.arrs "vtmp" = arrOf n A)
    (hmarks : Marks s n 1 M (fun _ => 0) sigma)
    (hacc : AugRowAcc n W root P Cap U E D R ID BH BV BN base sigma) :
    ∃ tau K, Run B (clearTmp s) sigma tau K ∧ K ≤ tail * 14 + 6 ∧
      Marks s n 1 (M \ valSet S) (fun _ => 0) tau ∧
      AugRowAcc n W root P Cap U E D R ID BH BV BN base tau := by
  have hsv : s ≠ "vtmp" := by
    rintro rfl
    rcases hs with h | h | h <;> contradiction
  obtain ⟨tau, K, hr, hK, hm⟩ :=
    clearBuffer_run (B := B) (n := n) (tail := tail)
      (src := "vtmp") (j := "avj") (jend := "avend") (u := "u")
      (s := s) (S := S) (M := M) (A := A) (sigma := sigma)
      (by decide) (by decide) (by decide) hsv hB1 hnB hrow hend hsrc hmarks
  exact ⟨tau, K, by simpa [clearTmp, scanTmp] using hr, hK, hm,
    hacc.run_bufferStore_private hclose hs hr⟩

theorem setVar {n W root : ℕ} {P : Env → Prop} {Cap U : Finset ℕ}
    {E D R ID BH BV BN : ℕ → ℕ} {base sigma : Env}
    (hclose : AugScratchClosed P)
    (h : AugRowAcc n W root P Cap U E D R ID BH BV BN base sigma)
    {y : String} {x : ℕ}
    (hn : y ≠ "n") (hw : y ≠ "w") (hc : y ≠ "c")
    (hi : y ≠ "i") (hsp : y ≠ "sp") (hls : y ≠ "ls")
    (hcnt : y ≠ "cnt") (hmind : y ≠ "mind") (hkmax : y ≠ "kmax")
    (har : y ≠ "avroot") :
    AugRowAcc n W root P Cap U E D R ID BH BV BN base
      (sigma.setVar y x) := by
  exact ⟨h.fill.setVar hc x, hclose.setVar hn h.persistent,
    h.engine.setVar y x hn,
    Lax3Proofs.Refine.OrderVirtualBaseOrient.ProviderStable.setVar_of_private
      h.stable hn hw hi hsp hls hcnt hmind hkmax x,
    by rw [vars_setVar, if_neg (Ne.symm hw)]; exact h.root_eq,
    by rw [vars_setVar, if_neg (Ne.symm har)]; exact h.saved_root,
    by simpa using h.tmp_length, by simpa using h.save_length⟩

theorem setSte {n W root : ℕ} {P : Env → Prop} {Cap U : Finset ℕ}
    {E D R ID BH BV BN : ℕ → ℕ} {base sigma : Env}
    (hclose : AugScratchClosed P)
    (h : AugRowAcc n W root P Cap U E D R ID BH BV BN base sigma)
    (p x : ℕ) :
    AugRowAcc n W root P Cap U E D R ID BH BV BN base
      (sigma.setArr "ste" p x) := by
  exact ⟨h.fill.setArr_of_ne (by decide) p x,
    hclose.setArr (by simp) h.persistent,
    h.engine.setArr_of_private (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) p x,
    h.stable.setArr "ste" p x, by simpa using h.root_eq,
    by simpa using h.saved_root, by simpa using h.tmp_length,
    by simpa using h.save_length⟩

/-- The row append action preserves the complete parent invariant. -/
theorem emits {B n W root : ℕ} {P : Env → Prop} {Cap : Finset ℕ}
    {E D R ID BH BV BN : ℕ → ℕ} {base : Env}
    (hclose : AugScratchClosed P) (hnB : n < B)
    (hCap : Cap ⊆ Finset.range n) :
    Emits B n 7 "vrow" "@" (rowFillAct "vrow") Cap
      (fun U sigma =>
        AugRowAcc n W root P Cap U E D R ID BH BV BN base sigma) := by
  intro U sigma z h hu hzn hzU hzCap
  obtain ⟨tau, K, hr, hK, hfill, hfv, hfa⟩ :=
    rowFillAcc_emits hnB hCap U sigma z h.fill hu hzn hzU hzCap
  have hP : P tau := hclose.run hr
    (by intro a ha; simp [rowFillAct, Com.wvars] at ha; subst a; decide)
    (by intro a ha; simp [rowFillAct, Com.warrs] at ha; subst a; simp)
    (by simp [rowFillAct, Com.reads]) (by simp [rowFillAct, Com.NoWrite])
    h.persistent
  have heng : EngineArrays n W E D R ID BH BV BN tau :=
    ⟨by rw [hfv "n" (by decide)]; exact h.engine.n_eq,
      by rw [hfa "elm" (by decide) (by decide)]; exact h.engine.elm_eq,
      by rw [hfa "deg" (by decide) (by decide)]; exact h.engine.deg_eq,
      by rw [hfa "rnk" (by decide) (by decide)]; exact h.engine.rank_eq,
      by rw [hfa "idg" (by decide) (by decide)]; exact h.engine.idg_eq,
      by rw [hfa "bh" (by decide) (by decide)]; exact h.engine.head_eq,
      by rw [hfa "bv" (by decide) (by decide)]; exact h.engine.val_eq,
      by rw [hfa "bn" (by decide) (by decide)]; exact h.engine.next_eq⟩
  exact ⟨tau, K, hr, hK,
    ⟨hfill, hP, heng,
      Lax3Proofs.Refine.OrderVirtualBaseOrient.ProviderStable.of_emit_frame
        h.stable hfv,
      by rw [hfv "w" (by decide)]; exact h.root_eq,
      by rw [hfv "avroot" (by decide)]; exact h.saved_root,
      by rw [hfa "vtmp" (by decide) (by decide)]; exact h.tmp_length,
      by rw [hfa "avsave" (by decide) (by decide)]; exact h.save_length⟩,
    hfv, hfa⟩

/-- Invoke one child provider while retaining the accumulated row and all
engine scalars. -/
theorem invoke_run {B n W root : ℕ} {P : Env → Prop} {Cap U : Finset ℕ}
    {E D R ID BH BV BN : ℕ → ℕ} {base sigma : Env}
    {S : Fin n → Finset (Fin n)} {provide : Com} {kappa : ℕ → ℕ}
    (hclose : AugScratchClosed P) (hframes : AugInvokeFrames provide)
    (hB1 : 1 < B) (hnB : n < B) (hCap : Cap ⊆ Finset.range n)
    (hp : ProvidesSetRows B n W S P "vtmp" provide kappa)
    (h : AugRowAcc n W root P Cap U E D R ID BH BV BN base sigma)
    (hroot : root < n) :
    ∃ tau tail A,
      Run B (virtualInvoke provide) sigma tau (kappa root + 12) ∧
      AugRowAcc n W root P Cap U E D R ID BH BV BN base tau ∧
      SetRowRep (S ⟨root, hroot⟩) tail A ∧
      tau.vars "avend" = tail ∧ tau.arrs "vtmp" = arrOf n A ∧
      tau.arrs "sta" = sigma.arrs "sta" ∧
      tau.arrs "std" = sigma.arrs "std" ∧
      tau.arrs "ste" = sigma.arrs "ste" := by
  have hcount : sigma.vars "c" = U.card := h.fill.2.choose_spec.2.1
  have hUr : U ⊆ Finset.range n := h.fill.1.trans hCap
  have hcard : U.card ≤ n := by
    simpa using Finset.card_le_card hUr
  obtain ⟨tau, tail, A, hr, hP, heng, hstable, hrow, htmp, hend,
      hc, hw, havroot, hsave, hvrow, hsta, hstd, hste⟩ :=
    virtualInvoke_run (root := ⟨root, hroot⟩) hclose.toInvokeClosed hframes hB1 hnB hp h.persistent
      h.engine h.root_eq h.saved_root hcount (by omega) h.save_length
  obtain ⟨hsub, Aout, hAout, hcOut, hnd, hmem⟩ := h.fill
  have hfill : RowFillAcc "vrow" n Cap U tau :=
    ⟨hsub, Aout, by rw [hvrow]; exact hAout, hc, hnd, hmem⟩
  refine ⟨tau, tail, A, hr, ?_, hrow, hend, htmp, hsta, hstd, hste⟩
  exact ⟨hfill, hP, heng, h.stable.trans hstable, hw, havroot,
    by rw [htmp, length_arrOf], hsave⟩

/-- Copy the old desired row into the output and initialise the emitted
stamp with exactly that row. -/
theorem freshBuffer_run {B n W root tail : ℕ} {P : Env → Prop}
    {Cap : Finset ℕ} {E D R ID BH BV BN A : ℕ → ℕ} {base sigma : Env}
    {S : Finset (Fin n)}
    (hclose : AugScratchClosed P) (hB1 : 1 < B) (hnB : n < B)
    (hCap : Cap ⊆ Finset.range n) (hSCap : valSet S ⊆ Cap)
    (hrow : SetRowRep S tail A) (hend : sigma.vars "avend" = tail)
    (hsrc : sigma.arrs "vtmp" = arrOf n A)
    (hmarks : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma)
    (hacc : AugRowAcc n W root P Cap ∅ E D R ID BH BV BN base sigma) :
    ∃ tau K,
      Run B emitTmpFresh sigma tau K ∧ K ≤ tail * 26 + 6 ∧
      Marks "ste" n 1 (valSet S) (fun _ => 0) tau ∧
      AugRowAcc n W root P Cap (valSet S) E D R ID BH BV BN base tau := by
  let AccT : Finset ℕ → Env → Prop := fun U tau =>
    AugRowAcc n W root P Cap U E D R ID BH BV BN base tau ∧
      tau.arrs "vtmp" = arrOf n A
  have hemit0 : Emits B n 7 "vrow" "@" (rowFillAct "vrow") Cap
      (fun U tau =>
        AugRowAcc n W root P Cap U E D R ID BH BV BN base tau) :=
    AugRowAcc.emits (B := B) (n := n) (W := W) (root := root)
      (P := P) (Cap := Cap) (E := E) (D := D) (R := R) (ID := ID)
      (BH := BH) (BV := BV) (BN := BN) (base := base) hclose hnB hCap
  have hemit : Emits B n 7 "vrow" "@" (rowFillAct "vrow") Cap AccT :=
    hemit0.and (by
      intro tau tau' htmp hfv hfa
      rw [hfa "vtmp" (by decide) (by decide)]
      exact htmp)
  have hAccSt : ∀ U tau p x, AccT U tau → AccT U (tau.setArr "ste" p x) := by
    rintro U tau p x ⟨hA, htmp⟩
    exact ⟨hA.setSte hclose p x, by simpa using htmp⟩
  have hguard : Guarded B n 15 (virtualFreshGuard (rowFillAct "vrow"))
      (fun z => {z}) Cap
      (fun U tau => Marks "ste" n 1 U (fun _ => 0) tau ∧ AccT U tau) :=
    virtualFreshGuard_of_emits (a₁ := "vrow") (a₂ := "@")
      (by decide) (by decide) hB1 hnB hAccSt hemit
  have hJv : ∀ U tau (y : String) (z : ℕ),
      (y = "avj" ∨ y = "u") →
      (Marks "ste" n 1 U (fun _ => 0) tau ∧ AccT U tau) →
      Marks "ste" n 1 U (fun _ => 0) (tau.setVar y z) ∧
        AccT U (tau.setVar y z) := by
    rintro U tau y z (rfl | rfl) ⟨hm, hA, htmp⟩
    · exact ⟨hm.setVar _ _, hA.setVar hclose (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), by simpa using htmp⟩
    · exact ⟨hm.setVar _ _, hA.setVar hclose (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), by simpa using htmp⟩
  have hslot : ∀ p, p < tail → ({A p} : Finset ℕ) ⊆ Cap := by
    intro p hp z hz
    have hzA : z = A p := by simpa using hz
    subst z
    exact hSCap ((hrow.mem_valSet_iff (A p)).2 ⟨p, hp, rfl⟩)
  obtain ⟨tau, K, hr, hK, hJ⟩ :=
    emitBuffer_run (B := B) (n := n) (tail := tail) (Kg := 15)
      (src := "vtmp") (j := "avj") (jend := "avend")
      (grd := virtualFreshGuard (rowFillAct "vrow"))
      (S := S) (A := A) (fe := fun z => {z})
      (J := fun U tau => Marks "ste" n 1 U (fun _ => 0) tau ∧ AccT U tau)
      (E0 := ∅) (Cap := Cap) (sigma := sigma)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hB1 hnB hrow hend hsrc (fun _ _ h => h.2.2) hJv hslot hguard
      ⟨hmarks, hacc, hsrc⟩
  have hfull : bufferAcc tail A (fun z => ({z} : Finset ℕ)) = valSet S := by
    rw [bufferAcc_eq_biUnion_valSet hrow]
    simp
  rw [Finset.empty_union, hfull] at hJ
  exact ⟨tau, K, by simpa [emitTmpFresh, scanTmp] using hr,
    by simpa using hK, hJ.1, hJ.2.1⟩

/-- Scan one exact desired-demand component under the rank-aware guard. -/
theorem augBuffer_run {B n W root tail : ℕ} {dir : RankDir} {rk : String}
    {P : Env → Prop} {Adj Opp Base Cap Cand : Finset ℕ}
    {RR E D R ID BH BV BN A : ℕ → ℕ} {base sigma : Env}
    {S : Finset (Fin n)}
    (hclose : AugScratchClosed P)
    (hrkv : rk ≠ "vrow") (hrka : rk ≠ "@") (hrks : rk ≠ "ste")
    (hB1 : 1 < B) (hnB : n < B) (hroot : root < n)
    (hRR : ∀ v, v < n → RR v < n) (hBaseAdj : Base ⊆ Adj)
    (hCap : Cap ⊆ Finset.range n)
    (hrow : SetRowRep S tail A) (hend : sigma.vars "avend" = tail)
    (hsrc : sigma.arrs "vtmp" = arrOf n A)
    (hfe : ∀ p, p < tail →
      virtualAugFe dir Adj Opp RR root (A p) ⊆ Cap)
    (hste : Marks "ste" n 1 (Base ∪ Cand) (fun _ => 0) sigma)
    (hsta : Marks "sta" n 1 Adj (fun _ => 0) sigma)
    (hstd : Marks "std" n 1 Opp (fun _ => 0) sigma)
    (hrank : sigma.arrs rk = arrOf n RR)
    (hacc : AugRowAcc n W root P Cap (Base ∪ Cand)
      E D R ID BH BV BN base sigma) :
    ∃ tau K,
      Run B (emitTmpAug dir rk) sigma tau K ∧ K ≤ tail * 42 + 6 ∧
      Marks "ste" n 1 (Base ∪ (Cand ∪ bufferAcc tail A
        (virtualAugFe dir Adj Opp RR root))) (fun _ => 0) tau ∧
      Marks "sta" n 1 Adj (fun _ => 0) tau ∧
      Marks "std" n 1 Opp (fun _ => 0) tau ∧
      tau.arrs rk = arrOf n RR ∧
      AugRowAcc n W root P Cap (Base ∪ (Cand ∪ bufferAcc tail A
        (virtualAugFe dir Adj Opp RR root)))
        E D R ID BH BV BN base tau := by
  let AccT : Finset ℕ → Env → Prop := fun U tau =>
    AugRowAcc n W root P Cap U E D R ID BH BV BN base tau ∧
      tau.arrs "vtmp" = arrOf n A
  have hemit0 : Emits B n 7 "vrow" "@" (rowFillAct "vrow") Cap
      (fun U tau =>
        AugRowAcc n W root P Cap U E D R ID BH BV BN base tau) :=
    AugRowAcc.emits (B := B) (n := n) (W := W) (root := root)
      (P := P) (Cap := Cap) (E := E) (D := D) (R := R) (ID := ID)
      (BH := BH) (BV := BV) (BN := BN) (base := base) hclose hnB hCap
  have hemit : Emits B n 7 "vrow" "@" (rowFillAct "vrow") Cap AccT :=
    hemit0.and (by
      intro tau tau' htmp hfv hfa
      rw [hfa "vtmp" (by decide) (by decide)]
      exact htmp)
  have hAccSt : ∀ U tau p x, AccT U tau → AccT U (tau.setArr "ste" p x) := by
    rintro U tau p x ⟨hA, htmp⟩
    exact ⟨hA.setSte hclose p x, by simpa using htmp⟩
  have hAccW : ∀ U tau, AccT U tau → tau.vars "w" = root :=
    fun _ _ h => h.1.root_eq
  have hguard : Guarded B n 31 (virtualAugGuard dir rk (rowFillAct "vrow"))
      (virtualAugFe dir Adj Opp RR root) Cap
      (fun Q tau =>
        Marks "ste" n 1 (Base ∪ Q) (fun _ => 0) tau ∧
        Marks "sta" n 1 Adj (fun _ => 0) tau ∧
        Marks "std" n 1 Opp (fun _ => 0) tau ∧
        tau.arrs rk = arrOf n RR ∧ AccT (Base ∪ Q) tau) :=
    virtualAugGuard_of_emits (a₁ := "vrow") (a₂ := "@")
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (Ne.symm hrkv) (Ne.symm hrka) hrks hB1 hnB hroot hRR hBaseAdj
      hAccSt hAccW hemit
  have hJv : ∀ Q tau (y : String) (z : ℕ),
      (y = "avj" ∨ y = "u") →
      (Marks "ste" n 1 (Base ∪ Q) (fun _ => 0) tau ∧
        Marks "sta" n 1 Adj (fun _ => 0) tau ∧
        Marks "std" n 1 Opp (fun _ => 0) tau ∧
        tau.arrs rk = arrOf n RR ∧ AccT (Base ∪ Q) tau) →
      Marks "ste" n 1 (Base ∪ Q) (fun _ => 0) (tau.setVar y z) ∧
        Marks "sta" n 1 Adj (fun _ => 0) (tau.setVar y z) ∧
        Marks "std" n 1 Opp (fun _ => 0) (tau.setVar y z) ∧
        (tau.setVar y z).arrs rk = arrOf n RR ∧
        AccT (Base ∪ Q) (tau.setVar y z) := by
    rintro Q tau y z (rfl | rfl) ⟨h1, h2, h3, h4, h5, htmp⟩
    · exact ⟨h1.setVar _ _, h2.setVar _ _, h3.setVar _ _, by simpa using h4,
        h5.setVar hclose (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), by simpa using htmp⟩
    · exact ⟨h1.setVar _ _, h2.setVar _ _, h3.setVar _ _, by simpa using h4,
        h5.setVar hclose (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), by simpa using htmp⟩
  obtain ⟨tau, K, hr, hK, hJ⟩ :=
    emitBuffer_run (B := B) (n := n) (tail := tail) (Kg := 31)
      (src := "vtmp") (j := "avj") (jend := "avend")
      (grd := virtualAugGuard dir rk (rowFillAct "vrow"))
      (S := S) (A := A) (fe := virtualAugFe dir Adj Opp RR root)
      (J := fun Q tau =>
        Marks "ste" n 1 (Base ∪ Q) (fun _ => 0) tau ∧
        Marks "sta" n 1 Adj (fun _ => 0) tau ∧
        Marks "std" n 1 Opp (fun _ => 0) tau ∧
        tau.arrs rk = arrOf n RR ∧ AccT (Base ∪ Q) tau)
      (E0 := Cand) (Cap := Cap) (sigma := sigma)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hB1 hnB hrow hend hsrc (fun _ _ h => h.2.2.2.2.2)
      hJv hfe hguard ⟨hste, hsta, hstd, hrank, hacc, hsrc⟩
  exact ⟨tau, K, by simpa [emitTmpAug, scanTmp] using hr,
    by simpa using hK, hJ.1, hJ.2.1, hJ.2.2.1, hJ.2.2.2.1,
    hJ.2.2.2.2.1⟩

end AugRowAcc

/-- Exact state after the six accumulating child calls. -/
structure AugAccumulated (n W root : ℕ) (P : Env → Prop)
    (rk : String) (Cap Adj Opp : Finset ℕ) (RR E D R ID BH BV BN : ℕ → ℕ)
    (base sigma : Env) : Prop where
  acc : AugRowAcc n W root P Cap Cap E D R ID BH BV BN base sigma
  adjacency : Marks "sta" n 1 Adj (fun _ => 0) sigma
  opposite : Marks "std" n 1 Opp (fun _ => 0) sigma
  emitted : Marks "ste" n 1 Cap (fun _ => 0) sigma
  rank : sigma.arrs rk = arrOf n RR

/-- State after cleanup: the exact output row remains live while every stamp
has been restored to its zero background. -/
structure AugCleaned (n W root : ℕ) (P : Env → Prop)
    (rk : String) (Cap : Finset ℕ) (RR E D R ID BH BV BN : ℕ → ℕ)
    (base sigma : Env) : Prop where
  acc : AugRowAcc n W root P Cap Cap E D R ID BH BV BN base sigma
  adjacency : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma
  opposite : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma
  emitted : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma
  rank : sigma.arrs rk = arrOf n RR

/-- The six child calls and seven buffer scans that construct the exact new
orientation row. -/
theorem virtualAugAccumulate_run {B n W : ℕ} {dir : RankDir} {rk : String}
    {P : Env → Prop} {Or : Orientation n} {rank : Fin n → ℕ}
    {RR : ℕ → ℕ} {root : Fin n}
    {base opposite trans oppositeTrans frat : Com}
    {kbase kopposite ktrans koppositeTrans kfrat : ℕ → ℕ}
    {E Deg ER ID BH BV BN : ℕ → ℕ} {sigma0 baseEnv : Env}
    (hclose : AugScratchClosed P)
    (fbase : AugInvokeFrames base) (fopposite : AugInvokeFrames opposite)
    (ftrans : AugInvokeFrames trans)
    (foppositeTrans : AugInvokeFrames oppositeTrans)
    (ffrat : AugInvokeFrames frat)
    (hrkv : rk ≠ "vrow") (hrka : rk ≠ "@") (hrks : rk ≠ "ste")
    (hB1 : 1 < B) (hnB : n < B)
    (hrankP : ∀ sigma, P sigma → sigma.arrs rk = arrOf n RR)
    (hrank : ∀ v : Fin n, rank v = RR (v : ℕ))
    (hRR : ∀ v, v < n → RR v < n)
    (hpbase : ProvidesSetRows B n W (fun w => orientSet dir Or w)
      P "vtmp" base kbase)
    (hpopposite : ProvidesSetRows B n W (oppositeOrientSet dir Or)
      P "vtmp" opposite kopposite)
    (hptrans : ProvidesSetRows B n W (transSet dir Or)
      P "vtmp" trans ktrans)
    (hpoppositeTrans : ProvidesSetRows B n W (oppositeTransSet dir Or)
      P "vtmp" oppositeTrans koppositeTrans)
    (hpfrat : ProvidesSetRows B n W (fratNbrs Or)
      P "vtmp" frat kfrat)
    (hacc0 : AugRowAcc n W (root : ℕ) P
      (valSet (orientSet dir (augOr Or rank) root)) ∅
      E Deg ER ID BH BV BN baseEnv sigma0)
    (hsta0 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma0)
    (hstd0 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma0)
    (hste0 : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma0) :
    ∃ sigma K,
      Run B (virtualAugAccumulate dir rk base opposite trans oppositeTrans frat)
        sigma0 sigma K ∧
      K ≤ virtualAugAccumulateCost dir Or kbase kopposite ktrans
        koppositeTrans kfrat root ∧
      AugAccumulated n W root P rk
        (valSet (orientSet dir (augOr Or rank) root))
        (valSet (Lax3Proofs.RamAugment.adjSet Or root))
        (valSet ((oppositeDemandSet dir Or root).erase root))
        RR E Deg ER ID BH BV BN baseEnv sigma := by
  classical
  let Base : Finset ℕ := valSet (orientSet dir Or root)
  let OppRow : Finset ℕ := valSet (oppositeOrientSet dir Or root)
  let Adj : Finset ℕ := valSet (Lax3Proofs.RamAugment.adjSet Or root)
  let OppTrans : Finset ℕ := valSet (oppositeTransSet dir Or root)
  let Frat : Finset ℕ := valSet (fratNbrs Or root)
  let Dm : Finset ℕ := valSet ((oppositeDemandSet dir Or root).erase root)
  let Trans : Finset ℕ := valSet (transSet dir Or root)
  let Cand : Finset ℕ := valSet (augCandidateSet dir Or rank root)
  let Cap : Finset ℕ := valSet (orientSet dir (augOr Or rank) root)
  let fe : ℕ → Finset ℕ :=
    virtualAugFe dir Adj Dm RR (root : ℕ)
  have hCapRange : Cap ⊆ Finset.range n := by
    intro z hz
    exact Finset.mem_range.2 (valSet_lt hz)
  have hBaseCap : Base ⊆ Cap := by
    simp only [Base, Cap]
    rw [orientSet_augOr_eq, Lax3Proofs.RamDriverAugment.valSet_union]
    exact Finset.subset_union_left
  have hAdjEq : Base ∪ OppRow = Adj := by
    simp only [Base, OppRow, Adj]
    rw [← Lax3Proofs.RamDriverAugment.valSet_union,
      ← adjSet_eq_direction_union]
  have hDmEq : OppTrans ∪ Frat = Dm := by
    simp only [OppTrans, Frat, Dm]
    rw [← Lax3Proofs.RamDriverAugment.valSet_union,
      ← oppositeDemandSet_erase_eq_union]
  have hDemandEq : Trans ∪ Frat =
      valSet ((demandSet dir Or root).erase root) := by
    simp only [Trans, Frat]
    rw [← Lax3Proofs.RamDriverAugment.valSet_union,
      ← demandSet_erase_eq_union]
  have hCandUnion :
      (valSet ((demandSet dir Or root).erase root)).biUnion fe = Cand := by
    simpa [fe, Adj, Dm, Cand] using
      virtualAugFe_demand_eq dir Or rank RR root hrank
  have hCandCap : Cand ⊆ Cap := by
    simp only [Cand, Cap]
    rw [orientSet_augOr_eq,
      Lax3Proofs.RamDriverAugment.valSet_union]
    exact Finset.subset_union_right
  have hfeDemand : ∀ z ∈ valSet ((demandSet dir Or root).erase root),
      fe z ⊆ Cap := by
    intro z hz y hy
    apply hCandCap
    rw [← hCandUnion]
    exact Finset.mem_biUnion.2 ⟨z, hz, hy⟩

  obtain ⟨sigma1, tb, Ab, r1, hacc1, hrowb, hendb, htmpb,
      hsta1eq, hstd1eq, hste1eq⟩ :=
    hacc0.invoke_run hclose fbase hB1 hnB hCapRange hpbase root.isLt
  have hsta1 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma1 :=
    hsta0.of_eq hsta1eq
  have hstd1 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma1 :=
    hstd0.of_eq hstd1eq
  have hste1 : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma1 :=
    hste0.of_eq hste1eq
  obtain ⟨sigma2, K2, r2, hK2, hste2, hacc2⟩ :=
    hacc1.freshBuffer_run hclose hB1 hnB hCapRange hBaseCap
      hrowb hendb htmpb hste1
  have hsta2 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma2 :=
    hsta1.of_eq (r2.frame_arr "sta" (by
      simp [emitTmpFresh, scanTmp, virtualFreshGuard, rowFillAct, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hstd2 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma2 :=
    hstd1.of_eq (r2.frame_arr "std" (by
      simp [emitTmpFresh, scanTmp, virtualFreshGuard, rowFillAct, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hendb2 : sigma2.vars "avend" = tb := by
    rw [r2.frame_var "avend" (by
      simp [emitTmpFresh, scanTmp, virtualFreshGuard, rowFillAct, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars])]
    exact hendb
  have htmpb2 : sigma2.arrs "vtmp" = arrOf n Ab := by
    rw [r2.frame_arr "vtmp" (by
      simp [emitTmpFresh, scanTmp, virtualFreshGuard, rowFillAct, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs])]
    exact htmpb
  obtain ⟨sigma3, K3, r3, hK3, hsta3, hacc3⟩ :=
    hacc2.stamp_run hclose (_root_.Or.inl rfl) hB1 hnB
      hrowb hendb2 htmpb2 hsta2
  have hste3 : Marks "ste" n 1 Base (fun _ => 0) sigma3 :=
    hste2.of_eq (r3.frame_arr "ste" (by
      simp [stampTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hstd3 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma3 :=
    hstd2.of_eq (r3.frame_arr "std" (by
      simp [stampTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))

  obtain ⟨sigma4, tOpp, Ao, r4, hacc4, hrowo, hendo, htmpo,
      hsta4eq, hstd4eq, hste4eq⟩ :=
    hacc3.invoke_run hclose fopposite hB1 hnB hCapRange hpopposite root.isLt
  have hsta4 : Marks "sta" n 1 Base (fun _ => 0) sigma4 := by
    simpa [Base] using hsta3.of_eq hsta4eq
  have hstd4 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma4 :=
    hstd3.of_eq hstd4eq
  have hste4 : Marks "ste" n 1 Base (fun _ => 0) sigma4 :=
    hste3.of_eq hste4eq
  obtain ⟨sigma5, K5, r5, hK5, hsta5raw, hacc5⟩ :=
    hacc4.stamp_run hclose (_root_.Or.inl rfl) hB1 hnB hrowo hendo htmpo hsta4
  have hsta5 : Marks "sta" n 1 Adj (fun _ => 0) sigma5 :=
    hsta5raw.congr hAdjEq
  have hstd5 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma5 :=
    hstd4.of_eq (r5.frame_arr "std" (by
      simp [stampTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hste5 : Marks "ste" n 1 Base (fun _ => 0) sigma5 :=
    hste4.of_eq (r5.frame_arr "ste" (by
      simp [stampTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))

  obtain ⟨sigma6, tot, Aot, r6, hacc6, hrowot, hendot, htmpot,
      hsta6eq, hstd6eq, hste6eq⟩ :=
    hacc5.invoke_run hclose foppositeTrans hB1 hnB hCapRange
      hpoppositeTrans root.isLt
  have hsta6 : Marks "sta" n 1 Adj (fun _ => 0) sigma6 :=
    hsta5.of_eq hsta6eq
  have hstd6 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma6 :=
    hstd5.of_eq hstd6eq
  have hste6 : Marks "ste" n 1 Base (fun _ => 0) sigma6 :=
    hste5.of_eq hste6eq
  obtain ⟨sigma7, K7, r7, hK7, hstd7, hacc7⟩ :=
    hacc6.stamp_run hclose (_root_.Or.inr (_root_.Or.inl rfl)) hB1 hnB
      hrowot hendot htmpot hstd6
  have hsta7 : Marks "sta" n 1 Adj (fun _ => 0) sigma7 :=
    hsta6.of_eq (r7.frame_arr "sta" (by
      simp [stampTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hste7 : Marks "ste" n 1 Base (fun _ => 0) sigma7 :=
    hste6.of_eq (r7.frame_arr "ste" (by
      simp [stampTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))

  obtain ⟨sigma8, tf1, Af1, r8, hacc8, hrowf1, hendf1, htmpf1,
      hsta8eq, hstd8eq, hste8eq⟩ :=
    hacc7.invoke_run hclose ffrat hB1 hnB hCapRange hpfrat root.isLt
  have hsta8 : Marks "sta" n 1 Adj (fun _ => 0) sigma8 :=
    hsta7.of_eq hsta8eq
  have hstd8 : Marks "std" n 1 OppTrans (fun _ => 0) sigma8 := by
    simpa [OppTrans] using hstd7.of_eq hstd8eq
  have hste8 : Marks "ste" n 1 Base (fun _ => 0) sigma8 :=
    hste7.of_eq hste8eq
  obtain ⟨sigma9, K9, r9, hK9, hstd9raw, hacc9⟩ :=
    hacc8.stamp_run hclose (_root_.Or.inr (_root_.Or.inl rfl)) hB1 hnB
      hrowf1 hendf1 htmpf1 hstd8
  have hstd9 : Marks "std" n 1 Dm (fun _ => 0) sigma9 :=
    hstd9raw.congr hDmEq
  have hsta9 : Marks "sta" n 1 Adj (fun _ => 0) sigma9 :=
    hsta8.of_eq (r9.frame_arr "sta" (by
      simp [stampTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hste9 : Marks "ste" n 1 Base (fun _ => 0) sigma9 :=
    hste8.of_eq (r9.frame_arr "ste" (by
      simp [stampTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))

  obtain ⟨sigma10, tt, At, r10, hacc10, hrowt, hendt, htmpt,
      hsta10eq, hstd10eq, hste10eq⟩ :=
    hacc9.invoke_run hclose ftrans hB1 hnB hCapRange hptrans root.isLt
  have hsta10 : Marks "sta" n 1 Adj (fun _ => 0) sigma10 :=
    hsta9.of_eq hsta10eq
  have hstd10 : Marks "std" n 1 Dm (fun _ => 0) sigma10 :=
    hstd9.of_eq hstd10eq
  have hste10 : Marks "ste" n 1 (Base ∪ ∅) (fun _ => 0) sigma10 := by
    simpa using hste9.of_eq hste10eq
  have hacc10' : AugRowAcc n W (root : ℕ) P Cap (Base ∪ ∅)
      E Deg ER ID BH BV BN baseEnv sigma10 := by
    simpa using hacc10
  have hfeT : ∀ p, p < tt → fe (At p) ⊆ Cap := by
    intro p hp
    apply hfeDemand (At p)
    rw [← hDemandEq]
    exact Finset.mem_union_left _
      ((hrowt.mem_valSet_iff (At p)).2 ⟨p, hp, rfl⟩)
  obtain ⟨sigma11, K11, r11, hK11, hste11, hsta11, hstd11, hrank11,
      hacc11⟩ :=
    hacc10'.augBuffer_run hclose hrkv hrka hrks hB1 hnB root.isLt hRR
      (by
        simp only [Base, Adj]
        rw [adjSet_eq_direction_union,
          Lax3Proofs.RamDriverAugment.valSet_union]
        exact Finset.subset_union_left)
      hCapRange hrowt hendt htmpt hfeT hste10 hsta10 hstd10
      (hrankP sigma10 hacc10.persistent)
  let TCand : Finset ℕ := bufferAcc tt At fe

  obtain ⟨sigma12, tf2, Af2, r12, hacc12, hrowf2, hendf2, htmpf2,
      hsta12eq, hstd12eq, hste12eq⟩ :=
    hacc11.invoke_run hclose ffrat hB1 hnB hCapRange hpfrat root.isLt
  have hsta12 : Marks "sta" n 1 Adj (fun _ => 0) sigma12 :=
    hsta11.of_eq hsta12eq
  have hstd12 : Marks "std" n 1 Dm (fun _ => 0) sigma12 :=
    hstd11.of_eq hstd12eq
  have hste12 : Marks "ste" n 1 (Base ∪ (TCand ∪ ∅))
      (fun _ => 0) sigma12 := by
    simpa [TCand] using hste11.of_eq hste12eq
  have hacc12' : AugRowAcc n W (root : ℕ) P Cap (Base ∪ (TCand ∪ ∅))
      E Deg ER ID BH BV BN baseEnv sigma12 := by
    simpa [TCand] using hacc12
  have hfeF : ∀ p, p < tf2 → fe (Af2 p) ⊆ Cap := by
    intro p hp
    apply hfeDemand (Af2 p)
    rw [← hDemandEq]
    exact Finset.mem_union_right _
      ((hrowf2.mem_valSet_iff (Af2 p)).2 ⟨p, hp, rfl⟩)
  obtain ⟨sigma13, K13, r13, hK13, hste13raw, hsta13, hstd13, hrank13,
      hacc13raw⟩ :=
    hacc12'.augBuffer_run hclose hrkv hrka hrks hB1 hnB root.isLt hRR
      (by
        simp only [Base, Adj]
        rw [adjSet_eq_direction_union,
          Lax3Proofs.RamDriverAugment.valSet_union]
        exact Finset.subset_union_left)
      hCapRange hrowf2 hendf2 htmpf2 hfeF hste12 hsta12 hstd12
      (hrankP sigma12 hacc12.persistent)
  let FCand : Finset ℕ := bufferAcc tf2 Af2 fe
  have hTCand : TCand = Trans.biUnion fe := by
    simpa [TCand, Trans] using bufferAcc_eq_biUnion_valSet hrowt fe
  have hFCand : FCand = Frat.biUnion fe := by
    simpa [FCand, Frat] using bufferAcc_eq_biUnion_valSet hrowf2 fe
  have hCandidates : TCand ∪ FCand = Cand := by
    rw [hTCand, hFCand, ← Finset.union_biUnion, hDemandEq, hCandUnion]
  have hCapEq : Base ∪ Cand = Cap := by
    simp only [Base, Cand, Cap]
    rw [orientSet_augOr_eq,
      Lax3Proofs.RamDriverAugment.valSet_union]
  have hFinal :
      Base ∪ (TCand ∪ ∅ ∪ bufferAcc tf2 Af2
        (virtualAugFe dir Adj Dm RR (root : ℕ))) = Cap := by
    change Base ∪ (TCand ∪ ∅ ∪ FCand) = Cap
    calc
      Base ∪ (TCand ∪ ∅ ∪ FCand) = Base ∪ (TCand ∪ FCand) := by simp
      _ = Base ∪ Cand := by rw [hCandidates]
      _ = Cap := hCapEq
  have hste13 : Marks "ste" n 1 Cap (fun _ => 0) sigma13 := by
    exact hste13raw.congr hFinal
  have hacc13 : AugRowAcc n W (root : ℕ) P Cap Cap
      E Deg ER ID BH BV BN baseEnv sigma13 := by
    simpa only [hFinal] using hacc13raw
  have hRunExact :=
    r1.seq <| r2.seq <| r3.seq <| r4.seq <| r5.seq <| r6.seq <|
      r7.seq <| r8.seq <| r9.seq <| r10.seq <| r11.seq <| r12.seq r13
  have hbCard : tb = (orientSet dir Or root).card := by
    simpa using hrowb.tail_eq
  have hoCard : tOpp = (oppositeOrientSet dir Or root).card := by
    simpa using hrowo.tail_eq
  have hotCard : tot = (oppositeTransSet dir Or root).card := by
    simpa using hrowot.tail_eq
  have hf1Card : tf1 = (fratNbrs Or root).card := by
    simpa using hrowf1.tail_eq
  have htCard : tt = (transSet dir Or root).card := by
    simpa using hrowt.tail_eq
  have hf2Card : tf2 = (fratNbrs Or root).card := by
    simpa using hrowf2.tail_eq
  rw [hbCard] at hK2 hK3
  rw [hoCard] at hK5
  rw [hotCard] at hK7
  rw [hf1Card] at hK9
  rw [htCard] at hK11
  rw [hf2Card] at hK13
  have hRunBound :
      Run B (virtualAugAccumulate dir rk base opposite trans oppositeTrans frat)
        sigma0 sigma13
        (virtualAugAccumulateCost dir Or kbase kopposite ktrans
          koppositeTrans kfrat root) := by
    apply hRunExact.mono
    rw [virtualAugAccumulateCost_of_lt dir Or kbase kopposite ktrans
      koppositeTrans kfrat root.isLt]
    have hrootEta : (⟨(root : ℕ), root.isLt⟩ : Fin n) = root := Fin.ext rfl
    rw [hrootEta]
    omega
  have hstaFinal :
      Marks "sta" n 1 (valSet (Lax3Proofs.RamAugment.adjSet Or root))
        (fun _ => 0) sigma13 := by
    simpa [Adj] using hsta13
  have hstdFinal :
      Marks "std" n 1 (valSet ((oppositeDemandSet dir Or root).erase root))
        (fun _ => 0) sigma13 := by
    simpa [Dm] using hstd13
  exact ⟨sigma13,
    virtualAugAccumulateCost dir Or kbase kopposite ktrans
      koppositeTrans kfrat root,
    hRunBound, le_rfl,
    ⟨hacc13, hstaFinal, hstdFinal, hste13, hrank13⟩⟩

/-- Regenerate the four stamped source rows, clear exactly their supports,
and finally clear the emitted stamp through the completed output row. -/
theorem virtualAugCleanup_run {B n W : ℕ} {dir : RankDir} {rk : String}
    {P : Env → Prop} {Or : Orientation n} {rank : Fin n → ℕ}
    {RR : ℕ → ℕ} {root : Fin n}
    {base opposite oppositeTrans frat : Com}
    {kbase kopposite koppositeTrans kfrat : ℕ → ℕ}
    {E Deg ER ID BH BV BN : ℕ → ℕ} {sigma0 baseEnv : Env}
    (hclose : AugScratchClosed P)
    (fbase : AugInvokeFrames base) (fopposite : AugInvokeFrames opposite)
    (foppositeTrans : AugInvokeFrames oppositeTrans)
    (ffrat : AugInvokeFrames frat)
    (hB1 : 1 < B) (hnB : n < B)
    (hrankP : ∀ sigma, P sigma → sigma.arrs rk = arrOf n RR)
    (hpbase : ProvidesSetRows B n W (fun w => orientSet dir Or w)
      P "vtmp" base kbase)
    (hpopposite : ProvidesSetRows B n W (oppositeOrientSet dir Or)
      P "vtmp" opposite kopposite)
    (hpoppositeTrans : ProvidesSetRows B n W (oppositeTransSet dir Or)
      P "vtmp" oppositeTrans koppositeTrans)
    (hpfrat : ProvidesSetRows B n W (fratNbrs Or)
      P "vtmp" frat kfrat)
    (hacc0 : AugAccumulated n W root P rk
      (valSet (orientSet dir (augOr Or rank) root))
      (valSet (Lax3Proofs.RamAugment.adjSet Or root))
      (valSet ((oppositeDemandSet dir Or root).erase root))
      RR E Deg ER ID BH BV BN baseEnv sigma0) :
    ∃ sigma K,
      Run B (virtualAugCleanup base opposite oppositeTrans frat) sigma0 sigma K ∧
      K ≤ virtualAugCleanupCost dir Or rank kbase kopposite
        koppositeTrans kfrat root ∧
      AugCleaned n W root P rk
        (valSet (orientSet dir (augOr Or rank) root))
        RR E Deg ER ID BH BV BN baseEnv sigma := by
  classical
  let Base : Finset ℕ := valSet (orientSet dir Or root)
  let OppRow : Finset ℕ := valSet (oppositeOrientSet dir Or root)
  let Adj : Finset ℕ := valSet (Lax3Proofs.RamAugment.adjSet Or root)
  let OppTrans : Finset ℕ := valSet (oppositeTransSet dir Or root)
  let Frat : Finset ℕ := valSet (fratNbrs Or root)
  let Dm : Finset ℕ := valSet ((oppositeDemandSet dir Or root).erase root)
  let Cap : Finset ℕ := valSet (orientSet dir (augOr Or rank) root)
  have hCapRange : Cap ⊆ Finset.range n := by
    intro z hz
    exact Finset.mem_range.2 (valSet_lt hz)
  have hAdjEq : Base ∪ OppRow = Adj := by
    simp only [Base, OppRow, Adj]
    rw [← Lax3Proofs.RamDriverAugment.valSet_union,
      ← adjSet_eq_direction_union]
  have hDmEq : OppTrans ∪ Frat = Dm := by
    simp only [OppTrans, Frat, Dm]
    rw [← Lax3Proofs.RamDriverAugment.valSet_union,
      ← oppositeDemandSet_erase_eq_union]

  obtain ⟨sigma1, tb, Ab, r1, hrowacc1, hrowb, hendb, htmpb,
      hsta1eq, hstd1eq, hste1eq⟩ :=
    hacc0.acc.invoke_run hclose fbase hB1 hnB hCapRange hpbase root.isLt
  have hsta1 : Marks "sta" n 1 Adj (fun _ => 0) sigma1 :=
    hacc0.adjacency.of_eq hsta1eq
  have hstd1 : Marks "std" n 1 Dm (fun _ => 0) sigma1 :=
    hacc0.opposite.of_eq hstd1eq
  have hste1 : Marks "ste" n 1 Cap (fun _ => 0) sigma1 :=
    hacc0.emitted.of_eq hste1eq
  obtain ⟨sigma2, K2, r2, hK2, hsta2, hrowacc2⟩ :=
    hrowacc1.clear_run hclose (_root_.Or.inl rfl) hB1 hnB
      hrowb hendb htmpb hsta1
  have hstd2 : Marks "std" n 1 Dm (fun _ => 0) sigma2 :=
    hstd1.of_eq (r2.frame_arr "std" (by
      simp [clearTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hste2 : Marks "ste" n 1 Cap (fun _ => 0) sigma2 :=
    hste1.of_eq (r2.frame_arr "ste" (by
      simp [clearTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))

  obtain ⟨sigma3, tOpp, Ao, r3, hrowacc3, hrowo, hendo, htmpo,
      hsta3eq, hstd3eq, hste3eq⟩ :=
    hrowacc2.invoke_run hclose fopposite hB1 hnB hCapRange
      hpopposite root.isLt
  have hsta3 : Marks "sta" n 1 (Adj \ Base) (fun _ => 0) sigma3 :=
    hsta2.of_eq hsta3eq
  have hstd3 : Marks "std" n 1 Dm (fun _ => 0) sigma3 :=
    hstd2.of_eq hstd3eq
  have hste3 : Marks "ste" n 1 Cap (fun _ => 0) sigma3 :=
    hste2.of_eq hste3eq
  obtain ⟨sigma4, K4, r4, hK4, hsta4raw, hrowacc4⟩ :=
    hrowacc3.clear_run hclose (_root_.Or.inl rfl) hB1 hnB
      hrowo hendo htmpo hsta3
  have hsta4 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma4 := by
    apply hsta4raw.congr
    change (Adj \ Base) \ OppRow = ∅
    rw [← hAdjEq]
    ext z
    simp
    aesop
  have hstd4 : Marks "std" n 1 Dm (fun _ => 0) sigma4 :=
    hstd3.of_eq (r4.frame_arr "std" (by
      simp [clearTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hste4 : Marks "ste" n 1 Cap (fun _ => 0) sigma4 :=
    hste3.of_eq (r4.frame_arr "ste" (by
      simp [clearTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))

  obtain ⟨sigma5, tOt, Aot, r5, hrowacc5, hrowot, hendot, htmpot,
      hsta5eq, hstd5eq, hste5eq⟩ :=
    hrowacc4.invoke_run hclose foppositeTrans hB1 hnB hCapRange
      hpoppositeTrans root.isLt
  have hsta5 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma5 :=
    hsta4.of_eq hsta5eq
  have hstd5 : Marks "std" n 1 Dm (fun _ => 0) sigma5 :=
    hstd4.of_eq hstd5eq
  have hste5 : Marks "ste" n 1 Cap (fun _ => 0) sigma5 :=
    hste4.of_eq hste5eq
  obtain ⟨sigma6, K6, r6, hK6, hstd6, hrowacc6⟩ :=
    hrowacc5.clear_run hclose (_root_.Or.inr (_root_.Or.inl rfl))
      hB1 hnB hrowot hendot htmpot hstd5
  have hsta6 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma6 :=
    hsta5.of_eq (r6.frame_arr "sta" (by
      simp [clearTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hste6 : Marks "ste" n 1 Cap (fun _ => 0) sigma6 :=
    hste5.of_eq (r6.frame_arr "ste" (by
      simp [clearTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))

  obtain ⟨sigma7, tf, Af, r7, hrowacc7, hrowf, hendf, htmpf,
      hsta7eq, hstd7eq, hste7eq⟩ :=
    hrowacc6.invoke_run hclose ffrat hB1 hnB hCapRange hpfrat root.isLt
  have hsta7 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma7 :=
    hsta6.of_eq hsta7eq
  have hstd7 : Marks "std" n 1 (Dm \ OppTrans) (fun _ => 0) sigma7 :=
    hstd6.of_eq hstd7eq
  have hste7 : Marks "ste" n 1 Cap (fun _ => 0) sigma7 :=
    hste6.of_eq hste7eq
  obtain ⟨sigma8, K8, r8, hK8, hstd8raw, hrowacc8⟩ :=
    hrowacc7.clear_run hclose (_root_.Or.inr (_root_.Or.inl rfl))
      hB1 hnB hrowf hendf htmpf hstd7
  have hstd8 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma8 := by
    apply hstd8raw.congr
    change (Dm \ OppTrans) \ Frat = ∅
    rw [← hDmEq]
    ext z
    simp
    aesop
  have hsta8 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma8 :=
    hsta7.of_eq (r8.frame_arr "sta" (by
      simp [clearTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hste8 : Marks "ste" n 1 Cap (fun _ => 0) sigma8 :=
    hste7.of_eq (r8.frame_arr "ste" (by
      simp [clearTmp, scanTmp, bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))

  obtain ⟨Aout, hAout, hcout, hrowout⟩ := hrowacc8.fill.toSetRowRep
  have hcardB : (orientSet dir (augOr Or rank) root).card < B :=
    lt_of_le_of_lt hrowout.tail_le hnB
  have ecount : (Expr.var "c").evalB B sigma8 =
      some (orientSet dir (augOr Or rank) root).card := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma8) (by
      rw [hcout]
      exact hcardB)
    rwa [hcout] at h
  let sigma9 := sigma8.setVar "avend"
    (orientSet dir (augOr Or rank) root).card
  have r9 : Run B (.assign "avend" (.var "c")) sigma8 sigma9 2 :=
    Run.assign ecount
  have hrowacc9 : AugRowAcc n W (root : ℕ) P Cap Cap
      E Deg ER ID BH BV BN baseEnv sigma9 :=
    hrowacc8.setVar hclose (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hsta9 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma9 :=
    hsta8.setVar _ _
  have hstd9 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma9 :=
    hstd8.setVar _ _
  have hste9 : Marks "ste" n 1 Cap (fun _ => 0) sigma9 :=
    hste8.setVar _ _
  have hendout : sigma9.vars "avend" =
      (orientSet dir (augOr Or rank) root).card := by
    simp [sigma9]
  have hsrcout : sigma9.arrs "vrow" = arrOf n Aout := by
    simpa [sigma9] using hAout
  obtain ⟨sigma10, K10, r10, hK10, hste10raw⟩ :=
    clearBuffer_run (B := B) (n := n)
      (tail := (orientSet dir (augOr Or rank) root).card)
      (src := "vrow") (j := "avj") (jend := "avend") (u := "u")
      (s := "ste") (S := orientSet dir (augOr Or rank) root)
      (M := Cap) (A := Aout) (sigma := sigma9)
      (by decide) (by decide) (by decide) (by decide)
      hB1 hnB hrowout hendout hsrcout hste9
  have hrowacc10 : AugRowAcc n W (root : ℕ) P Cap Cap
      E Deg ER ID BH BV BN baseEnv sigma10 :=
    hrowacc9.run_bufferStore_private hclose
      (_root_.Or.inr (_root_.Or.inr rfl)) r10
  have hste10 : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma10 := by
    apply hste10raw.congr
    simp [Cap]
  have hsta10 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma10 :=
    hsta9.of_eq (r10.frame_arr "sta" (by
      simp [bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hstd10 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma10 :=
    hstd9.of_eq (r10.frame_arr "std" (by
      simp [bufferScan,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.warrs]))
  have hrank10 : sigma10.arrs rk = arrOf n RR :=
    hrankP sigma10 hrowacc10.persistent
  have hRunExact :=
    r1.seq <| r2.seq <| r3.seq <| r4.seq <| r5.seq <| r6.seq <|
      r7.seq <| r8.seq <| r9.seq r10
  have hbCard : tb = (orientSet dir Or root).card := by
    simpa using hrowb.tail_eq
  have hoCard : tOpp = (oppositeOrientSet dir Or root).card := by
    simpa using hrowo.tail_eq
  have hotCard : tOt = (oppositeTransSet dir Or root).card := by
    simpa using hrowot.tail_eq
  have hfCard : tf = (fratNbrs Or root).card := by
    simpa using hrowf.tail_eq
  rw [hbCard] at hK2
  rw [hoCard] at hK4
  rw [hotCard] at hK6
  rw [hfCard] at hK8
  have hRunBound :
      Run B (virtualAugCleanup base opposite oppositeTrans frat)
        sigma0 sigma10
        (virtualAugCleanupCost dir Or rank kbase kopposite
          koppositeTrans kfrat root) := by
    apply hRunExact.mono
    rw [virtualAugCleanupCost_of_lt dir Or rank kbase kopposite
      koppositeTrans kfrat root.isLt]
    have hrootEta : (⟨(root : ℕ), root.isLt⟩ : Fin n) = root := Fin.ext rfl
    rw [hrootEta]
    omega
  exact ⟨sigma10,
    virtualAugCleanupCost dir Or rank kbase kopposite
      koppositeTrans kfrat root,
    hRunBound, le_rfl,
    ⟨hrowacc10, hsta10, hstd10, hste10, hrank10⟩⟩

/-- One complete augmentation provider.  Its public memory is the reusable
zeroed assembler workspace around the child providers' persistent memory. -/
theorem virtualAugProvidesSetRows {B n W : ℕ} {dir : RankDir} {rk : String}
    {P : Env → Prop} {Or : Orientation n} {rank : Fin n → ℕ}
    {RR : ℕ → ℕ}
    {base opposite trans oppositeTrans frat : Com}
    {kbase kopposite ktrans koppositeTrans kfrat : ℕ → ℕ}
    (hclose : AugScratchClosed P)
    (fbase : AugInvokeFrames base) (fopposite : AugInvokeFrames opposite)
    (ftrans : AugInvokeFrames trans)
    (foppositeTrans : AugInvokeFrames oppositeTrans)
    (ffrat : AugInvokeFrames frat)
    (hrkv : rk ≠ "vrow") (hrka : rk ≠ "@") (hrks : rk ≠ "ste")
    (hB1 : 1 < B) (hnB : n < B)
    (hrankP : ∀ sigma, P sigma → sigma.arrs rk = arrOf n RR)
    (hrank : ∀ v : Fin n, rank v = RR (v : ℕ))
    (hRR : ∀ v, v < n → RR v < n)
    (hpbase : ProvidesSetRows B n W (fun w => orientSet dir Or w)
      P "vtmp" base kbase)
    (hpopposite : ProvidesSetRows B n W (oppositeOrientSet dir Or)
      P "vtmp" opposite kopposite)
    (hptrans : ProvidesSetRows B n W (transSet dir Or)
      P "vtmp" trans ktrans)
    (hpoppositeTrans : ProvidesSetRows B n W (oppositeTransSet dir Or)
      P "vtmp" oppositeTrans koppositeTrans)
    (hpfrat : ProvidesSetRows B n W (fratNbrs Or)
      P "vtmp" frat kfrat) :
    ProvidesSetRows B n W (fun w => orientSet dir (augOr Or rank) w)
      (AugWorkspace n P) "vrow"
      (virtualAugProvide dir rk base opposite trans oppositeTrans frat)
      (virtualAugCost dir Or rank kbase kopposite ktrans koppositeTrans kfrat) := by
  classical
  intro root E Deg ER ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hwork, heng, hw⟩ := hpre
  have hrootB : (root : ℕ) < B := lt_trans root.isLt hnB
  have ew : (Expr.var "w").evalB B sigma = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "w") (σ := sigma) (by
      rw [hw]
      exact hrootB)
    rwa [hw] at h
  let sigma1 := sigma.setVar "avroot" (root : ℕ)
  have r1 : Run B (.assign "avroot" (.var "w")) sigma sigma1 2 :=
    Run.assign ew
  have hP1 : P sigma1 := hclose.setVar (by decide) hwork.persistent
  have heng1 : EngineArrays n W E Deg ER ID BH BV BN sigma1 :=
    heng.setVar "avroot" (root : ℕ) (by decide)
  let sigma2 := sigma1.setVar "c" 0
  have r2 : Run B (.assign "c" (.lit 0)) sigma1 sigma2 2 :=
    Run.assign (evalB_lit (by omega))
  have hP2 : P sigma2 := hclose.setVar (by decide) hP1
  have heng2 : EngineArrays n W E Deg ER ID BH BV BN sigma2 :=
    heng1.setVar "c" 0 (by decide)
  have hstable2 : ProviderStable sigma sigma2 :=
    ⟨by simp [sigma2, sigma1], by simp [sigma2, sigma1],
      by simp [sigma2, sigma1], by simp [sigma2, sigma1],
      by simp [sigma2, sigma1], by simp [sigma2, sigma1],
      by simp [sigma2, sigma1], by simp [sigma2, sigma1]⟩
  let Cap : Finset ℕ := valSet (orientSet dir (augOr Or rank) root)
  obtain ⟨A0, hA0⟩ :=
    Lax3Proofs.RamDriver.exists_arrOf hwork.output_length
  have hfill2 : RowFillAcc "vrow" n Cap (∅ : Finset ℕ) sigma2 := by
    refine ⟨Finset.empty_subset _, A0, ?_, ?_, ?_, ?_⟩
    · simpa [sigma2, sigma1] using hA0
    · simp [sigma2]
    · simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
    · intro z
      simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
  have hacc2 : AugRowAcc n W (root : ℕ) P Cap ∅
      E Deg ER ID BH BV BN sigma sigma2 :=
    ⟨hfill2, hP2, heng2, hstable2,
      by simpa [sigma2, sigma1] using hw,
      by simp [sigma2, sigma1],
      by simpa [sigma2, sigma1] using hwork.tmp_length,
      by simpa [sigma2, sigma1] using hwork.save_length⟩
  have hsta2 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma2 :=
    ⟨fun _ => 0, by simpa [sigma2, sigma1] using hwork.adjacency_zero,
      by simp⟩
  have hstd2 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma2 :=
    ⟨fun _ => 0, by simpa [sigma2, sigma1] using hwork.opposite_zero,
      by simp⟩
  have hste2 : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma2 :=
    ⟨fun _ => 0, by simpa [sigma2, sigma1] using hwork.emitted_zero,
      by simp⟩
  obtain ⟨sigma3, K3, r3, hK3, hacc3⟩ :=
    virtualAugAccumulate_run (dir := dir) (rk := rk) (Or := Or)
      (rank := rank) (RR := RR) (root := root)
      hclose fbase fopposite ftrans foppositeTrans ffrat
      hrkv hrka hrks hB1 hnB hrankP hrank hRR
      hpbase hpopposite hptrans hpoppositeTrans hpfrat
      hacc2 hsta2 hstd2 hste2
  obtain ⟨sigma4, K4, r4, hK4, hclean4⟩ :=
    virtualAugCleanup_run (dir := dir) (rk := rk) (Or := Or)
      (rank := rank) (RR := RR) (root := root)
      hclose fbase fopposite foppositeTrans ffrat hB1 hnB hrankP
      hpbase hpopposite hpoppositeTrans hpfrat hacc3
  obtain ⟨A, hA, hc, hrow⟩ := hclean4.acc.fill.toSetRowRep
  have hcardB : (orientSet dir (augOr Or rank) root).card < B :=
    lt_of_le_of_lt hrow.tail_le hnB
  have ec : (Expr.var "c").evalB B sigma4 =
      some (orientSet dir (augOr Or rank) root).card := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma4) (by
      rw [hc]
      exact hcardB)
    rwa [hc] at h
  let sigma5 := sigma4.setVar "vtail"
    (orientSet dir (augOr Or rank) root).card
  have r5 : Run B (.assign "vtail" (.var "c")) sigma4 sigma5 2 :=
    Run.assign ec
  have hP5 : P sigma5 := hclose.setVar (by decide) hclean4.acc.persistent
  have heng5 : EngineArrays n W E Deg ER ID BH BV BN sigma5 :=
    hclean4.acc.engine.setVar "vtail" _ (by decide)
  have hstable5 : ProviderStable sigma sigma5 :=
    Lax3Proofs.Refine.OrderVirtualBaseOrient.ProviderStable.setVar_of_private
      hclean4.acc.stable (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) _
  have havroot5 : sigma5.vars "avroot" = (root : ℕ) := by
    simpa [sigma5] using hclean4.acc.saved_root
  have eroot : (Expr.var "avroot").evalB B sigma5 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "avroot") (σ := sigma5) (by
      rw [havroot5]
      exact hrootB)
    rwa [havroot5] at h
  let sigma6 := sigma5.setVar "w" (root : ℕ)
  have r6 : Run B (.assign "w" (.var "avroot")) sigma5 sigma6 2 :=
    Run.assign eroot
  have hP6 : P sigma6 := hclose.setVar (by decide) hP5
  have heng6 : EngineArrays n W E Deg ER ID BH BV BN sigma6 :=
    heng5.setVar "w" (root : ℕ) (by decide)
  have hstable6 : ProviderStable sigma sigma6 :=
    ⟨by simpa [sigma6] using hstable5.n_eq,
      by simp [sigma6, hw],
      by simpa [sigma6] using hstable5.i_eq,
      by simpa [sigma6] using hstable5.sp_eq,
      by simpa [sigma6] using hstable5.ls_eq,
      by simpa [sigma6] using hstable5.cnt_eq,
      by simpa [sigma6] using hstable5.mind_eq,
      by simpa [sigma6] using hstable5.kmax_eq⟩
  have hsta6 : Marks "sta" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma6 :=
    (hclean4.adjacency.setVar "vtail" _).setVar "w" _
  have hstd6 : Marks "std" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma6 :=
    (hclean4.opposite.setVar "vtail" _).setVar "w" _
  have hste6 : Marks "ste" n 1 (∅ : Finset ℕ) (fun _ => 0) sigma6 :=
    (hclean4.emitted.setVar "vtail" _).setVar "w" _
  have hwork6 : AugWorkspace n P sigma6 :=
    ⟨hP6,
      by simpa [sigma6, sigma5] using hclean4.acc.tmp_length,
      by rw [show sigma6.arrs "vrow" = arrOf n A by
        simpa [sigma6, sigma5] using hA, length_arrOf],
      by simpa [sigma6, sigma5] using hclean4.acc.save_length,
      array_zero_of_marks_empty hsta6,
      array_zero_of_marks_empty hstd6,
      array_zero_of_marks_empty hste6⟩
  have hRunExact := r1.seq <| r2.seq <| r3.seq <| r4.seq <| r5.seq r6
  have hRun :
      Run B (virtualAugProvide dir rk base opposite trans oppositeTrans frat)
        sigma sigma6
        (virtualAugCost dir Or rank kbase kopposite ktrans
          koppositeTrans kfrat root) := by
    apply hRunExact.mono
    simp only [virtualAugCost]
    omega
  exact ⟨sigma6,
    virtualAugCost dir Or rank kbase kopposite ktrans koppositeTrans kfrat root,
    hRun, le_rfl, hwork6, heng6, hstable6,
    (orientSet dir (augOr Or rank) root).card, A, hrow,
    by simp [sigma6, sigma5], by simpa [sigma6, sigma5] using hA⟩

#print axioms virtualAugAccumulate_run
#print axioms virtualAugCleanup_run
#print axioms virtualAugProvidesSetRows
#print axioms sum_virtualAugCost_le

end Lax3Proofs.Refine.OrderVirtualOrient
