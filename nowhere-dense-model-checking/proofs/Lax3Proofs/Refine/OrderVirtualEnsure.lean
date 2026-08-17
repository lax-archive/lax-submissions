import Lax3Proofs.Refine.OrderVirtualReady

/-!
# Capacity guard for virtual elimination

The lazy bucket engine is kept in a fixed `3*n+3` arena.  Before consuming a
regenerated row it either observes enough room for any carrier-sized row or
rebuilds the buckets into their compact one-node-per-vertex form.
-/

namespace Lax3Proofs.Refine.OrderVirtualEnsure

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.RamElim (Elim Buck BuckInv)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualBucket

/-- The mathematical and resident invariant of the virtual elimination
loop. -/
def VirtualElimSt (n : ℕ) (G : SimpleGraph (Fin n)) (P : Env → Prop)
    (E D R ID BH BV BN : ℕ → ℕ) (σ : Env) : Prop :=
  P σ ∧
    EngineArrays n (bucketExtra n) E D R ID BH BV BN σ ∧
    Elim G (fun _ => 1) E D R ID
      (σ.vars "cnt") (σ.vars "mind") (σ.vars "kmax") ∧
    Buck n n E D BH BV BN (σ.vars "sp") (σ.vars "ls") ∧
    (∀ u < n, D u < n) ∧
    σ.vars "sp" < 3 * n + 3 ∧
    σ.vars "ls" + 1 ≤ σ.vars "sp" ∧
    σ.vars "mind" ≤ n ∧ σ.vars "kmax" ≤ n

def VirtualElimInv (n : ℕ) (G : SimpleGraph (Fin n)) (P : Env → Prop)
    (σ : Env) : Prop :=
  ∃ E D R ID BH BV BN, VirtualElimSt n G P E D R ID BH BV BN σ

/-- The threshold `2*n+3` leaves `n` further slots strictly below the
physical length `3*n+3`. -/
def virtualRoomCond : Cond :=
  .lt (.var "sp")
    (.add (.mul (.lit 2) (.var "n")) (.lit 3))

def ensureVirtualBuckets : Com :=
  .ite virtualRoomCond .skip rebuildBuckets

def ensureVirtualBucketsCost (n : ℕ) : ℕ :=
  rebuildBucketsCost n + 8

structure EnsureSkipEffect (σ σ' : Env) (K : ℕ) : Prop where
  cost : K ≤ 9
  state_eq : σ' = σ

structure EnsureRebuildEffect (n : ℕ) (σ σ' : Env) (K : ℕ) : Prop where
  cost : K ≤ rebuildBucketsCost n + 8
  old_sp_large : 2 * n + 3 ≤ σ.vars "sp"
  sp_eq : σ'.vars "sp" = n + 1
  ls_eq : σ'.vars "ls" = n
  cnt_eq : σ'.vars "cnt" = σ.vars "cnt"
  mind_eq : σ'.vars "mind" = σ.vars "mind"
  kmax_eq : σ'.vars "kmax" = σ.vars "kmax"
  elm_eq : σ'.arrs "elm" = σ.arrs "elm"

def EnsureEffect (n : ℕ) (σ σ' : Env) (K : ℕ) : Prop :=
  EnsureSkipEffect σ σ' K ∨ EnsureRebuildEffect n σ σ' K

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

private theorem virtualRoomCond_eval {B n : ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hB : 3 * n + 3 < B)
    (hsp : σ.vars "sp" < 3 * n + 3) :
    virtualRoomCond.evalB B σ = some (decide (σ.vars "sp" < 2 * n + 3)) := by
  have hsB : σ.vars "sp" < B := by omega
  have h2B : 2 < B := by omega
  have hnB : n < B := by omega
  have h2nB : 2 * n < B := by omega
  have h3B : 3 < B := by omega
  have hsumB : 2 * n + 3 < B := by omega
  have hne : (Expr.var "n").evalB B σ = some n := by
    have he := evalB_var (B := B) (x := "n") (σ := σ) (by rw [hn]; exact hnB)
    simpa [hn] using he
  refine evalB_condLt (evalB_var hsB) ?_
  refine evalB_bin (evalB_bin (evalB_lit h2B) hne ?_) (evalB_lit h3B) ?_
  · simpa using h2nB
  · simpa using hsumB

/-- The guard returns the same abstract elimination state with possibly
rebuilt bucket arrays and enough space for any row of length at most `n`. -/
theorem ensureVirtualBuckets_spec {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} (hclosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B) {E D R ID BH BV BN : ℕ → ℕ} :
    Spec B
      (VirtualElimSt n G P E D R ID BH BV BN)
      ensureVirtualBuckets
      (fun _ σ' =>
        ∃ BH' BV' BN',
          VirtualElimSt n G P E D R ID BH' BV' BN' σ' ∧
          σ'.vars "sp" < 2 * n + 3)
      (ensureVirtualBucketsCost n) := by
  intro σ hst
  obtain ⟨hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩ := hst
  have hcond := virtualRoomCond_eval heng.n_eq hB hsp
  by_cases hroom : σ.vars "sp" < 2 * n + 3
  · refine ⟨σ, (Run.ite_true (by simpa [hroom] using hcond) Run.skip).mono ?_,
      BH, BV, BN, ?_, hroom⟩
    · simp [ensureVirtualBuckets, ensureVirtualBucketsCost, virtualRoomCond,
        rebuildBucketsCost, Cond.size, Expr.size]
    · exact ⟨hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩
  · obtain ⟨σ', hr, hbuckI, hi'⟩ :=
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
    have hcnt' : σ'.vars "cnt" = σ.vars "cnt" := hr.frame_var "cnt" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.wvars])
    have hmind' : σ'.vars "mind" = σ.vars "mind" := hr.frame_var "mind" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.wvars])
    have hkmax' : σ'.vars "kmax" = σ.vars "kmax" := hr.frame_var "kmax" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.wvars])
    refine ⟨σ',
      (Run.ite_false (by simpa [hroom] using hcond) hr).mono ?_,
      BH', BV', BN', ?_, ?_⟩
    · simp [ensureVirtualBuckets, ensureVirtualBucketsCost, virtualRoomCond,
        Cond.size, Expr.size]
      omega
    · refine ⟨hP', ⟨hn', helm', hdeg', hrnk', hidg', hbh', hbv', hbn'⟩,
        ?_, ?_, hD, ?_, ?_, ?_, ?_⟩
      · simpa [hcnt', hmind', hkmax'] using helim
      · simpa [hi'] using hbuck0.weaken E
      · omega
      · omega
      · omega
      · omega
    · omega

/-- The same guard with its actual branch exposed.  This is the form needed
by amortized composition: a successful test costs only eight, while a rebuild
is paid by the drop in the arena pointer. -/
theorem ensureVirtualBuckets_run {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} (hclosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B) {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (hst : VirtualElimSt n G P E D R ID BH BV BN σ) :
    ∃ σ' K BH' BV' BN',
      Run B ensureVirtualBuckets σ σ' K ∧
      VirtualElimSt n G P E D R ID BH' BV' BN' σ' ∧
      σ'.vars "sp" < 2 * n + 3 ∧ EnsureEffect n σ σ' K := by
  obtain ⟨hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩ := hst
  have hcond := virtualRoomCond_eval heng.n_eq hB hsp
  by_cases hroom : σ.vars "sp" < 2 * n + 3
  · refine ⟨σ, 9, BH, BV, BN,
      (Run.ite_true (by simpa [hroom] using hcond) Run.skip).mono ?_,
      ⟨hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩,
      hroom, Or.inl ⟨by omega, rfl⟩⟩
    simp [ensureVirtualBuckets, virtualRoomCond, Cond.size, Expr.size]
  · obtain ⟨σ', hr, hbuckI, hi'⟩ :=
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
    have hcnt' : σ'.vars "cnt" = σ.vars "cnt" := hr.frame_var "cnt" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.wvars])
    have hmind' : σ'.vars "mind" = σ.vars "mind" := hr.frame_var "mind" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.wvars])
    have hkmax' : σ'.vars "kmax" = σ.vars "kmax" := hr.frame_var "kmax" (by
      simp [rebuildBuckets, Lax3Proofs.RamDriver.fillUpto,
        Lax3Proofs.RamElim.initBuck, Lax3Proofs.RamElim.initBuckRow,
        Lax3Proofs.RamElim.push, Lax13Proofs.Reasoning.Lib.Fill.put, Com.wvars])
    have helmFrame : σ'.arrs "elm" = σ.arrs "elm" := by
      rw [helm', heng.elm_eq]
    refine ⟨σ', rebuildBucketsCost n + 8, BH', BV', BN',
      (Run.ite_false (by simpa [hroom] using hcond) hr).mono ?_, ?_, ?_,
      Or.inr ⟨by omega, by omega, by omega, by omega,
        hcnt', hmind', hkmax', helmFrame⟩⟩
    · simp [ensureVirtualBuckets, virtualRoomCond, Cond.size, Expr.size,
        Nat.add_comm]
    · refine ⟨hP', ⟨hn', helm', hdeg', hrnk', hidg', hbh', hbv', hbn'⟩,
        ?_, ?_, hD, ?_, ?_, ?_, ?_⟩
      · simpa [hcnt', hmind', hkmax'] using helim
      · simpa [hi'] using hbuck0.weaken E
      · omega
      · omega
      · omega
      · omega
    · omega

/-- A guarded state has room for every provider row. -/
theorem room_for_row {n tail : ℕ} (hsp : tail ≤ n)
    {s : ℕ} (hs : s < 2 * n + 3) :
    s + tail < n + bucketExtra n + 1 := by
  simp [bucketExtra]
  omega

/-! ## Axiom audit -/

#print axioms ensureVirtualBuckets_spec
#print axioms ensureVirtualBuckets_run
#print axioms room_for_row

end Lax3Proofs.Refine.OrderVirtualEnsure
