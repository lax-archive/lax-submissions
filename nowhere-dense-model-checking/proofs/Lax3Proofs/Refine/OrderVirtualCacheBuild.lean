import Lax3Proofs.Refine.OrderVirtualCacheProvider

/-!
# Constructing the heavy incoming-row cache

This file starts the executable construction side of the heavy/light repair.
The first primitive appends the exact live prefix of `vrow` to a compact
target arena at the pointer in `cnt`.  Its semantic result is a functional
segment update, which is the representation used by the outer cache-builder
invariant.
-/

namespace Lax3Proofs.Refine.OrderVirtualCacheBuild

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Refine.OrderVirtualSetRow (bufferScan bufferScanC_run)
open Lax3Proofs.Refine.OrderVirtualSetRow (SetRowRep)
open Lax3Proofs.Refine.OrderVirtualBaseProvider (csrRowFun BoundedCsr)
open Lax3Proofs.Refine.OrderVirtualSetCsr (SetCsrRows)
open Lax3Proofs.Refine.OrderVirtualCacheMath (heavyRoots heavyInSlots)
open Lax3Proofs.Refine.OrderVirtualCacheProvider (heavyInRows)
open Lax3Proofs.Augmentation (Orientation)

variable {n : ℕ}

/-- Replace the half-open segment `[base, base + used)` by the corresponding
prefix of `A`. -/
def appendAt (T A : ℕ → ℕ) (base used q : ℕ) : ℕ :=
  if base ≤ q ∧ q < base + used then A (q - base) else T q

@[simp] theorem appendAt_zero (T A : ℕ → ℕ) (base q : ℕ) :
    appendAt T A base 0 q = T q := by
  simp [appendAt]

theorem appendAt_slot (T A : ℕ → ℕ) {base used p : ℕ}
    (hp : p < used) :
    appendAt T A base used (base + p) = A p := by
  simp [appendAt]
  omega

theorem appendAt_before (T A : ℕ → ℕ) {base used q : ℕ}
    (hq : q < base) : appendAt T A base used q = T q := by
  simp [appendAt]
  omega

theorem appendAt_succ_set {nt base p : ℕ} (T A : ℕ → ℕ) :
    (arrOf nt (appendAt T A base p)).set (base + p) (A p) =
      arrOf nt (appendAt T A base (p + 1)) := by
  rw [set_arrOf_eq_upd]
  apply arrOf_congr
  intro q hq
  simp only [upd, appendAt]
  by_cases hqp : q = base + p
  · subst q
    simp
  · by_cases hold : base ≤ q ∧ q < base + p
    · have hnew : base ≤ q ∧ q < base + (p + 1) := by omega
      simp [hqp, hold, hnew]
    · have hnew : ¬ (base ≤ q ∧ q < base + (p + 1)) := by
        intro h
        have : q = base + p := by omega
        exact hqp this
      simp [hqp, hold, hnew]

/-- Append the value already loaded into `u` and advance the cache pointer. -/
def cacheAppendSlot (tgt : String) : Com :=
  .seq (.store tgt (.var "cnt") (.var "u"))
    (.assign "cnt" (.add (.var "cnt") (.lit 1)))

/-- Scan the exact provider row and append it to `tgt`. -/
def cacheAppend (tgt : String) : Com :=
  bufferScan "vrow" "hcj" "vtail" "u" (cacheAppendSlot tgt)

/-- The state threaded through the live-prefix append scan. -/
structure AppendInv (n nt base tail p : ℕ) (tgt : String)
    (A T : ℕ → ℕ) (sigma : Env) : Prop where
  src : sigma.arrs "vrow" = arrOf n A
  tgt_eq : sigma.arrs tgt = arrOf nt (appendAt T A base p)
  count : sigma.vars "cnt" = base + p
  finish : sigma.vars "vtail" = tail
  pos : sigma.vars "hcj" = p
  le : p ≤ tail

/-- One append slot extends the represented target segment by one cell. -/
theorem cacheAppendSlot_run {B n nt base tail p : ℕ} {tgt : String}
    {A T : ℕ → ℕ} {sigma : Env}
    (htv : tgt ≠ "vrow") (hcu : "cnt" ≠ "u")
    (hcjcnt : "hcj" ≠ "cnt") (hcjtail : "hcj" ≠ "vtail")
    (hcnttail : "cnt" ≠ "vtail")
    (hB1 : 1 < B) (hbaseTailB : base + tail < B)
    (hfit : base + tail ≤ nt) (hval : A p < B)
    (hp : p < tail) (hI : AppendInv n nt base tail p tgt A T sigma) :
    ∃ tau,
      Run B (cacheAppendSlot tgt) (sigma.setVar "u" (A p)) tau 7 ∧
      tau.vars "hcj" = p ∧
      AppendInv n nt base tail (p + 1) tgt A T
        (tau.setVar "hcj" (p + 1)) := by
  have hcntB : base + p < B := by omega
  have hcntSlot : base + p < nt := by omega
  let sigma0 := sigma.setVar "u" (A p)
  have ecnt : (Expr.var "cnt").evalB B sigma0 = some (base + p) := by
    have hcnt0 : sigma0.vars "cnt" = base + p := by
      rw [vars_setVar, if_neg hcu]
      exact hI.count
    have h := evalB_var (B := B) (x := "cnt") (σ := sigma0) (by
      rw [hcnt0]
      exact hcntB)
    rwa [hcnt0] at h
  have eu : (Expr.var "u").evalB B sigma0 = some (A p) := by
    have hu : sigma0.vars "u" = A p := by simp [sigma0]
    have h := evalB_var (B := B) (x := "u") (σ := sigma0) (by
      rw [hu]
      exact hval)
    rwa [hu] at h
  have htgt0 : sigma0.arrs tgt = arrOf nt (appendAt T A base p) := by
    simpa [sigma0] using hI.tgt_eq
  have hslot0 : base + p < (sigma0.arrs tgt).length := by
    rw [htgt0, length_arrOf]
    exact hcntSlot
  let sigma1 := sigma0.setArr tgt (base + p) (A p)
  have r1 : Run B (.store tgt (.var "cnt") (.var "u")) sigma0 sigma1 3 :=
    Run.store ecnt eu hslot0
  have htgt1 : sigma1.arrs tgt =
      arrOf nt (appendAt T A base (p + 1)) := by
    simp only [sigma1, arrs_setArr, htgt0]
    exact appendAt_succ_set T A
  have hcnt1 : sigma1.vars "cnt" = base + p := by
    simpa [sigma1, sigma0, hcu] using hI.count
  have ecnt1 : (Expr.var "cnt").evalB B sigma1 = some (base + p) := by
    have h := evalB_var (B := B) (x := "cnt") (σ := sigma1) (by
      rw [hcnt1]
      exact hcntB)
    rwa [hcnt1] at h
  have einc : (Expr.add (.var "cnt") (.lit 1)).evalB B sigma1 =
      some (base + (p + 1)) := by
    simpa only [Nat.add_assoc] using
      (evalB_bin ecnt1 (evalB_lit hB1) (by
        simp [Bop.apply]
        omega))
  let sigma2 := sigma1.setVar "cnt" (base + (p + 1))
  have r2 : Run B (.assign "cnt" (.add (.var "cnt") (.lit 1)))
      sigma1 sigma2 4 := Run.assign einc
  have hpos2 : sigma2.vars "hcj" = p := by
    simp only [sigma2, vars_setVar, if_neg hcjcnt]
    simpa [sigma1, sigma0] using hI.pos
  have hsrc2 : sigma2.arrs "vrow" = arrOf n A := by
    simp only [sigma2, arrs_setVar, sigma1, arrs_setArr,
      if_neg (Ne.symm htv), sigma0, arrs_setVar]
    exact hI.src
  have hfinish2 : sigma2.vars "vtail" = tail := by
    simp only [sigma2, vars_setVar, if_neg (Ne.symm hcnttail)]
    simpa [sigma1, sigma0] using hI.finish
  refine ⟨sigma2, ?_, hpos2, ?_⟩
  · simpa only [cacheAppendSlot, sigma0] using r1.seq r2
  refine ⟨by simpa using hsrc2, ?_, ?_, ?_, by simp, by omega⟩
  · simpa [sigma2] using htgt1
  · simp [sigma2]
  · rw [vars_setVar, if_neg (Ne.symm hcjtail)]
    exact hfinish2

/-- Appending a complete exact provider row produces precisely one updated
target segment and advances `cnt` by its live length. -/
theorem cacheAppend_run {B n nt base tail : ℕ} {tgt : String}
    {A T : ℕ → ℕ} {sigma : Env}
    (htv : tgt ≠ "vrow")
    (hB1 : 1 < B) (hbaseTailB : base + tail < B)
    (hfit : base + tail ≤ nt) (htailn : tail ≤ n)
    (hval : ∀ p, p < tail → A p < B)
    (hsrc : sigma.arrs "vrow" = arrOf n A)
    (htgt : sigma.arrs tgt = arrOf nt T)
    (hcount : sigma.vars "cnt" = base)
    (hfinish : sigma.vars "vtail" = tail) :
    ∃ tau K,
      Run B (cacheAppend tgt) sigma tau K ∧ K ≤ 18 * tail + 6 ∧
      tau.arrs "vrow" = arrOf n A ∧
      tau.arrs tgt = arrOf nt (appendAt T A base tail) ∧
      tau.vars "cnt" = base + tail ∧
      tau.vars "vtail" = tail := by
  let I : ℕ → Env → Prop := fun p tau =>
    AppendInv n nt base tail p tgt A T tau
  have hstart : I 0 (sigma.setVar "hcj" 0) := by
    refine ⟨by simpa using hsrc, ?_, ?_, ?_, by simp, by omega⟩
    · rw [arrs_setVar, htgt]
      apply arrOf_congr
      intro q _
      exact (appendAt_zero T A base q).symm
    · simpa using hcount
    · simpa using hfinish
  obtain ⟨tau, K, hr, hK, hI⟩ :=
    bufferScanC_run (B := B) (len := n) (hi := tail)
      (src := "vrow") (j := "hcj") (jend := "vtail") (u := "u")
      (body := cacheAppendSlot tgt) (costs := fun _ => 7)
      (A := A) (I := I) (sigma := sigma)
      (by decide) (by omega) hB1 htailn hfinish
      (fun _ _ h => h.src)
      hval
      (fun _ _ h => ⟨h.finish, h.pos, h.le⟩)
      (by
        intro p rho hIp hp
        obtain ⟨rho', hr', hj', hnext⟩ :=
          cacheAppendSlot_run htv (by decide) (by decide) (by decide)
            (by decide) hB1 hbaseTailB hfit (hval p hp) hp hIp
        exact ⟨rho', 7, hr', le_rfl, hj', hnext⟩)
      hstart
  refine ⟨tau, K, by simpa only [cacheAppend] using hr, ?_,
    hI.src, hI.tgt_eq, hI.count, hI.finish⟩
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hK
  omega

/-! ## Canonical offsets and the semantic cache prefix -/

/-- Length retained for numeric root `i`; roots outside the carrier have no
row. -/
noncomputable def cacheLen (D : Orientation n) (d i : ℕ) : ℕ :=
  if hi : i < n then (heavyInRows D d ⟨i, hi⟩).card else 0

@[simp] theorem cacheLen_fin (D : Orientation n) (d : ℕ) (w : Fin n) :
    cacheLen D d w = (heavyInRows D d w).card := by
  simp [cacheLen, w.isLt]

/-- Canonical prefix sum of the retained row lengths. -/
noncomputable def cacheOff (D : Orientation n) (d i : ℕ) : ℕ :=
  ∑ k ∈ Finset.range i, cacheLen D d k

@[simp] theorem cacheOff_zero (D : Orientation n) (d : ℕ) :
    cacheOff D d 0 = 0 := by
  simp [cacheOff]

theorem cacheOff_succ (D : Orientation n) (d i : ℕ) :
    cacheOff D d (i + 1) = cacheOff D d i + cacheLen D d i := by
  rw [cacheOff, Finset.sum_range_succ, cacheOff]

theorem cacheOff_mono (D : Orientation n) (d : ℕ) :
    Monotone (cacheOff D d) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

theorem rowLen_cacheOff (D : Orientation n) (d i : ℕ) :
    Csr.rowLen (cacheOff D d) i = cacheLen D d i := by
  rw [Csr.rowLen, cacheOff_succ]
  omega

theorem cacheOff_final (D : Orientation n) (d : ℕ) :
    cacheOff D d n = heavyInSlots D d := by
  classical
  rw [cacheOff, ← Fin.sum_univ_eq_sum_range (fun i => cacheLen D d i) n]
  simp only [cacheLen_fin]
  rw [heavyInSlots, heavyRoots, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : d * d <
      (Lax3Proofs.RamAugment.outSet D x).card
  · simp [heavyInRows, heavyRoots, hx]
  · simp [heavyInRows, heavyRoots, hx]

theorem cacheOff_final_le {D : Orientation n} {d : ℕ}
    (hd : D.InDegLE d) : cacheOff D d n ≤ n := by
  rw [cacheOff_final]
  exact Lax3Proofs.Refine.OrderVirtualCacheMath.heavyInSlots_le hd

/-- The target arena contains exact compact rows for all roots below `i`,
and every occupied target cell is a carrier vertex. -/
structure CacheTargetPrefix (D : Orientation n) (d i : ℕ)
    (T : ℕ → ℕ) : Prop where
  target_lt : ∀ q, q < cacheOff D d i → T q < n
  row : ∀ w : Fin n, (w : ℕ) < i →
    SetRowRep (heavyInRows D d w) (cacheLen D d w)
      (csrRowFun (cacheOff D d) T w)

theorem cacheTargetPrefix_zero (D : Orientation n) (d : ℕ)
    (T : ℕ → ℕ) : CacheTargetPrefix D d 0 T := by
  constructor
  · intro q hq
    simp at hq
  · intro w hw
    omega

/-- Appending one exact retained row extends the semantic cache prefix by
one root.  This lemma also covers a light root: its retained row has length
zero, so the functional segment update is empty. -/
theorem CacheTargetPrefix.succ {D : Orientation n} {d i : ℕ}
    (hi : i < n) {T A : ℕ → ℕ}
    (hprefix : CacheTargetPrefix D d i T)
    (hrow : SetRowRep (heavyInRows D d ⟨i, hi⟩)
      (cacheLen D d i) A) :
    CacheTargetPrefix D d (i + 1)
      (appendAt T A (cacheOff D d i) (cacheLen D d i)) := by
  let base := cacheOff D d i
  let used := cacheLen D d i
  have hoff : cacheOff D d (i + 1) = base + used := by
    simpa only [base, used] using cacheOff_succ D d i
  constructor
  · intro q hq
    rw [hoff] at hq
    by_cases hqb : q < base
    · rw [appendAt_before T A hqb]
      exact hprefix.target_lt q hqb
    · have hseg : base ≤ q ∧ q < base + used := by omega
      rw [appendAt, if_pos hseg]
      exact hrow.value_lt (q - base) (by omega)
  · intro w hw
    by_cases hwi : (w : ℕ) < i
    · have hold := hprefix.row w hwi
      apply hold.congr_prefix
      intro p hp
      unfold csrRowFun
      apply appendAt_before
      have hslot : cacheOff D d w + p < cacheOff D d ((w : ℕ) + 1) := by
        rw [cacheOff_succ]
        have hp' : p < cacheLen D d w := hp
        omega
      have hnext : cacheOff D d ((w : ℕ) + 1) ≤ base := by
        apply cacheOff_mono
        omega
      omega
    · have hwiEq : (w : ℕ) = i := by omega
      have hwEq : w = (⟨i, hi⟩ : Fin n) := Fin.ext hwiEq
      subst w
      apply hrow.congr_prefix
      intro p hp
      unfold csrRowFun
      exact appendAt_slot T A hp

/-- A complete semantic prefix is precisely the compact exact-set structure
consumed by the verified cache reader. -/
theorem setCsrRows_of_cacheTargetPrefix {D : Orientation n} {d : ℕ}
    {T : ℕ → ℕ} (hprefix : CacheTargetPrefix D d n T) :
    SetCsrRows (heavyInRows D d) (cacheOff D d n)
      (cacheOff D d) T := by
  refine ⟨?_, rfl, ?_⟩
  · refine ⟨fun i hi => cacheOff_mono D d (Nat.le_succ i),
      fun i hi => cacheOff_mono D d (by omega),
      hprefix.target_lt, ?_⟩
    intro i hi
    rw [rowLen_cacheOff]
    exact (hprefix.row ⟨i, hi⟩ hi).tail_le
  · intro w
    rw [rowLen_cacheOff]
    exact hprefix.row w w.isLt

/-! ## Axiom audit -/

#print axioms appendAt_succ_set
#print axioms cacheAppendSlot_run
#print axioms cacheAppend_run
#print axioms cacheOff_final
#print axioms CacheTargetPrefix.succ
#print axioms setCsrRows_of_cacheTargetPrefix

end Lax3Proofs.Refine.OrderVirtualCacheBuild
