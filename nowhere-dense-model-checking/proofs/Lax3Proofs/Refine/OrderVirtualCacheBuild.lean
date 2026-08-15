import Lax3Proofs.Refine.OrderVirtualCacheProvider
import Lax3Proofs.Refine.SigmaLoop

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

/-! ## Machine invariant for the outer construction pass -/

/-- The first `i` membership cells contain the canonical heavy bits. -/
def HeavyFlagPrefix (D : Orientation n) (d i : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ q, q < n → q < i →
    F q = Lax3Proofs.Refine.OrderVirtualCacheProvider.heavyBit D d q

/-- Offset cells through `i` contain the canonical prefix sums. -/
def CacheOffPrefix (D : Orientation n) (d i : ℕ) (O : ℕ → ℕ) : Prop :=
  ∀ q, q ≤ i → O q = cacheOff D d q

theorem heavyFlagPrefix_zero (D : Orientation n) (d : ℕ) (F : ℕ → ℕ) :
    HeavyFlagPrefix D d 0 F := by
  intro q hqn hq
  omega

theorem cacheOffPrefix_zero {D : Orientation n} {d : ℕ} (O : ℕ → ℕ)
    (hO : O 0 = 0) : CacheOffPrefix D d 0 O := by
  intro q hq
  have : q = 0 := by omega
  subst q
  simpa using hO

theorem HeavyFlagPrefix.succ {D : Orientation n} {d i : ℕ}
    (hi : i < n) {F : ℕ → ℕ} (h : HeavyFlagPrefix D d i F) :
    HeavyFlagPrefix D d (i + 1)
      (upd F i
        (Lax3Proofs.Refine.OrderVirtualCacheProvider.heavyBit D d i)) := by
  intro q hqn hqi
  by_cases hq : q = i
  · subst q
    simp [upd]
  · simpa [upd, hq] using h q hqn (by omega)

theorem CacheOffPrefix.succ {D : Orientation n} {d i : ℕ}
    {O : ℕ → ℕ} (h : CacheOffPrefix D d i O) :
    CacheOffPrefix D d (i + 1)
      (upd O (i + 1) (cacheOff D d (i + 1))) := by
  intro q hq
  by_cases hqi : q = i + 1
  · subst q
    simp [upd]
  · simpa [upd, hqi] using h q (by omega)

/-- Full state at one outer-loop counter.  The three cache arrays are
represented by ghost functions because construction updates them in place;
only their completed prefixes carry semantics. -/
structure CacheBuildAt (W : ℕ) (P : Env → Prop) (D : Orientation n)
    (d i : ℕ) (flag off tgt : String)
    (E Deg R ID BH BV BN : ℕ → ℕ) (sigma : Env) : Prop where
  persistent : P sigma
  engine : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
    n W E Deg R ID BH BV BN sigma
  vrow_length : (sigma.arrs "vrow").length = n
  pos : sigma.vars "w" = i
  pos_le : i ≤ n
  count : sigma.vars "cnt" = cacheOff D d i
  flag : ∃ F, sigma.arrs flag = arrOf n F ∧ HeavyFlagPrefix D d i F
  offset : ∃ O, sigma.arrs off = arrOf (n + 1) O ∧ CacheOffPrefix D d i O
  target : ∃ T, sigma.arrs tgt = arrOf n T ∧ CacheTargetPrefix D d i T

/-- Persistent states used below must survive the builder's private scalar
writes and stores to its three newly allocated cache arrays. -/
structure CacheBuildClosed (P : Env → Prop) (flag off tgt : String) : Prop where
  setVar : ∀ {sigma : Env} {a : String} {x : ℕ}, a ≠ "n" →
    P sigma → P (sigma.setVar a x)
  setArr : ∀ {sigma : Env} {a : String} {p x : ℕ},
    a = flag ∨ a = off ∨ a = tgt →
    P sigma → P (sigma.setArr a p x)

namespace CacheBuildClosed

/-- Any internal IMP command confined to the builder names preserves its
underlying persistent state. -/
theorem run {B K : ℕ} {P : Env → Prop} {flag off tgt : String}
    {c : Com} {sigma tau : Env}
    (hclose : CacheBuildClosed P flag off tgt)
    (hr : Run B c sigma tau K)
    (hvars : ∀ a ∈ c.wvars, a ≠ "n")
    (harrs : ∀ a ∈ c.warrs, a = flag ∨ a = off ∨ a = tgt)
    (hreads : ¬ c.reads) (hwrites : c.NoWrite)
    (hP : P sigma) : P tau := by
  obtain ⟨k, hk, hrun⟩ := hr
  clear hk K
  induction hrun with
  | skip => exact hP
  | assign he => exact hclose.setVar (hvars _ (by simp [Com.wvars])) hP
  | @store sigma0 a ix e index value hi he hslot =>
      exact hclose.setArr (harrs a (by simp [Com.warrs])) hP
  | @seq c0 c1 sigma0 sigma1 sigma2 k0 k1 hc hd ihc ihd =>
      have hv0 : ∀ a ∈ c0.wvars, a ≠ "n" := fun a ha =>
        hvars a (by simp [Com.wvars, ha])
      have hv1 : ∀ a ∈ c1.wvars, a ≠ "n" := fun a ha =>
        hvars a (by simp [Com.wvars, ha])
      have ha0 : ∀ a ∈ c0.warrs, a = flag ∨ a = off ∨ a = tgt :=
        fun a ha => harrs a (by simp [Com.warrs, ha])
      have ha1 : ∀ a ∈ c1.warrs, a = flag ∨ a = off ∨ a = tgt :=
        fun a ha => harrs a (by simp [Com.warrs, ha])
      have hrs : ¬ c0.reads ∧ ¬ c1.reads := by
        simpa [Com.reads] using hreads
      have hws : c0.NoWrite ∧ c1.NoWrite := by
        simpa [Com.NoWrite] using hwrites
      exact ihd hv1 ha1 hrs.2 hws.2 (ihc hv0 ha0 hrs.1 hws.1 hP)
  | @ite_true b c0 c1 sigma0 sigma1 k0 hb hc ih =>
      apply ih
      · intro a ha; exact hvars a (by simp [Com.wvars, ha])
      · intro a ha; exact harrs a (by simp [Com.warrs, ha])
      · have h : ¬ c0.reads ∧ ¬ c1.reads := by
          simpa [Com.reads] using hreads
        exact h.1
      · have h : c0.NoWrite ∧ c1.NoWrite := by
          simpa [Com.NoWrite] using hwrites
        exact h.1
      · exact hP
  | @ite_false b c0 c1 sigma0 sigma1 k0 hb hc ih =>
      apply ih
      · intro a ha; exact hvars a (by simp [Com.wvars, ha])
      · intro a ha; exact harrs a (by simp [Com.warrs, ha])
      · have h : ¬ c0.reads ∧ ¬ c1.reads := by
          simpa [Com.reads] using hreads
        exact h.2
      · have h : c0.NoWrite ∧ c1.NoWrite := by
          simpa [Com.NoWrite] using hwrites
        exact h.2
      · exact hP
  | @while_true b c0 sigma0 sigma1 sigma2 k0 k1 hb hc hw ihc ihw =>
      have hv : ∀ a ∈ c0.wvars, a ≠ "n" := fun a ha =>
        hvars a (by simpa [Com.wvars] using ha)
      have ha : ∀ a ∈ c0.warrs, a = flag ∨ a = off ∨ a = tgt :=
        fun a hx => harrs a (by simpa [Com.warrs] using hx)
      have hrs : ¬ c0.reads := by simpa [Com.reads] using hreads
      have hws : c0.NoWrite := by simpa [Com.NoWrite] using hwrites
      exact ihw hvars harrs hreads hwrites (ihc hv ha hrs hws hP)
  | while_false hb => exact hP
  | read h => exact False.elim (hreads (by simp [Com.reads]))
  | write he => exact False.elim (by simpa [Com.NoWrite] using hwrites)

end CacheBuildClosed

/-! ## Executable outer pass -/

/-- The heavy branch records the bit, regenerates the incoming row, and
appends that exact row to the compact target arena. -/
def cacheHeavyBranch (flag tgt : String) (provideIn : Com) : Com :=
  .seq (.store flag (.var "w") (.lit 1))
    (.seq provideIn (cacheAppend tgt))

/-- A light root contributes no cached row. -/
def cacheLightBranch (flag : String) : Com :=
  .store flag (.var "w") (.lit 0)

/-- Store the next CSR offset and advance the root counter. -/
def cacheBuildFinish (off : String) : Com :=
  .seq (.store off (.add (.var "w") (.lit 1)) (.var "cnt"))
    (.assign "w" (.add (.var "w") (.lit 1)))

/-- Construct the cache entry for the root in `w`.  The outgoing provider is
used only to decide whether the root is heavy; the incoming provider runs
exactly once on a heavy root. -/
def cacheBuildTurn (d : ℕ) (flag off tgt : String)
    (provideOut provideIn : Com) : Com :=
  .seq provideOut
    (.seq
      (.ite (.lt (.lit (d * d)) (.var "vtail"))
        (cacheHeavyBranch flag tgt provideIn)
        (cacheLightBranch flag))
      (cacheBuildFinish off))

/-- One carrier scan builds all heavy bits, offsets, and retained rows. -/
def cacheBuild (d : ℕ) (flag off tgt : String)
    (provideOut provideIn : Com) : Com :=
  .seq (.assign "cnt" (.lit 0))
    (.seq (.store off (.lit 0) (.lit 0))
      (.seq (.assign "w" (.lit 0))
        (.while (.lt (.var "w") (.var "n"))
          (cacheBuildTurn d flag off tgt provideOut provideIn))))

/-- Branch-sensitive charge for one construction turn. -/
noncomputable def cacheBuildTurnCost (D : Orientation n) (d : ℕ)
    (kout kin : ℕ → ℕ) (i : ℕ) : ℕ :=
  if hi : i < n then
    kout i +
      if (⟨i, hi⟩ : Fin n) ∈ heavyRoots D d
      then kin i + 18 * (D.inN (⟨i, hi⟩ : Fin n)).card + 22
      else 16
  else 0

theorem setRowRep_empty (A : ℕ → ℕ) :
    SetRowRep (∅ : Finset (Fin n)) 0 A := by
  refine ⟨by simp, by simp, by simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList], ?_⟩
  intro u
  simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]

theorem cacheLen_of_heavy {D : Orientation n} {d : ℕ} {w : Fin n}
    (hw : w ∈ heavyRoots D d) :
    cacheLen D d w = (D.inN w).card := by
  rw [cacheLen_fin]
  simp [heavyInRows, hw]

theorem cacheLen_of_light {D : Orientation n} {d : ℕ} {w : Fin n}
    (hw : w ∉ heavyRoots D d) : cacheLen D d w = 0 := by
  rw [cacheLen_fin]
  simp [heavyInRows, hw]

theorem cacheOff_succ_le_final {D : Orientation n} {d i : ℕ}
    (hi : i < n) : cacheOff D d (i + 1) ≤ cacheOff D d n :=
  cacheOff_mono D d (by omega)

/-- State after the heavy/light branch and before the common offset/counter
suffix. -/
structure CacheBuildBeforeFinish (W : ℕ) (P : Env → Prop)
    (D : Orientation n) (d i : ℕ) (flag off tgt : String)
    (E Deg R ID BH BV BN : ℕ → ℕ) (sigma : Env) : Prop where
  persistent : P sigma
  engine : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
    n W E Deg R ID BH BV BN sigma
  vrow_length : (sigma.arrs "vrow").length = n
  pos : sigma.vars "w" = i
  count : sigma.vars "cnt" = cacheOff D d (i + 1)
  flag : ∃ F, sigma.arrs flag = arrOf n F ∧ HeavyFlagPrefix D d (i + 1) F
  offset : ∃ O, sigma.arrs off = arrOf (n + 1) O ∧ CacheOffPrefix D d i O
  target : ∃ T, sigma.arrs tgt = arrOf n T ∧ CacheTargetPrefix D d (i + 1) T

/-- Allocation and persistent state required before the cache construction
pass starts. -/
structure CacheBuildStart (W : ℕ) (P : Env → Prop)
    (n : ℕ) (flag off tgt : String)
    (E Deg R ID BH BV BN : ℕ → ℕ) (sigma : Env) : Prop where
  persistent : P sigma
  engine : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
    n W E Deg R ID BH BV BN sigma
  vrow_length : (sigma.arrs "vrow").length = n
  flag_length : (sigma.arrs flag).length = n
  offset_length : (sigma.arrs off).length = n + 1
  target_length : (sigma.arrs tgt).length = n

/-- Counter-indexed invariant in the form consumed by the summed loop rule. -/
def CacheBuildInv (W : ℕ) (P : Env → Prop) (D : Orientation n)
    (d : ℕ) (flag off tgt : String)
    (E Deg R ID BH BV BN : ℕ → ℕ) (sigma : Env) : Prop :=
  CacheBuildAt W P D d (sigma.vars "w") flag off tgt
    E Deg R ID BH BV BN sigma

/-- The common suffix commits the next offset and advances `w`. -/
theorem cacheBuildFinish_run {B n W i d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String}
    {E Deg R ID BH BV BN F O T : ℕ → ℕ} {sigma : Env}
    (hi : i < n) (hnB : n < B)
    (hcountB : cacheOff D d (i + 1) < B)
    (hclose : CacheBuildClosed P flag off tgt)
    (hoffEngine : off ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (hoffFlag : off ≠ flag) (hoffTgt : off ≠ tgt)
    (hP : P sigma)
    (heng : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN sigma)
    (hvrow : (sigma.arrs "vrow").length = n)
    (hw : sigma.vars "w" = i)
    (hcnt : sigma.vars "cnt" = cacheOff D d (i + 1))
    (hflag : sigma.arrs flag = arrOf n F)
    (hflagPrefix : HeavyFlagPrefix D d (i + 1) F)
    (hoff : sigma.arrs off = arrOf (n + 1) O)
    (hoffPrefix : CacheOffPrefix D d i O)
    (htgt : sigma.arrs tgt = arrOf n T)
    (htgtPrefix : CacheTargetPrefix D d (i + 1) T) :
    ∃ tau,
      Run B (cacheBuildFinish off) sigma tau 9 ∧
      CacheBuildAt W P D d (i + 1) flag off tgt
        E Deg R ID BH BV BN tau := by
  have hiB : i < B := by omega
  have hi1B : i + 1 < B := by omega
  have ew : (Expr.var "w").evalB B sigma = some i := by
    have h := evalB_var (B := B) (x := "w") (σ := sigma) (by rw [hw]; exact hiB)
    rwa [hw] at h
  have eone : (Expr.lit 1).evalB B sigma = some 1 := evalB_lit (by omega)
  have eidx : (Expr.add (.var "w") (.lit 1)).evalB B sigma =
      some (i + 1) := by
    simpa [Lax13Proofs.Imp.Bop.apply] using
      (evalB_bin (op := .add) ew eone (by
        simp [Lax13Proofs.Imp.Bop.apply]
        exact hi1B))
  have ecnt : (Expr.var "cnt").evalB B sigma =
      some (cacheOff D d (i + 1)) := by
    have h := evalB_var (B := B) (x := "cnt") (σ := sigma) (by
      rw [hcnt]
      exact hcountB)
    rwa [hcnt] at h
  have hslot : i + 1 < (sigma.arrs off).length := by
    rw [hoff, length_arrOf]
    omega
  let sigma1 := sigma.setArr off (i + 1) (cacheOff D d (i + 1))
  have rstore : Run B
      (.store off (.add (.var "w") (.lit 1)) (.var "cnt"))
      sigma sigma1 5 := by
    simpa only [sigma1] using Run.store eidx ecnt hslot
  have hw1 : sigma1.vars "w" = i := by simpa [sigma1] using hw
  have ew1 : (Expr.var "w").evalB B sigma1 = some i := by
    have h := evalB_var (B := B) (x := "w") (σ := sigma1) (by rw [hw1]; exact hiB)
    rwa [hw1] at h
  have eone1 : (Expr.lit 1).evalB B sigma1 = some 1 := evalB_lit (by omega)
  have einc : (Expr.add (.var "w") (.lit 1)).evalB B sigma1 =
      some (i + 1) := by
    simpa [Lax13Proofs.Imp.Bop.apply] using
      (evalB_bin (op := .add) ew1 eone1 (by
        simp [Lax13Proofs.Imp.Bop.apply]
        exact hi1B))
  let tau := sigma1.setVar "w" (i + 1)
  have rinc : Run B (.assign "w" (.add (.var "w") (.lit 1)))
      sigma1 tau 4 := by
    simpa only [tau] using Run.assign einc
  have hP1 : P sigma1 :=
    hclose.setArr (a := off) (Or.inr (Or.inl rfl)) hP
  have hPtau : P tau := hclose.setVar (a := "w") (by decide) hP1
  have heng1 : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN sigma1 :=
    heng.setArr_of_private
      (by intro h; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (i + 1) (cacheOff D d (i + 1))
  have hengtau : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN tau :=
    heng1.setVar "w" (i + 1) (by decide)
  have hoff1 : sigma1.arrs off =
      arrOf (n + 1) (upd O (i + 1) (cacheOff D d (i + 1))) := by
    simpa [sigma1, hoff] using
      (set_arrOf_eq_upd (n := n + 1) O (i + 1)
        (cacheOff D d (i + 1)))
  refine ⟨tau, by simpa only [cacheBuildFinish] using rstore.seq rinc,
    hPtau, hengtau, ?_, by simp [tau], by omega, ?_, ?_, ?_, ?_⟩
  · simpa only [tau, arrs_setVar, sigma1, length_arrs_setArr] using hvrow
  · simpa [tau, sigma1] using hcnt
  · refine ⟨F, ?_, hflagPrefix⟩
    simp only [tau, arrs_setVar, sigma1, arrs_setArr, if_neg (Ne.symm hoffFlag)]
    exact hflag
  · refine ⟨upd O (i + 1) (cacheOff D d (i + 1)), ?_,
      hoffPrefix.succ⟩
    simpa [tau] using hoff1
  · refine ⟨T, ?_, htgtPrefix⟩
    simp only [tau, arrs_setVar, sigma1, arrs_setArr, if_neg (Ne.symm hoffTgt)]
    exact htgt

theorem cacheBuildFinish_of_before {B n W i d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String}
    {E Deg R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (hi : i < n) (hd : D.InDegLE d) (hnB : n < B)
    (hclose : CacheBuildClosed P flag off tgt)
    (hoffEngine : off ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (hoffFlag : off ≠ flag) (hoffTgt : off ≠ tgt)
    (h : CacheBuildBeforeFinish W P D d i flag off tgt
      E Deg R ID BH BV BN sigma) :
    ∃ tau,
      Run B (cacheBuildFinish off) sigma tau 9 ∧
      CacheBuildAt W P D d (i + 1) flag off tgt
        E Deg R ID BH BV BN tau := by
  obtain ⟨F, hflag, hflagPrefix⟩ := h.flag
  obtain ⟨O, hoff, hoffPrefix⟩ := h.offset
  obtain ⟨T, htgt, htgtPrefix⟩ := h.target
  apply cacheBuildFinish_run hi hnB
    (lt_of_le_of_lt
      ((cacheOff_succ_le_final (D := D) (d := d) hi).trans
        (cacheOff_final_le hd)) hnB)
    hclose hoffEngine hoffFlag hoffTgt h.persistent h.engine
    h.vrow_length h.pos h.count
    hflag hflagPrefix hoff hoffPrefix htgt htgtPrefix

/-- The light branch writes a zero bit and extends the semantic target by an
empty row, without invoking the incoming provider. -/
theorem cacheLightBranch_run {B n W i d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String}
    {E Deg R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (hi : i < n) (hB1 : 1 < B) (hnB : n < B)
    (hclose : CacheBuildClosed P flag off tgt)
    (hflagEngine : flag ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (hflagOff : flag ≠ off) (hflagTgt : flag ≠ tgt)
    (hlight : (⟨i, hi⟩ : Fin n) ∉ heavyRoots D d)
    (h : CacheBuildAt W P D d i flag off tgt
      E Deg R ID BH BV BN sigma) :
    ∃ tau,
      Run B (cacheLightBranch flag) sigma tau 3 ∧
      CacheBuildBeforeFinish W P D d i flag off tgt
        E Deg R ID BH BV BN tau := by
  obtain ⟨F, hflag, hflagPrefix⟩ := h.flag
  obtain ⟨O, hoff, hoffPrefix⟩ := h.offset
  obtain ⟨T, htgt, htgtPrefix⟩ := h.target
  have hiB : i < B := lt_trans hi hnB
  have ew : (Expr.var "w").evalB B sigma = some i := by
    have he := evalB_var (B := B) (x := "w") (σ := sigma) (by
      rw [h.pos]
      exact hiB)
    rwa [h.pos] at he
  have ezero : (Expr.lit 0).evalB B sigma = some 0 := evalB_lit (by omega)
  have hslot : i < (sigma.arrs flag).length := by
    rw [hflag, length_arrOf]
    exact hi
  let tau := sigma.setArr flag i 0
  have hr : Run B (cacheLightBranch flag) sigma tau 3 := by
    simpa only [cacheLightBranch, tau] using Run.store ew ezero hslot
  have hPtau : P tau := hclose.setArr (a := flag) (Or.inl rfl) h.persistent
  have hengtau : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN tau :=
    h.engine.setArr_of_private
      (by intro h; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro h; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      i 0
  have hbit : Lax3Proofs.Refine.OrderVirtualCacheProvider.heavyBit D d i = 0 := by
    simpa using
      (Lax3Proofs.Refine.OrderVirtualCacheProvider.heavyBit_of_notMem hlight)
  have hlen : cacheLen D d i = 0 := by
    simpa using cacheLen_of_light hlight
  have hcntNext : tau.vars "cnt" = cacheOff D d (i + 1) := by
    simp only [tau, vars_setArr]
    rw [cacheOff_succ, hlen, Nat.add_zero]
    exact h.count
  have htargetNext : CacheTargetPrefix D d (i + 1) T := by
    have hrow : SetRowRep (heavyInRows D d (⟨i, hi⟩ : Fin n))
        (cacheLen D d i) (fun _ => 0) := by
      simpa [heavyInRows, hlight, hlen] using
        (setRowRep_empty (n := n) (fun _ => 0))
    have hnext := htgtPrefix.succ hi hrow
    have heq : appendAt T (fun _ => 0) (cacheOff D d i) 0 = T := by
      funext q
      exact appendAt_zero T (fun _ => 0) (cacheOff D d i) q
    simpa only [hlen, heq] using hnext
  refine ⟨tau, hr, hPtau, hengtau, ?_, by simpa [tau] using h.pos,
    hcntNext, ?_, ?_, ?_⟩
  · simpa only [tau, length_arrs_setArr] using h.vrow_length
  · refine ⟨upd F i 0, ?_, ?_⟩
    · simpa [tau, hflag] using
        (set_arrOf_eq_upd (n := n) F i 0)
    · simpa [hbit] using hflagPrefix.succ hi
  · refine ⟨O, ?_, hoffPrefix⟩
    simp only [tau, arrs_setArr, if_neg (Ne.symm hflagOff)]
    exact hoff
  · refine ⟨T, ?_, htargetNext⟩
    simp only [tau, arrs_setArr, if_neg (Ne.symm hflagTgt)]
    exact htgt

/-- The heavy branch calls the incoming provider once and appends exactly its
row.  Its charge is the provider charge plus the compact-copy charge. -/
theorem cacheHeavyBranch_run {B n W i d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String}
    {E Deg R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    {provideIn : Com} {kin : ℕ → ℕ}
    (hi : i < n) (hd : D.InDegLE d) (hB1 : 1 < B) (hnB : n < B)
    (hclose : CacheBuildClosed P flag off tgt)
    (hflagEngine : flag ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (htgtEngine : tgt ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (hflagOff : flag ≠ off) (hflagTgt : flag ≠ tgt)
    (hoffTgt : off ≠ tgt) (htgtVrow : tgt ≠ "vrow")
    (hprovideFlag : flag ∉ provideIn.warrs)
    (hprovideOff : off ∉ provideIn.warrs)
    (hprovideTgt : tgt ∉ provideIn.warrs)
    (hpin : Lax3Proofs.Refine.OrderVirtualSetRow.ProvidesSetRows
      B n W (fun w => D.inN w) P "vrow" provideIn kin)
    (hheavy : (⟨i, hi⟩ : Fin n) ∈ heavyRoots D d)
    (h : CacheBuildAt W P D d i flag off tgt
      E Deg R ID BH BV BN sigma) :
    ∃ tau K,
      Run B (cacheHeavyBranch flag tgt provideIn) sigma tau K ∧
      K ≤ kin i + 18 * (D.inN (⟨i, hi⟩ : Fin n)).card + 9 ∧
      CacheBuildBeforeFinish W P D d i flag off tgt
        E Deg R ID BH BV BN tau := by
  obtain ⟨F, hflag, hflagPrefix⟩ := h.flag
  obtain ⟨O, hoff, hoffPrefix⟩ := h.offset
  obtain ⟨T, htgt, htgtPrefix⟩ := h.target
  have hiB : i < B := lt_trans hi hnB
  have ew : (Expr.var "w").evalB B sigma = some i := by
    have he := evalB_var (B := B) (x := "w") (σ := sigma) (by
      rw [h.pos]
      exact hiB)
    rwa [h.pos] at he
  have eone : (Expr.lit 1).evalB B sigma = some 1 := evalB_lit hB1
  have hslot : i < (sigma.arrs flag).length := by
    rw [hflag, length_arrOf]
    exact hi
  let sigma1 := sigma.setArr flag i 1
  have rflag : Run B (.store flag (.var "w") (.lit 1)) sigma sigma1 3 := by
    simpa only [sigma1] using Run.store ew eone hslot
  have hP1 : P sigma1 := hclose.setArr (a := flag) (Or.inl rfl) h.persistent
  have heng1 : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN sigma1 :=
    h.engine.setArr_of_private
      (by intro hx; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst flag; exact hflagEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      i 1
  have hw1 : sigma1.vars "w" = i := by simpa [sigma1] using h.pos
  obtain ⟨sigma2, rin, hP2, heng2, hstable, tail, A,
      hrow, htail, hsrc⟩ :=
    (hpin (⟨i, hi⟩ : Fin n) E Deg R ID BH BV BN).run
      ⟨hP1, heng1, hw1⟩
  have hflag1 : sigma1.arrs flag = arrOf n (upd F i 1) := by
    simpa [sigma1, hflag] using (set_arrOf_eq_upd (n := n) F i 1)
  have hflag2 : sigma2.arrs flag = arrOf n (upd F i 1) := by
    rw [rin.frame_arr flag hprovideFlag]
    exact hflag1
  have hoff2 : sigma2.arrs off = arrOf (n + 1) O := by
    rw [rin.frame_arr off hprovideOff]
    simp only [sigma1, arrs_setArr, if_neg (Ne.symm hflagOff)]
    exact hoff
  have htgt2 : sigma2.arrs tgt = arrOf n T := by
    rw [rin.frame_arr tgt hprovideTgt]
    simp only [sigma1, arrs_setArr, if_neg (Ne.symm hflagTgt)]
    exact htgt
  have hw2 : sigma2.vars "w" = i := by
    rw [hstable.w_eq]
    exact hw1
  have hcnt2 : sigma2.vars "cnt" = cacheOff D d i := by
    rw [hstable.cnt_eq]
    simpa [sigma1] using h.count
  have hused : tail = cacheLen D d i := by
    rw [cacheLen_of_heavy hheavy]
    exact hrow.tail_eq
  have hfit : cacheOff D d i + tail ≤ n := by
    rw [hused, ← cacheOff_succ]
    exact (cacheOff_succ_le_final (D := D) (d := d) hi).trans
      (cacheOff_final_le hd)
  have hbaseTailB : cacheOff D d i + tail < B := lt_of_le_of_lt hfit hnB
  obtain ⟨sigma3, Kapp, rapp, hKapp, hsrc3, htgt3, hcnt3, htail3⟩ :=
    cacheAppend_run (B := B) (n := n) (nt := n)
      (base := cacheOff D d i) (tail := tail) (tgt := tgt)
      (A := A) (T := T) (sigma := sigma2)
      htgtVrow hB1 hbaseTailB hfit hrow.tail_le
      (fun p hp => lt_trans (hrow.value_lt p hp) hnB)
      hsrc htgt2 hcnt2 htail
  have hP3 : P sigma3 := hclose.run rapp
    (by
      intro a ha
      simp [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
        Lax3Proofs.RamDriverAugment.scanBody, Com.wvars] at ha
      rcases ha with rfl | rfl | rfl | rfl
      all_goals decide)
    (by
      intro a ha
      simp [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
        Lax3Proofs.RamDriverAugment.scanBody, Com.warrs] at ha
      exact Or.inr (Or.inr ha))
    (by simp [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
      Lax3Proofs.RamDriverAugment.scanBody, Com.reads])
    (by simp [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
      Lax3Proofs.RamDriverAugment.scanBody, Com.NoWrite]) hP2
  have hframeN : sigma3.vars "n" = sigma2.vars "n" :=
    rapp.frame_var "n" (by
      simp [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
        Lax3Proofs.RamDriverAugment.scanBody, Com.wvars])
  have hframeEngine : ∀ a,
      a ∈ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames →
      sigma3.arrs a = sigma2.arrs a := by
    intro a ha
    apply rapp.frame_arr a
    intro haw
    have hat : a = tgt := by
      simpa [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
        Lax3Proofs.RamDriverAugment.scanBody, Com.warrs] using haw
    subst a
    exact htgtEngine ha
  have heng3 : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN sigma3 :=
    ⟨hframeN.trans heng2.n_eq,
      by rw [hframeEngine "elm" (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames])]; exact heng2.elm_eq,
      by rw [hframeEngine "deg" (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames])]; exact heng2.deg_eq,
      by rw [hframeEngine "rnk" (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames])]; exact heng2.rank_eq,
      by rw [hframeEngine "idg" (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames])]; exact heng2.idg_eq,
      by rw [hframeEngine "bh" (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames])]; exact heng2.head_eq,
      by rw [hframeEngine "bv" (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames])]; exact heng2.val_eq,
      by rw [hframeEngine "bn" (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames])]; exact heng2.next_eq⟩
  have hw3 : sigma3.vars "w" = i := by
    rw [rapp.frame_var "w" (by
      simp [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
        Lax3Proofs.RamDriverAugment.scanBody, Com.wvars])]
    exact hw2
  have hflag3 : sigma3.arrs flag = arrOf n (upd F i 1) := by
    rw [rapp.frame_arr flag (by
      intro haw
      have : flag = tgt := by
        simpa [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
          Lax3Proofs.RamDriverAugment.scanBody, Com.warrs] using haw
      exact hflagTgt this)]
    exact hflag2
  have hoff3 : sigma3.arrs off = arrOf (n + 1) O := by
    rw [rapp.frame_arr off (by
      intro haw
      have : off = tgt := by
        simpa [cacheAppend, cacheAppendSlot, bufferScan, Csr.scan,
          Lax3Proofs.RamDriverAugment.scanBody, Com.warrs] using haw
      exact hoffTgt this)]
    exact hoff2
  have htargetPrefix : CacheTargetPrefix D d (i + 1)
      (appendAt T A (cacheOff D d i) tail) := by
    have hrow' : SetRowRep (heavyInRows D d (⟨i, hi⟩ : Fin n))
        (cacheLen D d i) A := by
      simpa [heavyInRows, hheavy, hused] using hrow
    have hnext := htgtPrefix.succ hi hrow'
    simpa [hused] using hnext
  let K := 3 + (kin i + Kapp)
  have hr : Run B (cacheHeavyBranch flag tgt provideIn) sigma sigma3 K := by
    simpa only [cacheHeavyBranch, K] using rflag.seq (rin.seq rapp)
  refine ⟨sigma3, K, hr, ?_, hP3, heng3, ?_, hw3, ?_, ?_, ?_, ?_⟩
  · have htailCard : tail = (D.inN (⟨i, hi⟩ : Fin n)).card := by
      simpa using hrow.tail_eq
    dsimp [K]
    rw [htailCard] at hKapp
    omega
  · rw [Lax3Proofs.RamDriver.run_length_arrs rapp "vrow",
      hsrc, length_arrOf]
  · calc
      sigma3.vars "cnt" = cacheOff D d i + tail := hcnt3
      _ = cacheOff D d i + cacheLen D d i := by rw [hused]
      _ = cacheOff D d (i + 1) := (cacheOff_succ D d i).symm
  · refine ⟨upd F i 1, hflag3, ?_⟩
    have hbit :=
      Lax3Proofs.Refine.OrderVirtualCacheProvider.heavyBit_of_mem hheavy
    simpa [hbit] using hflagPrefix.succ hi
  · exact ⟨O, hoff3, hoffPrefix⟩
  · exact ⟨appendAt T A (cacheOff D d i) tail, htgt3, htargetPrefix⟩

/-- One complete construction turn selects the heavy/light branch from the
exact outgoing-row cardinality and extends the canonical cache prefix. -/
theorem cacheBuildTurn_spec {B n W i d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String}
    {E Deg R ID BH BV BN : ℕ → ℕ}
    {provideOut provideIn : Com} {kout kin : ℕ → ℕ}
    (hi : i < n) (hd : D.InDegLE d)
    (hB1 : 1 < B) (hnB : n < B) (hddB : d * d < B)
    (hclose : CacheBuildClosed P flag off tgt)
    (hflagEngine : flag ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (hoffEngine : off ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (htgtEngine : tgt ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (hflagOff : flag ≠ off) (hflagTgt : flag ≠ tgt)
    (hoffTgt : off ≠ tgt) (htgtVrow : tgt ≠ "vrow")
    (houtFlag : flag ∉ provideOut.warrs)
    (houtOff : off ∉ provideOut.warrs)
    (houtTgt : tgt ∉ provideOut.warrs)
    (hinFlag : flag ∉ provideIn.warrs)
    (hinOff : off ∉ provideIn.warrs)
    (hinTgt : tgt ∉ provideIn.warrs)
    (hpout : Lax3Proofs.Refine.OrderVirtualSetRow.ProvidesSetRows
      B n W (fun w => Lax3Proofs.RamAugment.outSet D w)
        P "vrow" provideOut kout)
    (hpin : Lax3Proofs.Refine.OrderVirtualSetRow.ProvidesSetRows
      B n W (fun w => D.inN w) P "vrow" provideIn kin) :
    Spec B
      (CacheBuildAt W P D d i flag off tgt E Deg R ID BH BV BN)
      (cacheBuildTurn d flag off tgt provideOut provideIn)
      (fun _ tau => CacheBuildAt W P D d (i + 1) flag off tgt
        E Deg R ID BH BV BN tau)
      (cacheBuildTurnCost D d kout kin i) := by
  classical
  refine Spec.of_exists fun sigma hstate => ?_
  obtain ⟨sigmaOut, rout, hPout, hengOut, hstableOut,
      outTail, Aout, hrowOut, htailOut, hAout⟩ :=
    (hpout (⟨i, hi⟩ : Fin n) E Deg R ID BH BV BN).run
      ⟨hstate.persistent, hstate.engine, hstate.pos⟩
  obtain ⟨F, hflag, hflagPrefix⟩ := hstate.flag
  obtain ⟨O, hoff, hoffPrefix⟩ := hstate.offset
  obtain ⟨T, htgt, htgtPrefix⟩ := hstate.target
  have hflagOut : sigmaOut.arrs flag = arrOf n F := by
    rw [rout.frame_arr flag houtFlag]
    exact hflag
  have hoffOut : sigmaOut.arrs off = arrOf (n + 1) O := by
    rw [rout.frame_arr off houtOff]
    exact hoff
  have htgtOut : sigmaOut.arrs tgt = arrOf n T := by
    rw [rout.frame_arr tgt houtTgt]
    exact htgt
  have hstateOut : CacheBuildAt W P D d i flag off tgt
      E Deg R ID BH BV BN sigmaOut := by
    refine ⟨hPout, hengOut, ?_, ?_, hstate.pos_le, ?_,
      ⟨F, hflagOut, hflagPrefix⟩, ⟨O, hoffOut, hoffPrefix⟩,
      ⟨T, htgtOut, htgtPrefix⟩⟩
    · rw [hAout, length_arrOf]
    · rw [hstableOut.w_eq]
      exact hstate.pos
    · rw [hstableOut.cnt_eq]
      exact hstate.count
  have houtTailB : outTail < B := lt_of_le_of_lt hrowOut.tail_le hnB
  have edd : (Expr.lit (d * d)).evalB B sigmaOut = some (d * d) :=
    evalB_lit hddB
  have etail : (Expr.var "vtail").evalB B sigmaOut = some outTail := by
    have he := evalB_var (B := B) (x := "vtail") (σ := sigmaOut) (by
      rw [htailOut]
      exact houtTailB)
    rwa [htailOut] at he
  have econd := evalB_condLt edd etail
  by_cases hheavy : (⟨i, hi⟩ : Fin n) ∈ heavyRoots D d
  · have hlt : d * d < outTail := by
      rw [hrowOut.tail_eq]
      exact Lax3Proofs.Refine.OrderVirtualCacheMath.mem_heavyRoots.1 hheavy
    have etrue :
        (Cond.lt (.lit (d * d)) (.var "vtail")).evalB B sigmaOut =
          some true := by
      simpa [hlt] using econd
    obtain ⟨sigmaBranch, Kbranch, rbranch, hKbranch, hbefore⟩ :=
      cacheHeavyBranch_run hi hd hB1 hnB hclose hflagEngine htgtEngine
        hflagOff hflagTgt hoffTgt htgtVrow hinFlag hinOff hinTgt
        hpin hheavy hstateOut
    obtain ⟨tau, rfinish, hfinal⟩ :=
      cacheBuildFinish_of_before hi hd hnB hclose hoffEngine
        (Ne.symm hflagOff) hoffTgt hbefore
    have rbranchIf : Run B
        (.ite (.lt (.lit (d * d)) (.var "vtail"))
          (cacheHeavyBranch flag tgt provideIn) (cacheLightBranch flag))
        sigmaOut sigmaBranch (Kbranch + 4) := by
      have hr := Run.ite_true
        (d := cacheLightBranch flag) etrue rbranch
      simpa [Cond.size, Expr.size, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hr
    have rturn : Run B
        (cacheBuildTurn d flag off tgt provideOut provideIn)
        sigma tau (kout i + (Kbranch + 4 + 9)) := by
      simpa only [cacheBuildTurn, Nat.add_assoc] using
        rout.seq (rbranchIf.seq rfinish)
    refine ⟨tau, kout i + (Kbranch + 4 + 9), rturn, ?_, hfinal⟩
    rw [cacheBuildTurnCost, dif_pos hi, if_pos hheavy]
    omega
  · have hle : outTail ≤ d * d := by
      rw [hrowOut.tail_eq]
      exact Lax3Proofs.Refine.OrderVirtualCacheMath.out_card_le_sq_of_not_heavy
        hheavy
    have efalse :
        (Cond.lt (.lit (d * d)) (.var "vtail")).evalB B sigmaOut =
          some false := by
      have hnlt : ¬ d * d < outTail := by omega
      simpa [hnlt] using econd
    obtain ⟨sigmaBranch, rbranch, hbefore⟩ :=
      cacheLightBranch_run hi hB1 hnB hclose hflagEngine
        hflagOff hflagTgt hheavy hstateOut
    obtain ⟨tau, rfinish, hfinal⟩ :=
      cacheBuildFinish_of_before hi hd hnB hclose hoffEngine
        (Ne.symm hflagOff) hoffTgt hbefore
    have rbranchIf : Run B
        (.ite (.lt (.lit (d * d)) (.var "vtail"))
          (cacheHeavyBranch flag tgt provideIn) (cacheLightBranch flag))
        sigmaOut sigmaBranch 7 := by
      have hr := Run.ite_false
        (c := cacheHeavyBranch flag tgt provideIn) efalse rbranch
      simpa [Cond.size, Expr.size] using hr
    have rturn : Run B
        (cacheBuildTurn d flag off tgt provideOut provideIn)
        sigma tau (kout i + (7 + 9)) := by
      simpa only [cacheBuildTurn, Nat.add_assoc] using
        rout.seq (rbranchIf.seq rfinish)
    refine ⟨tau, kout i + (7 + 9), rturn, ?_, hfinal⟩
    rw [cacheBuildTurnCost, dif_pos hi, if_neg hheavy]

/-- The complete carrier scan constructs every cache row with a summed,
branch-sensitive charge. -/
theorem cacheBuild_spec {B n W d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String}
    {E Deg R ID BH BV BN : ℕ → ℕ}
    {provideOut provideIn : Com} {kout kin : ℕ → ℕ}
    (hd : D.InDegLE d)
    (hB1 : 1 < B) (hnB : n < B) (hddB : d * d < B)
    (hclose : CacheBuildClosed P flag off tgt)
    (hflagEngine : flag ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (hoffEngine : off ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (htgtEngine : tgt ∉ Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames)
    (hflagOff : flag ≠ off) (hflagTgt : flag ≠ tgt)
    (hoffTgt : off ≠ tgt) (htgtVrow : tgt ≠ "vrow")
    (houtFlag : flag ∉ provideOut.warrs)
    (houtOff : off ∉ provideOut.warrs)
    (houtTgt : tgt ∉ provideOut.warrs)
    (hinFlag : flag ∉ provideIn.warrs)
    (hinOff : off ∉ provideIn.warrs)
    (hinTgt : tgt ∉ provideIn.warrs)
    (hpout : Lax3Proofs.Refine.OrderVirtualSetRow.ProvidesSetRows
      B n W (fun w => Lax3Proofs.RamAugment.outSet D w)
        P "vrow" provideOut kout)
    (hpin : Lax3Proofs.Refine.OrderVirtualSetRow.ProvidesSetRows
      B n W (fun w => D.inN w) P "vrow" provideIn kin) :
    Spec B
      (CacheBuildStart W P n flag off tgt E Deg R ID BH BV BN)
      (cacheBuild d flag off tgt provideOut provideIn)
      (fun _ tau => CacheBuildAt W P D d n flag off tgt
        E Deg R ID BH BV BN tau)
      ((∑ k ∈ Finset.range n,
          (cacheBuildTurnCost D d kout kin k + 4)) + 11) := by
  let I : Env → Prop := CacheBuildInv W P D d flag off tgt
    E Deg R ID BH BV BN
  have hloop := Lax3Proofs.Refine.SigmaLoop.forRangeZeroSum
    (c := cacheBuildTurn d flag off tgt provideOut provideIn)
    "w" "n" I n (cacheBuildTurnCost D d kout kin) hnB
    (fun _ hI => hI.pos_le)
    (fun _ hI => hI.engine.n_eq)
    (by
      intro k hk
      refine Spec.of_exists fun rho hrho => ?_
      obtain ⟨hI, hw⟩ := hrho
      have hkState : CacheBuildAt W P D d k flag off tgt
          E Deg R ID BH BV BN rho := by
        simpa only [I, CacheBuildInv, hw] using hI
      obtain ⟨tau, hr, hnext⟩ :=
        (cacheBuildTurn_spec hk hd hB1 hnB hddB hclose
          hflagEngine hoffEngine htgtEngine hflagOff hflagTgt
          hoffTgt htgtVrow houtFlag houtOff houtTgt
          hinFlag hinOff hinTgt hpout hpin).run hkState
      have hInvNext : I tau := by
        simpa only [I, CacheBuildInv, hnext.pos] using hnext
      exact ⟨tau, cacheBuildTurnCost D d kout kin k, hr, le_rfl,
        hInvNext, hnext.pos⟩)
  intro sigma hstart
  have ezero : (Expr.lit 0).evalB B sigma = some 0 := evalB_lit (by omega)
  let sigma1 := sigma.setVar "cnt" 0
  have rcount : Run B (.assign "cnt" (.lit 0)) sigma sigma1 2 := by
    simpa only [sigma1] using Run.assign ezero
  have ezeroIx : (Expr.lit 0).evalB B sigma1 = some 0 := evalB_lit (by omega)
  have ezeroVal : (Expr.lit 0).evalB B sigma1 = some 0 := evalB_lit (by omega)
  have hoffSlot : 0 < (sigma1.arrs off).length := by
    simpa [sigma1, hstart.offset_length]
  let sigma2 := sigma1.setArr off 0 0
  have roff : Run B (.store off (.lit 0) (.lit 0)) sigma1 sigma2 3 := by
    simpa only [sigma2] using Run.store ezeroIx ezeroVal hoffSlot
  let sigma3 := sigma2.setVar "w" 0
  have hP1 : P sigma1 := hclose.setVar (a := "cnt") (by decide)
    hstart.persistent
  have hP2 : P sigma2 := hclose.setArr (a := off)
    (Or.inr (Or.inl rfl)) hP1
  have hP3 : P sigma3 := hclose.setVar (a := "w") (by decide) hP2
  have heng1 : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN sigma1 :=
    hstart.engine.setVar "cnt" 0 (by decide)
  have heng2 : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN sigma2 :=
    heng1.setArr_of_private
      (by intro hx; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      (by intro hx; subst off; exact hoffEngine (by simp [Lax3Proofs.Refine.OrderVirtualProvider.engineArrNames]))
      0 0
  have heng3 : Lax3Proofs.Refine.OrderVirtualProvider.EngineArrays
      n W E Deg R ID BH BV BN sigma3 :=
    heng2.setVar "w" 0 (by decide)
  obtain ⟨F, hF⟩ :=
    Lax3Proofs.RamDriver.exists_arrOf hstart.flag_length
  obtain ⟨O, hO⟩ :=
    Lax3Proofs.RamDriver.exists_arrOf hstart.offset_length
  obtain ⟨T, hT⟩ :=
    Lax3Proofs.RamDriver.exists_arrOf hstart.target_length
  have hflag3 : sigma3.arrs flag = arrOf n F := by
    simp only [sigma3, arrs_setVar, sigma2, arrs_setArr,
      if_neg hflagOff, sigma1, arrs_setVar]
    exact hF
  have hoff2 : sigma2.arrs off = arrOf (n + 1) (upd O 0 0) := by
    simpa [sigma2, sigma1, hO] using
      (set_arrOf_eq_upd (n := n + 1) O 0 0)
  have htgt3 : sigma3.arrs tgt = arrOf n T := by
    simp only [sigma3, arrs_setVar, sigma2, arrs_setArr,
      if_neg (Ne.symm hoffTgt), sigma1, arrs_setVar]
    exact hT
  have hI0 : I sigma3 := by
    refine ⟨hP3, heng3, ?_, rfl, by simp [sigma3], ?_,
      ⟨F, hflag3, heavyFlagPrefix_zero D d F⟩,
      ⟨upd O 0 0, by simpa [sigma3] using hoff2, ?_⟩,
      ⟨T, htgt3, cacheTargetPrefix_zero D d T⟩⟩
    · simpa only [sigma3, arrs_setVar, sigma2, length_arrs_setArr,
        sigma1, arrs_setVar] using hstart.vrow_length
    · simp [sigma3, sigma2, sigma1, cacheOff_zero]
    · exact cacheOffPrefix_zero (D := D) (d := d) (upd O 0 0)
        (by simp [upd, cacheOff_zero])
  obtain ⟨tau, rloop, hInvFinal, hwFinal⟩ := hloop.run hI0
  have hfinal : CacheBuildAt W P D d n flag off tgt
      E Deg R ID BH BV BN tau := by
    simpa only [I, CacheBuildInv, hwFinal] using hInvFinal
  refine ⟨tau, ?_, hfinal⟩
  have hr : Run B (cacheBuild d flag off tgt provideOut provideIn)
      sigma tau
      (2 + (3 + ((∑ k ∈ Finset.range n,
        (cacheBuildTurnCost D d kout kin k + 4)) + 6))) := by
    simpa only [cacheBuild] using rcount.seq (roff.seq rloop)
  exact hr.mono (by omega)

/-! ## Completed cache and aggregate charge -/

/-- The terminal construction invariant is exactly the persistent compact
cache memory consumed by `cachedIncomingOfHeavyCache`. -/
theorem heavyCacheMem_of_final {n W d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String}
    {E Deg R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (h : CacheBuildAt W P D d n flag off tgt
      E Deg R ID BH BV BN sigma) :
    ∃ T,
      SetCsrRows (heavyInRows D d) (cacheOff D d n)
        (cacheOff D d) T ∧
      Lax3Proofs.Refine.OrderVirtualCacheProvider.HeavyCacheMem
        D d (cacheOff D d n) n flag off tgt (cacheOff D d) T P sigma := by
  obtain ⟨F, hflag, hflagPrefix⟩ := h.flag
  obtain ⟨O, hoff, hoffPrefix⟩ := h.offset
  obtain ⟨T, htgt, htgtPrefix⟩ := h.target
  have hflagExact :
      sigma.arrs flag = arrOf n
        (Lax3Proofs.Refine.OrderVirtualCacheProvider.heavyBit D d) := by
    rw [hflag]
    apply arrOf_congr
    intro q hqn
    exact hflagPrefix q hqn hqn
  have hoffExact : sigma.arrs off = arrOf (n + 1) (cacheOff D d) := by
    rw [hoff]
    apply arrOf_congr
    intro q hq
    exact hoffPrefix q (by omega)
  have hrows := setCsrRows_of_cacheTargetPrefix htgtPrefix
  exact ⟨T, hrows, h.persistent,
    hflagExact, ⟨hoffExact, htgt, h.vrow_length⟩⟩

theorem cacheBuildTurnCost_le {D : Orientation n} {d : ℕ}
    (kout kin : ℕ → ℕ) {i : ℕ} (hi : i < n) :
    cacheBuildTurnCost D d kout kin i ≤
      kout i + kin i + 18 * cacheLen D d i + 22 := by
  classical
  rw [cacheBuildTurnCost, dif_pos hi]
  by_cases hheavy : (⟨i, hi⟩ : Fin n) ∈ heavyRoots D d
  · rw [if_pos hheavy, cacheLen_of_heavy hheavy]
    omega
  · rw [if_neg hheavy, cacheLen_of_light hheavy]
    omega

/-- Cache construction calls each provider at most once per root and copies
at most `n` retained cells. -/
theorem cacheBuildCost_le {D : Orientation n} {d : ℕ}
    (hd : D.InDegLE d) (kout kin : ℕ → ℕ) :
    ((∑ i ∈ Finset.range n,
        (cacheBuildTurnCost D d kout kin i + 4)) + 11) ≤
      (∑ i ∈ Finset.range n, kout i) +
      (∑ i ∈ Finset.range n, kin i) + 44 * n + 11 := by
  classical
  have hpoint :
      (∑ i ∈ Finset.range n, cacheBuildTurnCost D d kout kin i) ≤
        ∑ i ∈ Finset.range n,
          (kout i + kin i + 18 * cacheLen D d i + 22) := by
    apply Finset.sum_le_sum
    intro i hi
    exact cacheBuildTurnCost_le kout kin (Finset.mem_range.1 hi)
  have hoffLe : cacheOff D d n ≤ n := cacheOff_final_le hd
  have hsplit :
      (∑ i ∈ Finset.range n,
          (kout i + kin i + 18 * cacheLen D d i + 22)) =
        (∑ i ∈ Finset.range n, kout i) +
        (∑ i ∈ Finset.range n, kin i) +
        18 * cacheOff D d n + 22 * n := by
    simp only [Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, cacheOff]
    ring
  have hturn :
      (∑ i ∈ Finset.range n, cacheBuildTurnCost D d kout kin i) ≤
        (∑ i ∈ Finset.range n, kout i) +
        (∑ i ∈ Finset.range n, kin i) + 40 * n := by
    rw [hsplit] at hpoint
    omega
  have htotal :
      (∑ i ∈ Finset.range n,
          (cacheBuildTurnCost D d kout kin i + 4)) =
        (∑ i ∈ Finset.range n,
          cacheBuildTurnCost D d kout kin i) + 4 * n := by
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    omega
  rw [htotal]
  omega

/-! ## Axiom audit -/

#print axioms appendAt_succ_set
#print axioms cacheAppendSlot_run
#print axioms cacheAppend_run
#print axioms cacheOff_final
#print axioms CacheTargetPrefix.succ
#print axioms setCsrRows_of_cacheTargetPrefix
#print axioms cacheBuildTurn_spec
#print axioms cacheBuild_spec
#print axioms heavyCacheMem_of_final
#print axioms cacheBuildCost_le

end Lax3Proofs.Refine.OrderVirtualCacheBuild
