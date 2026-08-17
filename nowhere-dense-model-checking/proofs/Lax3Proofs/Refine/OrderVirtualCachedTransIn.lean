import Lax3Proofs.Refine.OrderVirtualCacheBuild
import Lax3Proofs.Refine.OrderVirtualRename

/-!
# Cached incoming rows inside the transitive provider

The compact heavy-row cache is useful only after its reader and the original
child provider inhabit the same persistent state and the nested two-walk
provider can consume the result in `vin`.  This file closes that composition
boundary.  The cache reader is the verified compact-CSR reader transported by
the involutive exchange `vrow ↔ vin`; no second row-copy proof is introduced.
-/

namespace Lax3Proofs.Refine.OrderVirtualCachedTransIn

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamAugment
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.OrderVirtualBaseProvider
open Lax3Proofs.Refine.OrderVirtualSetCsr
open Lax3Proofs.Refine.OrderVirtualFrat
open Lax3Proofs.Refine.OrderVirtualBiUnion
open Lax3Proofs.Refine.OrderVirtualCacheProvider
open Lax3Proofs.Refine.OrderVirtualCacheBuild
open Lax3Proofs.Refine.OrderVirtualRename
open Lax3Proofs.RamDriverAugment (valSet)
open Lax3Proofs.Refine.OrderVirtualRows
  (transInWalkWork transInWalkWork_le)
open Lax3Proofs.Refine.ScatterBlock
  (renCom renEnv renCom_wvars renCom_warrs)

variable {n : ℕ}

/-! ## The common persistent workspace -/

/-- Arrays which the cache reader or the enclosing nested-union provider may
mutate while the child provider's persistent data remain resident. -/
def cachedTransScratchArrNames : List String :=
  ["vrow", "vin", "vout", "vsave", "stf"]

/-- Closure of the child-persistent state under the scratch owned by the
cached transitive provider. -/
structure CachedTransScratchClosed (P : Env → Prop) : Prop where
  setVar : ∀ {sigma : Env} {a : String} {x : ℕ}, a ≠ "n" →
    P sigma → P (sigma.setVar a x)
  setArr : ∀ {sigma : Env} {a : String} {p x : ℕ},
    a ∈ cachedTransScratchArrNames →
    P sigma → P (sigma.setArr a p x)

namespace CachedTransScratchClosed

/-- Any tape-free IMP command confined to the cached-transitive scratch
preserves the child-persistent state. -/
theorem run {B K : ℕ} {P : Env → Prop} {c : Com} {sigma tau : Env}
    (hclose : CachedTransScratchClosed P)
    (hr : Run B c sigma tau K)
    (hvars : ∀ a ∈ c.wvars, a ≠ "n")
    (harrs : ∀ a ∈ c.warrs, a ∈ cachedTransScratchArrNames)
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
      have ha0 : ∀ a ∈ c0.warrs, a ∈ cachedTransScratchArrNames :=
        fun a ha => harrs a (by simp [Com.warrs, ha])
      have ha1 : ∀ a ∈ c1.warrs, a ∈ cachedTransScratchArrNames :=
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
      have ha : ∀ a ∈ c0.warrs, a ∈ cachedTransScratchArrNames :=
        fun a hx => harrs a (by simpa [Com.warrs] using hx)
      have hrs : ¬ c0.reads := by simpa [Com.reads] using hreads
      have hws : c0.NoWrite := by simpa [Com.NoWrite] using hwrites
      exact ihw hvars harrs hreads hwrites (ihc hv ha hrs hws hP)
  | while_false hb => exact hP
  | read h => exact False.elim (hreads (by simp [Com.reads]))
  | write he => exact False.elim (by simpa [Com.NoWrite] using hwrites)

end CachedTransScratchClosed

/-- The compact heavy cache together with the two private row buffers needed
by a nested incoming two-walk.  The public `vrow` length already belongs to
`HeavyCacheMem`. -/
structure CachedTransMem (D : Orientation n) (d ns nt : ℕ)
    (flag off tgt : String) (O T : ℕ → ℕ) (P : Env → Prop)
    (sigma : Env) : Prop where
  cache : HeavyCacheMem D d ns nt flag off tgt O T P sigma
  vin_length : (sigma.arrs "vin").length = n
  vout_length : (sigma.arrs "vout").length = n

/-- Fresh cache names make the common cache memory closed under every parent
scratch update. -/
theorem cachedTransMem_closed {D : Orientation n} {d ns nt : ℕ}
    {flag off tgt : String} {O T : ℕ → ℕ} {P : Env → Prop}
    (hclose : CachedTransScratchClosed P)
    (hflag : flag ∉ cachedTransScratchArrNames)
    (hoff : off ∉ cachedTransScratchArrNames)
    (htgt : tgt ∉ cachedTransScratchArrNames) :
    CachedTransScratchClosed
      (CachedTransMem D d ns nt flag off tgt O T P) := by
  constructor
  · intro sigma a x han hmem
    refine ⟨⟨hclose.setVar han hmem.cache.persistent, ?_, ?_⟩, ?_, ?_⟩
    · simpa using hmem.cache.flag_eq
    · exact ⟨by simpa using hmem.cache.csr.off_eq,
        by simpa using hmem.cache.csr.tgt_eq,
        by simpa using hmem.cache.csr.row_length⟩
    · simpa using hmem.vin_length
    · simpa using hmem.vout_length
  · intro sigma a p x ha hmem
    have haflag : a ≠ flag := fun e => hflag (e ▸ ha)
    have haoff : a ≠ off := fun e => hoff (e ▸ ha)
    have hatgt : a ≠ tgt := fun e => htgt (e ▸ ha)
    refine ⟨⟨hclose.setArr ha hmem.cache.persistent, ?_, ?_⟩, ?_, ?_⟩
    · rw [HasHeavyFlag, arrs_setArr, if_neg (Ne.symm haflag)]
      exact hmem.cache.flag_eq
    · refine ⟨?_, ?_, ?_⟩
      · simpa [Ne.symm haoff] using hmem.cache.csr.off_eq
      · simpa [Ne.symm hatgt] using hmem.cache.csr.tgt_eq
      · exact (length_arrs_setArr
          (σ := sigma) (a := a) (i := p) (v := x) (b := "vrow")).trans
          hmem.cache.csr.row_length
    · exact (length_arrs_setArr
        (σ := sigma) (a := a) (i := p) (v := x) (b := "vin")).trans
        hmem.vin_length
    · exact (length_arrs_setArr
        (σ := sigma) (a := a) (i := p) (v := x) (b := "vout")).trans
        hmem.vout_length

/-- The common memory supplies the closure expected by the existing nested
union proof. -/
theorem cachedTransMem_fratClosed {D : Orientation n} {d ns nt : ℕ}
    {flag off tgt : String} {O T : ℕ → ℕ} {P : Env → Prop}
    (hclose : CachedTransScratchClosed P)
    (hflag : flag ∉ cachedTransScratchArrNames)
    (hoff : off ∉ cachedTransScratchArrNames)
    (htgt : tgt ∉ cachedTransScratchArrNames) :
    FratScratchClosed (CachedTransMem D d ns nt flag off tgt O T P) := by
  have h := cachedTransMem_closed (D := D) (d := d) (ns := ns) (nt := nt)
    (O := O) (T := T) hclose hflag hoff htgt
  refine ⟨h.setVar, ?_, ?_, ?_⟩
  · intro sigma p x hm
    exact h.setArr (by simp [cachedTransScratchArrNames]) hm
  · intro sigma p x hm
    exact h.setArr (by simp [cachedTransScratchArrNames]) hm
  · intro sigma p x hm
    exact h.setArr (by simp [cachedTransScratchArrNames]) hm

/-! ## A compact cache reader writing `vin` -/

/-- Exchange the public provider buffer with the nested incoming buffer. -/
def cacheVinSwap : String → String := arraySwap "vrow" "vin"

/-- The existing compact-CSR reader, transported to write `vin`. -/
def cacheProvideVin (off tgt : String) : Com :=
  renCom cacheVinSwap (baseProvide off tgt)

theorem cacheVinSwap_invol (z : String) :
    cacheVinSwap (cacheVinSwap z) = z :=
  arraySwap_invol "vrow" "vin" z

theorem cacheVinSwap_fixesEngine : FixesEngine cacheVinSwap :=
  arraySwap_fixesEngine (by decide) (by decide)

/-- The renamed compact reader preserves the common cache workspace and
returns the exact selected row in `vin`. -/
theorem cacheVinProvidesSetRows {B n ns nt W d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String} {O T : ℕ → ℕ}
    (hrows : SetCsrRows (heavyInRows D d) ns O T)
    (hclose : CachedTransScratchClosed P)
    (hflag : flag ∉ cachedTransScratchArrNames)
    (hoffScratch : off ∉ cachedTransScratchArrNames)
    (htgtScratch : tgt ∉ cachedTransScratchArrNames)
    (hnsnt : ns ≤ nt) (hB : n + W + 1 < B) (hnsB : ns < B)
    (hoffEngine : off ∉ engineArrNames)
    (htgtEngine : tgt ∉ engineArrNames) :
    ProvidesSetRows B n W (heavyInRows D d)
      (CachedTransMem D d ns nt flag off tgt O T P) "vin"
      (cacheProvideVin off tgt) (baseProvideCost O) := by
  have hbase := setCsrProvidesSetRows hrows hnsnt hB hnsB
    hoffEngine htgtEngine
  have hren : ProvidesSetRows B n W (heavyInRows D d)
      (fun sigma => BaseCsrMem n nt off tgt O T (renEnv cacheVinSwap sigma))
      "vin" (cacheProvideVin off tgt) (baseProvideCost O) := by
    simpa [cacheVinSwap, cacheProvideVin, arraySwap] using
      (providesSetRows_ren cacheVinSwap_invol cacheVinSwap_fixesEngine hbase)
  have hmemClose := cachedTransMem_closed (D := D) (d := d)
    (ns := ns) (nt := nt) (O := O) (T := T)
    hclose hflag hoffScratch htgtScratch
  intro w E Deg R ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  have hoffRow : off ≠ "vrow" := fun e =>
    hoffScratch (e ▸ by simp [cachedTransScratchArrNames])
  have hoffVin : off ≠ "vin" := fun e =>
    hoffScratch (e ▸ by simp [cachedTransScratchArrNames])
  have htgtRow : tgt ≠ "vrow" := fun e =>
    htgtScratch (e ▸ by simp [cachedTransScratchArrNames])
  have htgtVin : tgt ≠ "vin" := fun e =>
    htgtScratch (e ▸ by simp [cachedTransScratchArrNames])
  have hbaseMem : BaseCsrMem n nt off tgt O T (renEnv cacheVinSwap sigma) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
        show cacheVinSwap off = off by
        exact arraySwap_of_ne hoffRow hoffVin]
      exact hmem.cache.csr.off_eq
    · rw [Lax3Proofs.Refine.ScatterBlock.renEnv_arrs,
        show cacheVinSwap tgt = tgt by
        exact arraySwap_of_ne htgtRow htgtVin]
      exact hmem.cache.csr.tgt_eq
    · simpa [cacheVinSwap, arraySwap] using hmem.vin_length
  obtain ⟨tau, hr, -, heng', hstable, tail, A, hrow, htail, hA⟩ :=
    (hren w E Deg R ID BH BV BN).run ⟨hbaseMem, heng, hw⟩
  have hmem' : CachedTransMem D d ns nt flag off tgt O T P tau :=
    hmemClose.run hr
      (by
        intro a ha
        simp [cacheProvideVin, baseProvide, baseRowSlot, Csr.loadRow,
          Csr.scan, renCom_wvars, Com.wvars] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha
        simp [cacheProvideVin, cacheVinSwap, baseProvide, baseRowSlot,
          Csr.loadRow, Csr.scan, renCom_warrs, arraySwap, Com.warrs] at ha
        subst a
        simp [cachedTransScratchArrNames])
      (by simp [cacheProvideVin, renCom, baseProvide, baseRowSlot,
        Csr.loadRow, Csr.scan, Com.reads])
      (Lax3Proofs.Refine.ScatterBlock.renCom_noWrite cacheVinSwap (by
        simp [baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, Com.NoWrite])) hmem
  exact ⟨tau, baseProvideCost O w, hr, le_rfl, hmem', heng', hstable,
    tail, A, hrow, htail, hA⟩

/-! ## Lifting child providers through the cache -/

/-- A provider that frames the three cache arrays preserves the complete
common cache workspace.  Array stores preserve the three row-buffer lengths
even when the provider writes one of those buffers. -/
theorem providesSetRows_underCachedTransMem {B n ns nt W d : ℕ}
    {P : Env → Prop} {D : Orientation n}
    {S : Fin n → Finset (Fin n)} {flag off tgt dst : String}
    {O T : ℕ → ℕ} {provide : Com} {kappa : ℕ → ℕ}
    (hp : ProvidesSetRows B n W S P dst provide kappa)
    (hflag : flag ∉ provide.warrs) (hoff : off ∉ provide.warrs)
    (htgt : tgt ∉ provide.warrs) :
    ProvidesSetRows B n W S
      (CachedTransMem D d ns nt flag off tgt O T P) dst provide kappa := by
  intro w E Deg R ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  obtain ⟨tau, hr, hP', heng', hstable, tail, A, hrow, htail, hA⟩ :=
    (hp w E Deg R ID BH BV BN).run ⟨hmem.cache.persistent, heng, hw⟩
  have hflag' : HasHeavyFlag D d flag tau := by
    rw [HasHeavyFlag, hr.frame_arr flag hflag]
    exact hmem.cache.flag_eq
  have hcsr' : BaseCsrMem n nt off tgt O T tau := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hr.frame_arr off hoff]
      exact hmem.cache.csr.off_eq
    · rw [hr.frame_arr tgt htgt]
      exact hmem.cache.csr.tgt_eq
    · rw [Lax3Proofs.RamDriver.run_length_arrs hr "vrow"]
      exact hmem.cache.csr.row_length
  have hvin' : (tau.arrs "vin").length = n := by
    rw [Lax3Proofs.RamDriver.run_length_arrs hr "vin"]
    exact hmem.vin_length
  have hvout' : (tau.arrs "vout").length = n := by
    rw [Lax3Proofs.RamDriver.run_length_arrs hr "vout"]
    exact hmem.vout_length
  exact ⟨tau, kappa w, hr, le_rfl,
    ⟨⟨hP', hflag', hcsr'⟩, hvin', hvout'⟩,
    heng', hstable, tail, A, hrow, htail, hA⟩

/-! ## The cached nested incoming provider -/

/-- Heavy roots read the compact cache in `vin`; light roots invoke the
original named child provider. -/
def cachedIncomingVin (flag off tgt : String) (child : Com) : Com :=
  cachedIncomingProvide flag (cacheProvideVin off tgt) child

/-- The named cache reader and a cache-framing child form an exact incoming
row provider in the common workspace. -/
theorem cachedIncomingVinProvidesSetRows
    {B n ns nt W d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String} {O T : ℕ → ℕ}
    {child : Com} {kchild : ℕ → ℕ}
    (hrows : SetCsrRows (heavyInRows D d) ns O T)
    (hclose : CachedTransScratchClosed P)
    (hflagScratch : flag ∉ cachedTransScratchArrNames)
    (hoffScratch : off ∉ cachedTransScratchArrNames)
    (htgtScratch : tgt ∉ cachedTransScratchArrNames)
    (hchild : ProvidesSetRows B n W (fun w => D.inN w)
      P "vin" child kchild)
    (hchildFlag : flag ∉ child.warrs)
    (hchildOff : off ∉ child.warrs)
    (hchildTgt : tgt ∉ child.warrs)
    (hB1 : 1 < B) (hnB : n < B)
    (hnsnt : ns ≤ nt) (hBW : n + W + 1 < B) (hnsB : ns < B)
    (hoffEngine : off ∉ engineArrNames)
    (htgtEngine : tgt ∉ engineArrNames) :
    ProvidesSetRows B n W (fun w => D.inN w)
      (CachedTransMem D d ns nt flag off tgt O T P) "vin"
      (cachedIncomingVin flag off tgt child)
      (cachedIncomingCost D d (baseProvideCost O) kchild) := by
  apply cachedIncomingProvidesSetRows hB1 hnB
    (fun _ hmem => hmem.cache.flag_eq)
  · exact cacheVinProvidesSetRows hrows hclose hflagScratch
      hoffScratch htgtScratch hnsnt hBW hnsB hoffEngine htgtEngine
  · exact providesSetRows_underCachedTransMem hchild
      hchildFlag hchildOff hchildTgt

/-- The cached branch inherits every frame required of a nested incoming-row
provider.  Its cache arm writes only `vin`. -/
theorem cachedIncomingVin_frames {flag off tgt : String} {child : Com}
    (hchild : FratIncomingFrames child) :
    FratIncomingFrames (cachedIncomingVin flag off tgt child) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
        baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, renCom_wvars,
        Com.wvars] using hchild.stable.n
    · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
        baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, renCom_wvars,
        Com.wvars] using hchild.stable.i
    · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
        baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, renCom_wvars,
        Com.wvars] using hchild.stable.sp
    · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
        baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, renCom_wvars,
        Com.wvars] using hchild.stable.ls
    · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
        baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, renCom_wvars,
        Com.wvars] using hchild.stable.cnt
    · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
        baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, renCom_wvars,
        Com.wvars] using hchild.stable.mind
    · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
        baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, renCom_wvars,
        Com.wvars] using hchild.stable.kmax
  · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
      cacheVinSwap, baseProvide, baseRowSlot, Csr.loadRow, Csr.scan,
      renCom_warrs, arraySwap, Com.warrs] using hchild.vout
  · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
      cacheVinSwap, baseProvide, baseRowSlot, Csr.loadRow, Csr.scan,
      renCom_warrs, arraySwap, Com.warrs] using hchild.vrow
  · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
      cacheVinSwap, baseProvide, baseRowSlot, Csr.loadRow, Csr.scan,
      renCom_warrs, arraySwap, Com.warrs] using hchild.stamp
  · simpa [cachedIncomingVin, cachedIncomingProvide, cacheProvideVin,
      cacheVinSwap, baseProvide, baseRowSlot, Csr.loadRow, Csr.scan,
      renCom_warrs, arraySwap, Com.warrs] using hchild.save

/-- End-to-end cached incoming two-walk rows.  The inner provider is selected
by the verified heavy/light branch inside the existing erased-biunion
machine, so a heavy root is no longer regenerated at every outgoing
occurrence. -/
theorem virtualTransInCachedProvidesSetRows
    {B n ns nt W d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String} {O T : ℕ → ℕ}
    {provideOuter provideInner : Com} {kouter kinner : ℕ → ℕ}
    (hrows : SetCsrRows (heavyInRows D d) ns O T)
    (hclose : CachedTransScratchClosed P)
    (hflagScratch : flag ∉ cachedTransScratchArrNames)
    (hoffScratch : off ∉ cachedTransScratchArrNames)
    (htgtScratch : tgt ∉ cachedTransScratchArrNames)
    (hinnerFrames : FratIncomingFrames provideInner)
    (houterFrames : FratOutgoingFrames provideOuter)
    (hinnerFlag : flag ∉ provideInner.warrs)
    (hinnerOff : off ∉ provideInner.warrs)
    (hinnerTgt : tgt ∉ provideInner.warrs)
    (houterFlag : flag ∉ provideOuter.warrs)
    (houterOff : off ∉ provideOuter.warrs)
    (houterTgt : tgt ∉ provideOuter.warrs)
    (hB4 : 3 < B) (hnB : n < B)
    (hnsnt : ns ≤ nt) (hBW : n + W + 1 < B) (hnsB : ns < B)
    (hoffEngine : off ∉ engineArrNames)
    (htgtEngine : tgt ∉ engineArrNames)
    (hinner : ProvidesSetRows B n W (fun w => D.inN w)
      P "vin" provideInner kinner)
    (houter : ProvidesSetRows B n W (fun w => D.inN w)
      P "vout" provideOuter kouter) :
    ProvidesSetRows B n W (transInSet D)
      (FratWorkspace n
        (CachedTransMem D d ns nt flag off tgt O T P)) "vrow"
      (virtualFratProvide provideOuter
        (cachedIncomingVin flag off tgt provideInner))
      (eraseBiCost kouter
        (cachedIncomingCost D d (baseProvideCost O) kinner)
        (fun w => D.inN w) (fun w => D.inN w)) := by
  apply virtualTransInProvidesSetRows
    (cachedTransMem_fratClosed hclose hflagScratch hoffScratch htgtScratch)
    (cachedIncomingVin_frames hinnerFrames) houterFrames hB4 hnB
  · exact cachedIncomingVinProvidesSetRows hrows hclose hflagScratch
      hoffScratch htgtScratch hinner hinnerFlag hinnerOff hinnerTgt
      (by omega) hnB hnsnt hBW hnsB hoffEngine htgtEngine
  · exact providesSetRows_underCachedTransMem houter
      houterFlag houterOff houterTgt

/-! ## Aggregate cached-transitive charge -/

/-- Summing a numerical weight over the value image of a finite vertex set
is the same as summing it over the vertices themselves. -/
private theorem sum_valSet_eq (S : Finset (Fin n)) (f : ℕ → ℕ) :
    (∑ z ∈ valSet S, f z) = ∑ z ∈ S, f z := by
  rw [valSet, Finset.sum_image]
  intro a _ b _ hab
  exact Fin.val_injective hab

/-- Exact expansion of the cost of all cached incoming two-walk rows.  The
inner-provider term is kept as `incomingProviderCharge`, so the heavy/light
amortisation theorem applies without losing its actual call multiplicity. -/
theorem sum_eraseBiCost_transIn_eq {D : Orientation n}
    (kouter kin : ℕ → ℕ) :
    (∑ w : Fin n,
      eraseBiCost kouter kin (fun v => D.inN v) (fun v => D.inN v) w) =
      (∑ w : Fin n, kouter w) +
      incomingProviderCharge D kin +
      26 * transInWalkWork D +
      43 * (∑ w : Fin n, (D.inN w).card) +
      14 * (∑ w : Fin n, (transInSet D w).card) +
      30 * n := by
  classical
  simp only [eraseBiCost, Fin.isLt, dif_pos, Fin.eta, sum_valSet_eq,
    eraseBiSlotBudget_of_lt, Finset.sum_add_distrib, Finset.sum_const,
    smul_eq_mul, incomingProviderCharge, transInWalkWork, Finset.mul_sum]
  simp only [transInSet, Finset.card_univ, Fintype.card_fin]
  ring

/-- The cached incoming two-walk provider has an almost-linear aggregate
charge.  In particular, the child-provider total is multiplied by `d²`, not
by the number of outgoing occurrences of heavy roots. -/
theorem sum_eraseBiCost_transIn_cached_le {D : Orientation n} {d ns : ℕ}
    {O T : ℕ → ℕ} (hd : D.InDegLE d)
    (hrows : SetCsrRows (heavyInRows D d) ns O T)
    (kouter kinner : ℕ → ℕ) :
    (∑ w : Fin n,
      eraseBiCost kouter
        (cachedIncomingCost D d (baseProvideCost O) kinner)
        (fun v => D.inN v) (fun v => D.inN v) w) ≤
      (∑ w : Fin n, kouter w) +
      d * d * (∑ z : Fin n, kinner z) +
      64 * (n * (d * d)) + 63 * (n * d) + 30 * n := by
  rw [sum_eraseBiCost_transIn_eq]
  have hcharge := incomingProviderCharge_heavyCache_le hd hrows kinner
  have hwalk := transInWalkWork_le hd
  have harcs : (∑ v : Fin n, (D.inN v).card) ≤ n * d := by
    calc
      (∑ v : Fin n, (D.inN v).card) ≤ ∑ _v : Fin n, d :=
        Finset.sum_le_sum fun v _ => hd v
      _ = n * d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
  have hrowsum : (∑ v : Fin n, (transInSet D v).card) ≤
      n * (d * d) := by
    classical
    calc
      (∑ v : Fin n, (transInSet D v).card) ≤
          ∑ v : Fin n, ∑ z ∈ D.inN v, (D.inN z).card := by
            apply Finset.sum_le_sum
            intro v _
            exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
              Finset.card_biUnion_le
      _ = transInWalkWork D := rfl
      _ ≤ n * (d * d) := transInWalkWork_le hd
  omega

/-! ## Builder-to-reader seam -/

/-- The terminal executable cache invariant, together with the two retained
nested buffers, is exactly the common memory consumed by the cached
`transIn` provider. -/
theorem cachedTransMem_of_final {n W d : ℕ} {P : Env → Prop}
    {D : Orientation n} {flag off tgt : String}
    {E Deg R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (h : CacheBuildAt W P D d n flag off tgt
      E Deg R ID BH BV BN sigma)
    (hvin : (sigma.arrs "vin").length = n)
    (hvout : (sigma.arrs "vout").length = n) :
    ∃ T,
      SetCsrRows (heavyInRows D d) (cacheOff D d n)
        (cacheOff D d) T ∧
      CachedTransMem D d (cacheOff D d n) n flag off tgt
        (cacheOff D d) T P sigma := by
  obtain ⟨T, hrows, hcache⟩ := heavyCacheMem_of_final h
  exact ⟨T, hrows, hcache, hvin, hvout⟩

/-! ## Axiom audit for the cached transitive boundary -/

#print axioms cacheVinProvidesSetRows
#print axioms providesSetRows_underCachedTransMem
#print axioms cachedIncomingVinProvidesSetRows
#print axioms cachedIncomingVin_frames
#print axioms virtualTransInCachedProvidesSetRows
#print axioms sum_eraseBiCost_transIn_eq
#print axioms sum_eraseBiCost_transIn_cached_le
#print axioms cachedTransMem_of_final

end Lax3Proofs.Refine.OrderVirtualCachedTransIn
