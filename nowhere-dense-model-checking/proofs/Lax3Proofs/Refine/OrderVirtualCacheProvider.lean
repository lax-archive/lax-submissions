import Lax3Proofs.Refine.OrderVirtualCacheMath
import Lax3Proofs.Refine.OrderVirtualSetCsr

/-!
# Heavy/light incoming-row provider

The incoming half of a transitive two-walk may request one root once for
every outgoing arc of that root.  This module exposes the executable branch
used by the repair: heavy roots are read from a compact cache, while light
roots invoke the child provider.  Crucially, the public charge records which
branch was taken instead of replacing both by a worst-case maximum.
-/

namespace Lax3Proofs.Refine.OrderVirtualCacheProvider

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.OrderVirtualCacheMath
open Lax3Proofs.Refine.OrderVirtualRows (transInWalkWork transInWalkWork_le)
open Lax3Proofs.Refine.OrderVirtualBaseProvider
open Lax3Proofs.Refine.OrderVirtualSetCsr
open Lax3Proofs.Refine.OrderVirtualFrat (FratScratchClosed)

variable {n : ℕ}

/-- The partial row family physically retained by the heavy cache. -/
noncomputable def heavyInRows (D : Orientation n) (d : ℕ)
    (w : Fin n) : Finset (Fin n) :=
  if w ∈ heavyRoots D d then D.inN w else ∅

@[simp] theorem heavyInRows_of_mem {D : Orientation n} {d : ℕ}
    {w : Fin n} (hw : w ∈ heavyRoots D d) :
    heavyInRows D d w = D.inN w := by
  simp [heavyInRows, hw]

@[simp] theorem heavyInRows_of_notMem {D : Orientation n} {d : ℕ}
    {w : Fin n} (hw : w ∉ heavyRoots D d) :
    heavyInRows D d w = ∅ := by
  simp [heavyInRows, hw]

/-- Numeric membership bit stored beside the compact cached rows. -/
noncomputable def heavyBit (D : Orientation n) (d i : ℕ) : ℕ :=
  if hi : i < n then
    if (⟨i, hi⟩ : Fin n) ∈ heavyRoots D d then 1 else 0
  else 0

@[simp] theorem heavyBit_of_mem {D : Orientation n} {d : ℕ}
    {w : Fin n} (hw : w ∈ heavyRoots D d) :
    heavyBit D d (w : ℕ) = 1 := by
  simp [heavyBit, w.isLt, hw]

@[simp] theorem heavyBit_of_notMem {D : Orientation n} {d : ℕ}
    {w : Fin n} (hw : w ∉ heavyRoots D d) :
    heavyBit D d (w : ℕ) = 0 := by
  simp [heavyBit, w.isLt, hw]

/-- The persistent predicate exposes the exact heavy-membership array. -/
def HasHeavyFlag (D : Orientation n) (d : ℕ) (flag : String)
    (sigma : Env) : Prop :=
  sigma.arrs flag = arrOf n (heavyBit D d)

/-- Select the retained row exactly on a heavy root. -/
def cachedIncomingProvide (flag : String) (cache child : Com) : Com :=
  .ite (.eq (.get flag (.var "w")) (.lit 1)) cache child

/-- Branch-sensitive charge of the cached incoming provider. -/
noncomputable def cachedIncomingCost (D : Orientation n) (d : ℕ)
    (kcache kchild : ℕ → ℕ) (w : ℕ) : ℕ :=
  if hw : w < n then
    (if (⟨w, hw⟩ : Fin n) ∈ heavyRoots D d then kcache w else kchild w) + 6
  else 0

@[simp] theorem cachedIncomingCost_of_heavy (D : Orientation n) (d : ℕ)
    (kcache kchild : ℕ → ℕ) {w : Fin n} (hw : w ∈ heavyRoots D d) :
    cachedIncomingCost D d kcache kchild (w : ℕ) = kcache w + 6 := by
  simp [cachedIncomingCost, w.isLt, hw]

@[simp] theorem cachedIncomingCost_of_light (D : Orientation n) (d : ℕ)
    (kcache kchild : ℕ → ℕ) {w : Fin n} (hw : w ∉ heavyRoots D d) :
    cachedIncomingCost D d kcache kchild (w : ℕ) = kchild w + 6 := by
  simp [cachedIncomingCost, w.isLt, hw]

/-- A cached partial-row provider and the original child provider combine to
an exact incoming-row provider.  Both branches deliberately use the same
persistent predicate; later construction lemmas establish that the child
frames the cache and the cache reader frames the child state. -/
theorem cachedIncomingProvidesSetRows {B n W : ℕ} {P : Env → Prop}
    {D : Orientation n} {d : ℕ} {flag dst : String}
    {cache child : Com} {kcache kchild : ℕ → ℕ}
    (hB1 : 1 < B) (hnB : n < B)
    (hflag : ∀ sigma, P sigma → HasHeavyFlag D d flag sigma)
    (hcache : ProvidesSetRows B n W (heavyInRows D d)
      P dst cache kcache)
    (hchild : ProvidesSetRows B n W (fun w => D.inN w)
      P dst child kchild) :
    ProvidesSetRows B n W (fun w => D.inN w) P dst
      (cachedIncomingProvide flag cache child)
      (cachedIncomingCost D d kcache kchild) := by
  classical
  intro w E Deg R ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hP, heng, hw⟩ := hpre
  have hflagEq := hflag sigma hP
  have hwB : (w : ℕ) < B := lt_trans w.isLt hnB
  have ew : (Expr.var "w").evalB B sigma = some (w : ℕ) := by
    have h := evalB_var (B := B) (x := "w") (σ := sigma) (by
      rw [hw]
      exact hwB)
    rwa [hw] at h
  have hflagLen : (sigma.arrs flag).length = n := by
    rw [hflagEq, length_arrOf]
  have hflagGet : (sigma.arrs flag).getD (w : ℕ) 0 =
      heavyBit D d (w : ℕ) := by
    rw [hflagEq, getD_arrOf _ w.isLt]
  have hflagB : (sigma.arrs flag).getD (w : ℕ) 0 < B := by
    rw [hflagGet]
    by_cases hheavy : w ∈ heavyRoots D d
    · simp [hheavy, hB1]
    · simp [hheavy]
      omega
  have eflag : (Expr.get flag (.var "w")).evalB B sigma =
      some (heavyBit D d (w : ℕ)) := by
    have h := RunStep.eval_get B sigma flag (.var "w") (w : ℕ)
      ew (by rw [hflagLen]; exact w.isLt) hflagB
    rwa [hflagGet] at h
  have eone : (Expr.lit 1).evalB B sigma = some 1 :=
    evalB_lit hB1
  have econd :
      (Cond.eq (.get flag (.var "w")) (.lit 1)).evalB B sigma =
        some (decide (heavyBit D d (w : ℕ) = 1)) :=
    evalB_condEq eflag eone
  by_cases hheavy : w ∈ heavyRoots D d
  · have etrue :
        (Cond.eq (.get flag (.var "w")) (.lit 1)).evalB B sigma =
          some true := by
      simpa [heavyBit_of_mem hheavy] using econd
    obtain ⟨tau, hr, hP', heng', hstable, tail, A, hrow,
        htail, hA⟩ :=
      (hcache w E Deg R ID BH BV BN).run ⟨hP, heng, hw⟩
    have hrow' : SetRowRep (D.inN w) tail A := by
      simpa [heavyInRows, hheavy] using hrow
    refine ⟨tau, cachedIncomingCost D d kcache kchild (w : ℕ), ?_,
      le_rfl, hP', heng', hstable, tail, A, hrow', htail, hA⟩
    have hrun := Run.ite_true (d := child) etrue hr
    simpa only [cachedIncomingProvide] using hrun.mono (by
      rw [cachedIncomingCost_of_heavy D d kcache kchild hheavy]
      simp [Cond.size, Expr.size]
      omega)
  · have efalse :
        (Cond.eq (.get flag (.var "w")) (.lit 1)).evalB B sigma =
          some false := by
      simpa [heavyBit_of_notMem hheavy] using econd
    obtain ⟨tau, hr, hP', heng', hstable, tail, A, hrow,
        htail, hA⟩ :=
      (hchild w E Deg R ID BH BV BN).run ⟨hP, heng, hw⟩
    refine ⟨tau, cachedIncomingCost D d kcache kchild (w : ℕ), ?_,
      le_rfl, hP', heng', hstable, tail, A, hrow, htail, hA⟩
    have hrun := Run.ite_false (c := cache) efalse hr
    simpa only [cachedIncomingProvide] using hrun.mono (by
      rw [cachedIncomingCost_of_light D d kcache kchild hheavy]
      simp [Cond.size, Expr.size]
      omega)

/-! ## A prebuilt compact cache -/

/-- Common persistent state of a child provider and one compact heavy-row
cache.  The cache reader and the child will be lifted to this same predicate
before the executable branch theorem is applied. -/
structure HeavyCacheMem (D : Orientation n) (d ns nt : ℕ)
    (flag o t : String) (O T : ℕ → ℕ) (P : Env → Prop)
    (sigma : Env) : Prop where
  persistent : P sigma
  flag_eq : HasHeavyFlag D d flag sigma
  csr : BaseCsrMem n nt o t O T sigma

/-- Reading a compact cache row preserves any child state closed under the
reader's scalar and `vrow` writes. -/
theorem heavyCacheProvidesSetRows {B n ns nt W : ℕ} {P : Env → Prop}
    {D : Orientation n} {d : ℕ} {flag o t : String} {O T : ℕ → ℕ}
    (hrows : SetCsrRows (heavyInRows D d) ns O T)
    (hclose : FratScratchClosed P)
    (hnsnt : ns ≤ nt) (hB : n + W + 1 < B) (hnsB : ns < B)
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames)
    (hflagv : flag ≠ "vrow") :
    ProvidesSetRows B n W (heavyInRows D d)
      (HeavyCacheMem D d ns nt flag o t O T P) "vrow"
      (baseProvide o t) (baseProvideCost O) := by
  have hbase := setCsrProvidesSetRows hrows hnsnt hB hnsB ho ht
  intro w E Deg R ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  obtain ⟨tau, hr, hcsr, heng', hstable, tail, A, hrow, htail, hA⟩ :=
    (hbase w E Deg R ID BH BV BN).run ⟨hmem.csr, heng, hw⟩
  have hP' : P tau := hclose.run hr
    (by
      intro a ha
      simp [baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, Com.wvars] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide)
    (by
      intro a ha
      simp [baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, Com.warrs] at ha
      exact Or.inl ha)
    (by simp [baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, Com.reads])
    (by simp [baseProvide, baseRowSlot, Csr.loadRow, Csr.scan, Com.NoWrite])
    hmem.persistent
  have hflag' : HasHeavyFlag D d flag tau := by
    rw [HasHeavyFlag, hr.frame_arr flag (by
      intro ha
      simp [baseProvide, baseRowSlot, Csr.loadRow, Csr.scan,
        Com.warrs] at ha
      exact hflagv ha)]
    exact hmem.flag_eq
  exact ⟨tau, baseProvideCost O w, hr, le_rfl,
    ⟨hP', hflag', hcsr⟩, heng', hstable, tail, A, hrow, htail, hA⟩

/-- A child provider frames a compact cache when it does not write the three
cache arrays.  Writes to the shared output buffer are harmless because IMP
array stores preserve its allocated length. -/
theorem childProvidesSetRows_underHeavyCache {B n ns nt W : ℕ}
    {P : Env → Prop} {D : Orientation n} {d : ℕ}
    {S : Fin n → Finset (Fin n)} {flag o t : String} {O T : ℕ → ℕ}
    {child : Com} {kchild : ℕ → ℕ}
    (hchild : ProvidesSetRows B n W S P "vrow" child kchild)
    (hflag : flag ∉ child.warrs) (ho : o ∉ child.warrs)
    (ht : t ∉ child.warrs) :
    ProvidesSetRows B n W S
      (HeavyCacheMem D d ns nt flag o t O T P) "vrow" child kchild := by
  intro w E Deg R ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  obtain ⟨tau, hr, hP', heng', hstable, tail, A, hrow, htail, hA⟩ :=
    (hchild w E Deg R ID BH BV BN).run ⟨hmem.persistent, heng, hw⟩
  have hflag' : HasHeavyFlag D d flag tau := by
    rw [HasHeavyFlag, hr.frame_arr flag hflag]
    exact hmem.flag_eq
  have hcsr' : BaseCsrMem n nt o t O T tau := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hr.frame_arr o ho]
      exact hmem.csr.off_eq
    · rw [hr.frame_arr t ht]
      exact hmem.csr.tgt_eq
    · rw [Lax3Proofs.RamDriver.run_length_arrs hr "vrow"]
      exact hmem.csr.row_length
  exact ⟨tau, kchild w, hr, le_rfl, ⟨hP', hflag', hcsr'⟩,
    heng', hstable, tail, A, hrow, htail, hA⟩

/-- The prebuilt cache and a framed child instantiate the heavy/light branch
as an exact incoming-row provider. -/
theorem cachedIncomingOfHeavyCache {B n ns nt W : ℕ} {P : Env → Prop}
    {D : Orientation n} {d : ℕ} {flag o t : String} {O T : ℕ → ℕ}
    {child : Com} {kchild : ℕ → ℕ}
    (hrows : SetCsrRows (heavyInRows D d) ns O T)
    (hclose : FratScratchClosed P)
    (hchild : ProvidesSetRows B n W (fun w => D.inN w)
      P "vrow" child kchild)
    (hchildFlag : flag ∉ child.warrs) (hchildO : o ∉ child.warrs)
    (hchildT : t ∉ child.warrs)
    (hB1 : 1 < B) (hnB : n < B)
    (hnsnt : ns ≤ nt) (hBW : n + W + 1 < B) (hnsB : ns < B)
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames)
    (hflagv : flag ≠ "vrow") :
    ProvidesSetRows B n W (fun w => D.inN w)
      (HeavyCacheMem D d ns nt flag o t O T P) "vrow"
      (cachedIncomingProvide flag (baseProvide o t) child)
      (cachedIncomingCost D d (baseProvideCost O) kchild) := by
  apply cachedIncomingProvidesSetRows hB1 hnB
    (fun _ hmem => hmem.flag_eq)
  · exact heavyCacheProvidesSetRows hrows hclose hnsnt hBW hnsB
      ho ht hflagv
  · exact childProvidesSetRows_underHeavyCache hchild
      hchildFlag hchildO hchildT

/-- On a heavy root, the compact cache branch has exactly the direct-copy
charge assumed by the global heavy/light estimate. -/
theorem baseProvideCost_heavy {D : Orientation n} {d ns : ℕ}
    {O T : ℕ → ℕ} (hrows : SetCsrRows (heavyInRows D d) ns O T)
    (z : Fin n) (hz : z ∈ heavyRoots D d) :
    baseProvideCost O z = 24 * (D.inN z).card + 14 := by
  rw [baseProvideCost]
  have htail := (hrows.row z).tail_eq
  simp only [heavyInRows, hz, if_true] at htail
  rw [htail]

/-! ## Aggregate charge -/

/-- Calls made by all incoming two-walk rows, counted with their actual
outer-row multiplicity. -/
noncomputable def incomingProviderCharge (D : Orientation n)
    (kappa : ℕ → ℕ) : ℕ :=
  ∑ v : Fin n, ∑ z ∈ D.inN v, kappa z

/-- The executable heavy/light branch has the required global charge.  A
cached heavy row costs at most its direct compact-row copy; the child charge
is paid only on light roots, while all copying and branch overhead are paid
by the bounded number of directed two-walk slots and arcs. -/
theorem incomingProviderCharge_cached_le {D : Orientation n} {d : ℕ}
    (hd : D.InDegLE d) (kcache kchild : ℕ → ℕ)
    (hcache : ∀ z : Fin n, z ∈ heavyRoots D d →
      kcache z ≤ 24 * (D.inN z).card + 14) :
    incomingProviderCharge D (cachedIncomingCost D d kcache kchild) ≤
      d * d * (∑ z : Fin n, kchild z) +
        24 * (n * (d * d)) + 20 * (n * d) := by
  classical
  have hpoint : ∀ z : Fin n,
      cachedIncomingCost D d kcache kchild z ≤
        (if z ∈ heavyRoots D d then 0 else kchild z) +
          24 * (D.inN z).card + 20 := by
    intro z
    by_cases hz : z ∈ heavyRoots D d
    · rw [cachedIncomingCost_of_heavy D d kcache kchild hz]
      simp only [hz, if_true, zero_add]
      exact Nat.add_le_add_right (hcache z hz) 6 |>.trans (by omega)
    · rw [cachedIncomingCost_of_light D d kcache kchild hz]
      simp only [hz, if_false]
      omega
  calc
    incomingProviderCharge D (cachedIncomingCost D d kcache kchild)
        ≤ ∑ v : Fin n, ∑ z ∈ D.inN v,
            ((if z ∈ heavyRoots D d then 0 else kchild z) +
              24 * (D.inN z).card + 20) := by
          apply Finset.sum_le_sum
          intro v _
          apply Finset.sum_le_sum
          intro z _
          exact hpoint z
    _ = lightIncomingCharge D d (fun z : Fin n => kchild z) +
          24 * transInWalkWork D +
          20 * (∑ v : Fin n, (D.inN v).card) := by
          simp only [lightIncomingCharge, transInWalkWork,
            Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
            Finset.mul_sum]
          ring
    _ ≤ d * d * (∑ z : Fin n, kchild z) +
          24 * (n * (d * d)) + 20 * (n * d) := by
          have hlight := lightIncomingCharge_le D d
            (fun z : Fin n => kchild z)
          have hwalk := transInWalkWork_le hd
          have harcs : (∑ v : Fin n, (D.inN v).card) ≤ n * d := by
            calc
              (∑ v : Fin n, (D.inN v).card) ≤ ∑ _v : Fin n, d :=
                Finset.sum_le_sum fun v _ => hd v
              _ = n * d := by
                rw [Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, smul_eq_mul]
          omega

/-- Specialization of the global estimate to the verified compact-row
reader. -/
theorem incomingProviderCharge_heavyCache_le {D : Orientation n} {d ns : ℕ}
    {O T : ℕ → ℕ} (hd : D.InDegLE d)
    (hrows : SetCsrRows (heavyInRows D d) ns O T)
    (kchild : ℕ → ℕ) :
    incomingProviderCharge D
        (cachedIncomingCost D d (baseProvideCost O) kchild) ≤
      d * d * (∑ z : Fin n, kchild z) +
        24 * (n * (d * d)) + 20 * (n * d) := by
  apply incomingProviderCharge_cached_le hd
  intro z hz
  exact (baseProvideCost_heavy hrows z hz).le

/-! ## Axiom audit -/

#print axioms cachedIncomingProvidesSetRows
#print axioms heavyCacheProvidesSetRows
#print axioms childProvidesSetRows_underHeavyCache
#print axioms cachedIncomingOfHeavyCache
#print axioms incomingProviderCharge_cached_le
#print axioms incomingProviderCharge_heavyCache_le

end Lax3Proofs.Refine.OrderVirtualCacheProvider
