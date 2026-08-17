import Lax3Proofs.Refine.OrderVirtualDriver
import Lax3Proofs.RamDriverAugment

/-!
# Exact finite-set rows and an emitting accumulator

Implicit orientation providers enumerate finite sets rather than an already
materialized graph row.  This file supplies their common output contract and
the constant-cost action that appends each freshly emitted vertex to a
carrier-sized buffer.
-/

namespace Lax3Proofs.Refine.OrderVirtualSetRow

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Refine.OrderVirtualRowRep (rowList mem_rowList_iff)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.RamDriverAugment
  (Emits Guarded Marks valSet mem_valSet card_valSet valSet_lt)
open Lax3Proofs.Augmentation (nbrsIn mem_nbrsIn)

variable {n : ℕ}

/-- A carrier buffer enumerates a given finset exactly once. -/
structure SetRowRep (S : Finset (Fin n)) (tail : ℕ) (A : ℕ → ℕ) : Prop where
  tail_eq : tail = S.card
  value_lt : ∀ p < tail, A p < n
  nodup : (rowList tail A).Nodup
  mem_iff : ∀ u : Fin n, (u : ℕ) ∈ rowList tail A ↔ u ∈ S

namespace SetRowRep

theorem tail_le {n tail : ℕ} {S : Finset (Fin n)} {A : ℕ → ℕ}
    (h : SetRowRep S tail A) : tail ≤ n := by
  rw [h.tail_eq]
  simpa only [Fintype.card_fin] using Finset.card_le_univ S

/-- Exact rows transport across changes outside their live prefix. -/
theorem congr_prefix {S : Finset (Fin n)} {tail : ℕ} {A : ℕ → ℕ}
    (h : SetRowRep S tail A) {A' : ℕ → ℕ}
    (heq : ∀ p < tail, A' p = A p) : SetRowRep S tail A' := by
  have hlist : rowList tail A' = rowList tail A := by
    apply List.ext_getElem
    · simp
    · intro p hp hp'
      simpa [rowList] using heq p (by simpa using hp)
  exact ⟨h.tail_eq, fun p hp => by rw [heq p hp]; exact h.value_lt p hp,
    by rw [hlist]; exact h.nodup, fun u => by rw [hlist]; exact h.mem_iff u⟩

theorem slot_ne {S : Finset (Fin n)} {tail : ℕ} {A : ℕ → ℕ}
    (h : SetRowRep S tail A) {p q : ℕ} (hp : p < tail) (hq : q < tail)
    (hpq : p ≠ q) : A p ≠ A q := by
  intro heq
  have hplen : p < (rowList tail A).length := by simpa using hp
  have hqlen : q < (rowList tail A).length := by simpa using hq
  have he : (rowList tail A)[p] = (rowList tail A)[q] := by
    simpa [rowList] using heq
  exact hpq ((List.Nodup.getElem_inj_iff h.nodup).1 he)

/-- An exact set row becomes the graph-row contract when its set is the
neighbourhood of the requested vertex. -/
theorem toRowRep {G : SimpleGraph (Fin n)} {w : Fin n}
    {S : Finset (Fin n)} {tail : ℕ} {A : ℕ → ℕ}
    (h : SetRowRep S tail A) (hS : S = nbrsIn G Finset.univ w) :
    Lax3Proofs.Refine.OrderVirtualRowRep.RowRep G w tail A := by
  refine ⟨h.tail_le, h.value_lt, h.nodup, ?_, ?_⟩
  · intro u
    have hm := h.mem_iff u
    rw [hS, mem_nbrsIn] at hm
    simpa using hm.symm
  · rw [h.tail_eq, hS]

end SetRowRep

/-- Appending at the old tail changes a live row by one final element. -/
theorem rowList_succ_upd (tail z : ℕ) (A : ℕ → ℕ) :
    rowList (tail + 1) (upd A tail z) = rowList tail A ++ [z] := by
  unfold rowList
  rw [List.ofFn_succ_last]
  congr 1
  · apply congrArg List.ofFn
    funext p
    change upd A tail z (p : ℕ) = A (p : ℕ)
    rw [upd_of_ne _ (by omega)]
  · simp

/-- State of a duplicate-free output action.  The abstract emitted set is
numeric because `RamDriverAugment.Emits` uses numeric candidates. -/
def RowFillAcc (dst : String) (n : ℕ) (Cap S : Finset ℕ) (tau : Env) : Prop :=
  S ⊆ Cap ∧
  ∃ A, tau.arrs dst = arrOf n A ∧ tau.vars "c" = S.card ∧
    (rowList S.card A).Nodup ∧
    ∀ z, z ∈ rowList S.card A ↔ z ∈ S

namespace RowFillAcc

theorem setVar {dst : String} {Cap S : Finset ℕ} {tau : Env}
    (h : RowFillAcc dst n Cap S tau) {y : String} (hy : y ≠ "c") (x : ℕ) :
    RowFillAcc dst n Cap S (tau.setVar y x) := by
  obtain ⟨hsub, A, hA, hc, hnd, hmem⟩ := h
  exact ⟨hsub, A, by simpa using hA,
    by rw [vars_setVar, if_neg (Ne.symm hy)]; exact hc, hnd, hmem⟩

theorem setArr_of_ne {dst a : String} {Cap S : Finset ℕ} {tau : Env}
    (h : RowFillAcc dst n Cap S tau) (ha : a ≠ dst) (p x : ℕ) :
    RowFillAcc dst n Cap S (tau.setArr a p x) := by
  obtain ⟨hsub, A, hA, hc, hnd, hmem⟩ := h
  exact ⟨hsub, A,
    by rw [arrs_setArr, if_neg (Ne.symm ha)]; exact hA,
    by simpa using hc, hnd, hmem⟩

/-- At the complete numeric image of a finset, the accumulator is its exact
`SetRowRep`. -/
theorem toSetRowRep {dst : String} {S : Finset (Fin n)} {tau : Env}
    {Cap : Finset ℕ} (h : RowFillAcc dst n Cap (valSet S) tau) :
    ∃ A, tau.arrs dst = arrOf n A ∧ tau.vars "c" = S.card ∧
      SetRowRep S S.card A := by
  obtain ⟨-, A, hA, hc, hnd, hmem⟩ := h
  have hcard := card_valSet S
  rw [hcard] at hc hnd hmem
  refine ⟨A, hA, ?_, rfl, ?_, hnd, ?_⟩
  · exact hc
  · intro p hp
    have hm : A p ∈ rowList S.card A := by
      rw [mem_rowList_iff]
      exact ⟨p, hp, rfl⟩
    exact valSet_lt ((hmem (A p)).1 hm)
  · intro u
    rw [hmem (u : ℕ), mem_valSet]
    constructor
    · rintro ⟨hu, hm⟩
      simpa using hm
    · intro hm
      exact ⟨u.isLt, by simpa using hm⟩

end RowFillAcc

/-! ## Provider surface -/

/-- A provider for an exact family of finite-set rows.  The destination is
parameterized so recursive providers can retain an outer row while invoking
an inner provider in another carrier-sized buffer. -/
def ProvidesSetRows (B n W : ℕ) (S : Fin n → Finset (Fin n))
    (P : Env → Prop) (dst : String) (provide : Com) (kappa : ℕ → ℕ) : Prop :=
  ∀ (w : Fin n) (E D R ID BH BV BN : ℕ → ℕ),
    Spec B
      (fun sigma => P sigma ∧ EngineArrays n W E D R ID BH BV BN sigma ∧
        sigma.vars "w" = (w : ℕ))
      provide
      (fun sigma sigma' => P sigma' ∧ EngineArrays n W E D R ID BH BV BN sigma' ∧
        ProviderStable sigma sigma' ∧
        ∃ tail A, SetRowRep (S w) tail A ∧ sigma'.vars "vtail" = tail ∧
          sigma'.arrs dst = arrOf n A)
      (kappa (w : ℕ))

/-- A set provider for exact graph neighbourhoods is a virtual-elimination
row provider. -/
theorem providesRows_of_setRows {B n W : ℕ} {G : SimpleGraph (Fin n)}
    {S : Fin n → Finset (Fin n)} {P : Env → Prop} {provide : Com}
    {kappa : ℕ → ℕ}
    (hp : ProvidesSetRows B n W S P "vrow" provide kappa)
    (hS : ∀ w, S w = nbrsIn G Finset.univ w) :
    ProvidesRows B n W G P provide kappa := by
  intro w E D R ID BH BV BN
  refine (hp w E D R ID BH BV BN).post fun sigma sigma' _ hpost => ?_
  obtain ⟨hP, heng, hstable, tail, A, hrow, htail, hA⟩ := hpost
  exact ⟨hP, heng, hstable, tail, A, hrow.toRowRep (hS w), htail, hA⟩

/-- Append the candidate in `u` and advance the emitted-cardinality scalar. -/
def rowFillAct (dst : String) : Com :=
  .seq (.store dst (.var "c") (.var "u"))
    (.assign "c" (.add (.var "c") (.lit 1)))

/-- The append action is an `Emits`: freshness is exactly what makes the
extended row duplicate-free. -/
theorem rowFillAcc_emits {B n : ℕ} {dst : String} {Cap : Finset ℕ}
    (hnB : n < B) (hCap : Cap ⊆ Finset.range n) :
    Emits B n 7 dst "@" (rowFillAct dst) Cap (RowFillAcc dst n Cap) := by
  classical
  rintro S tau z ⟨hsub, A, hA, hc, hnd, hmem⟩ hu hzn hzS hzCap
  have hcard : S.card < n := by
    have hins : insert z S ⊆ Finset.range n :=
      Finset.insert_subset (Finset.mem_range.2 hzn) (hsub.trans hCap)
    have hle := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hzS, Finset.card_range] at hle
    omega
  have hcB : tau.vars "c" < B := by rw [hc]; omega
  have huB : tau.vars "u" < B := by rw [hu]; omega
  have ec : (Expr.var "c").evalB B tau = some S.card := by
    have h := evalB_var (B := B) (x := "c") (σ := tau) hcB
    rwa [hc] at h
  have eu : (Expr.var "u").evalB B tau = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := tau) huB
    rwa [hu] at h
  have hslot : S.card < (tau.arrs dst).length := by
    rw [hA, length_arrOf]
    exact hcard
  let tau1 := tau.setArr dst S.card z
  have r1 : Run B (.store dst (.var "c") (.var "u")) tau tau1 3 :=
    Run.store ec eu hslot
  have hc1 : tau1.vars "c" = S.card := by simp [tau1, hc]
  have ec1 : (Expr.var "c").evalB B tau1 = some S.card := by
    have h := evalB_var (B := B) (x := "c") (σ := tau1) (by rw [hc1]; omega)
    rwa [hc1] at h
  have einc : (Expr.add (.var "c") (.lit 1)).evalB B tau1 = some (S.card + 1) :=
    evalB_bin ec1 (evalB_lit (by omega)) (by simp [Bop.apply]; omega)
  let tau2 := tau1.setVar "c" (S.card + 1)
  have r2 : Run B (.assign "c" (.add (.var "c") (.lit 1))) tau1 tau2 4 :=
    Run.assign einc
  have hcards : (insert z S).card = S.card + 1 := Finset.card_insert_of_notMem hzS
  refine ⟨tau2, 7, r1.seq r2, le_rfl, ?_, ?_, ?_⟩
  · refine ⟨Finset.insert_subset hzCap hsub,
      upd A S.card z, ?_, ?_, ?_, ?_⟩
    · simp [tau2, tau1, hA, set_arrOf_eq_upd]
    · simp [tau2, hcards]
    · rw [hcards, rowList_succ_upd]
      rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro haz
      subst a
      exact hzS ((hmem z).1 ha)
    · intro y
      rw [hcards, rowList_succ_upd, List.mem_append, List.mem_singleton, hmem]
      simp only [Finset.mem_insert]
      tauto
  · intro y hy
    simp [tau2, tau1, hy]
  · intro a ha _
    simp [tau2, tau1, ha]

/-! ## Contiguous reusable-buffer scans -/

/-- The union contributed by the live prefix of a reusable buffer. -/
def bufferAcc (tail : ℕ) (A : ℕ → ℕ) (fe : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range tail).biUnion fun p => fe (A p)

@[simp] theorem bufferAcc_zero (A : ℕ → ℕ) (fe : ℕ → Finset ℕ) :
    bufferAcc 0 A fe = ∅ := by
  simp [bufferAcc]

theorem mem_bufferAcc {tail : ℕ} {A : ℕ → ℕ} {fe : ℕ → Finset ℕ} {z : ℕ} :
    z ∈ bufferAcc tail A fe ↔ ∃ p < tail, z ∈ fe (A p) := by
  simp [bufferAcc]

theorem bufferAcc_succ (p : ℕ) (A : ℕ → ℕ) (fe : ℕ → Finset ℕ) :
    bufferAcc (p + 1) A fe = bufferAcc p A fe ∪ fe (A p) := by
  ext z
  rw [mem_bufferAcc, Finset.mem_union, mem_bufferAcc]
  constructor
  · rintro ⟨q, hq, hz⟩
    by_cases hqp : q = p
    · right
      simpa [hqp] using hz
    · left
      exact ⟨q, by omega, hz⟩
  · rintro (⟨q, hq, hz⟩ | hz)
    · exact ⟨q, by omega, hz⟩
    · exact ⟨p, by omega, hz⟩

theorem SetRowRep.mem_valSet_iff {S : Finset (Fin n)} {tail : ℕ}
    {A : ℕ → ℕ} (h : SetRowRep S tail A) (z : ℕ) :
    z ∈ valSet S ↔ ∃ p < tail, A p = z := by
  constructor
  · intro hz
    obtain ⟨hzn, hzS⟩ := mem_valSet.1 hz
    have hzrow : z ∈ rowList tail A := by
      simpa using (h.mem_iff ⟨z, hzn⟩).2 hzS
    exact mem_rowList_iff.1 hzrow
  · rintro ⟨p, hp, hpz⟩
    have hzn : z < n := by
      rw [← hpz]
      exact h.value_lt p hp
    apply mem_valSet.2
    refine ⟨hzn, (h.mem_iff ⟨z, hzn⟩).1 ?_⟩
    apply mem_rowList_iff.2
    exact ⟨p, hp, hpz⟩

/-- A weight summed over the live slots of an exact buffer is the same
weight summed over its abstract numeric set. -/
theorem SetRowRep.sum_slots {S : Finset (Fin n)} {tail : ℕ}
    {A : ℕ → ℕ} (h : SetRowRep S tail A) (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range tail, f (A p)) = ∑ z ∈ valSet S, f z := by
  classical
  refine Finset.sum_bij (i := fun p _ => A p) ?_ ?_ ?_ ?_
  · intro p hp
    exact (h.mem_valSet_iff (A p)).2 ⟨p, Finset.mem_range.1 hp, rfl⟩
  · intro p hp q hq hpq
    by_contra hne
    exact h.slot_ne (Finset.mem_range.1 hp) (Finset.mem_range.1 hq) hne hpq
  · intro z hz
    obtain ⟨p, hp, hpz⟩ := (h.mem_valSet_iff z).1 hz
    exact ⟨p, Finset.mem_range.2 hp, hpz⟩
  · intro _ _
    rfl

/-- A live exact buffer supports the same union as its abstract finite set. -/
theorem bufferAcc_eq_biUnion_valSet {S : Finset (Fin n)} {tail : ℕ}
    {A : ℕ → ℕ} (h : SetRowRep S tail A) (fe : ℕ → Finset ℕ) :
    bufferAcc tail A fe = (valSet S).biUnion fe := by
  ext z
  rw [mem_bufferAcc]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hz⟩
    exact ⟨A p, (h.mem_valSet_iff (A p)).2 ⟨p, hp, rfl⟩, hz⟩
  · rintro ⟨u, hu, hz⟩
    obtain ⟨p, hp, hpu⟩ := (h.mem_valSet_iff u).1 hu
    exact ⟨p, hp, by simpa [hpu] using hz⟩

/-- Scan the live prefix `[0, jend)` of a carrier buffer.  Unlike a CSR
block scan, no offset array is needed: exact row providers already expose
their tail in a scalar. -/
def bufferScan (src j jend u : String) (body : Com) : Com :=
  .seq (.assign j (.lit 0))
    (Csr.scan j jend (Lax3Proofs.RamDriverAugment.scanBody src j u body))

/-- A reusable buffer scan with a cost depending on each occupied slot. -/
theorem bufferScanC_run {B len hi : ℕ} {src j jend u : String} {body : Com}
    {costs A : ℕ → ℕ} {I : ℕ → Env → Prop} {sigma : Env}
    (hjje : j ≠ jend) (hhiB : hi < B) (hB1 : 1 < B) (hhilen : hi ≤ len)
    (hend : sigma.vars jend = hi)
    (hsrc : ∀ p tau, I p tau → tau.arrs src = arrOf len A)
    (hAB : ∀ p, p < hi → A p < B)
    (hIb : ∀ p tau, I p tau → tau.vars jend = hi ∧ tau.vars j = p ∧ p ≤ hi)
    (hstep : ∀ p tau, I p tau → p < hi →
      ∃ tau' K, Run B body (tau.setVar u (A p)) tau' K ∧ K ≤ costs p ∧
        tau'.vars j = p ∧ I (p + 1) (tau'.setVar j (p + 1)))
    (hstart : I 0 (sigma.setVar j 0)) :
    ∃ sigma' K, Run B (bufferScan src j jend u body) sigma sigma' K ∧
      K ≤ (∑ p ∈ Finset.range hi, (costs p + 11)) + 6 ∧ I hi sigma' := by
  let sigma1 := sigma.setVar j 0
  have r1 : Run B (.assign j (.lit 0)) sigma sigma1 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨sigma2, K2, r2, hK2, hI2⟩ :=
    Lax3Proofs.RamDriverAugment.rowScanC_run
      (B := B) (t := src) (j := j) (jend := jend) (w := u) (c := body)
      (len := len) (lo := 0) (hi := hi) (costs := costs) (tgt := A)
      (I := I) (σ := sigma1) hhiB hB1 hhilen hsrc hAB hIb hstep hstart
  refine ⟨sigma2, 2 + K2, ?_, ?_, hI2⟩
  · simpa only [bufferScan] using r1.seq r2
  · have hzero : Finset.Ico 0 hi = Finset.range hi := by
      ext x
      simp
    rw [hzero] at hK2
    omega

/-- Run a guarded emitter over an exact reusable buffer.  The cost is
charged once per occupied slot, and the abstract accumulator receives the
union contributed by precisely those slots. -/
theorem emitBuffer_run {B n tail Kg : ℕ} {src j jend : String} {grd : Com}
    {S : Finset (Fin n)} {A : ℕ → ℕ} {fe : ℕ → Finset ℕ}
    {J : Finset ℕ → Env → Prop} {E0 Cap : Finset ℕ} {sigma : Env}
    (hjje : j ≠ jend) (hju : j ≠ "u") (hjeu : jend ≠ "u")
    (hjc : j ≠ "c") (hjec : jend ≠ "c")
    (hB1 : 1 < B) (hnB : n < B)
    (hrow : SetRowRep S tail A) (hend : sigma.vars jend = tail)
    (hsrc : sigma.arrs src = arrOf n A)
    (hsrcJ : ∀ E tau, J E tau → tau.arrs src = arrOf n A)
    (hJv : ∀ E tau (y : String) (z : ℕ), (y = j ∨ y = "u") → J E tau →
      J E (tau.setVar y z))
    (hcap : ∀ p, p < tail → fe (A p) ⊆ Cap)
    (hg : Guarded B n Kg grd fe Cap J) (hJ0 : J E0 sigma) :
    ∃ sigma' K, Run B (bufferScan src j jend "u" grd) sigma sigma' K ∧
      K ≤ tail * (Kg + 11) + 6 ∧ J (E0 ∪ bufferAcc tail A fe) sigma' := by
  let I : ℕ → Env → Prop := fun p tau =>
    J (E0 ∪ bufferAcc p A fe) tau ∧ tau.vars jend = tail ∧
      tau.vars j = p ∧ p ≤ tail
  have htailB : tail < B := lt_of_le_of_lt hrow.tail_le hnB
  have hstart : I 0 (sigma.setVar j 0) := by
    refine ⟨?_, ?_, by simp, by omega⟩
    · simpa using hJv E0 sigma j 0 (Or.inl rfl) hJ0
    · rw [vars_setVar, if_neg (Ne.symm hjje)]
      exact hend
  obtain ⟨sigma', K, hrun, hK, hI⟩ :=
    bufferScanC_run (B := B) (len := n) (hi := tail)
      (src := src) (j := j) (jend := jend) (u := "u") (body := grd)
      (costs := fun _ => Kg) (A := A) (I := I) (sigma := sigma)
      hjje htailB hB1 hrow.tail_le hend
      (fun p tau h => hsrcJ _ _ h.1)
      (fun p hp => lt_trans (hrow.value_lt p hp) hnB)
      (fun p tau h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
      (by
        intro p tau hI hp
        have hval : A p < n := hrow.value_lt p hp
        have hJu : J (E0 ∪ bufferAcc p A fe) (tau.setVar "u" (A p)) :=
          hJv _ tau "u" (A p) (Or.inr rfl) hI.1
        obtain ⟨tau', K', hr, hK', hJ', hfv⟩ :=
          hg _ (tau.setVar "u" (A p)) (A p) hJu (by simp) hval (hcap p hp)
        have hj' : tau'.vars j = p := by
          rw [hfv j hjc, vars_setVar, if_neg hju, hI.2.2.1]
        have hJnext0 : J (E0 ∪ bufferAcc (p + 1) A fe) tau' := by
          rw [bufferAcc_succ]
          simpa only [Finset.union_assoc] using hJ'
        have hJnext : J (E0 ∪ bufferAcc (p + 1) A fe)
            (tau'.setVar j (p + 1)) :=
          hJv _ tau' j (p + 1) (Or.inl rfl) hJnext0
        refine ⟨tau', K', hr, hK', hj', hJnext, ?_, by simp, by omega⟩
        rw [vars_setVar, if_neg (Ne.symm hjje), hfv jend hjec,
          vars_setVar, if_neg hjeu]
        exact hI.2.1)
      hstart
  refine ⟨sigma', K, hrun, ?_, hI.1⟩
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hK
  exact hK

/-- Write one literal into every vertex named by an exact reusable buffer.
This is the buffer counterpart of `stampRow_run`; in particular it is the
cleanup operation used by virtual row providers. -/
theorem stampBuffer_run {B n tail b : ℕ} {src j jend u s : String}
    {S : Finset (Fin n)} {A g : ℕ → ℕ} {sigma : Env}
    (hjje : j ≠ jend) (hju : j ≠ u) (hjeu : jend ≠ u)
    (hst : s ≠ src) (hB1 : 1 < B) (hnB : n < B) (hbB : b < B)
    (hrow : SetRowRep S tail A) (hend : sigma.vars jend = tail)
    (hsrc : sigma.arrs src = arrOf n A) (hsa : sigma.arrs s = arrOf n g) :
    ∃ sigma' K,
      Run B (bufferScan src j jend u (.store s (.var u) (.lit b)))
        sigma sigma' K ∧
      K ≤ tail * 14 + 6 ∧ Marks s n b (valSet S) g sigma' := by
  classical
  let I : ℕ → Env → Prop := fun p tau =>
    tau.arrs src = arrOf n A ∧
      Marks s n b (bufferAcc p A (fun z => {z})) g tau ∧
      tau.vars jend = tail ∧ tau.vars j = p ∧ p ≤ tail
  have hstart : I 0 (sigma.setVar j 0) := by
    refine ⟨by simpa using hsrc, ?_, ?_, by simp, by omega⟩
    · exact Marks.zero ⟨g, by simpa using hsa, fun _ _ => rfl⟩
    · rw [vars_setVar, if_neg (Ne.symm hjje)]
      exact hend
  obtain ⟨sigma', K, hrun, hK, hI⟩ :=
    bufferScanC_run (B := B) (len := n) (hi := tail)
      (src := src) (j := j) (jend := jend) (u := u)
      (body := .store s (.var u) (.lit b)) (costs := fun _ => 3)
      (A := A) (I := I) (sigma := sigma) hjje
      (lt_of_le_of_lt hrow.tail_le hnB) hB1 hrow.tail_le hend
      (fun _ _ h => h.1)
      (fun p hp => lt_trans (hrow.value_lt p hp) hnB)
      (fun _ _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
      (by
        rintro p tau ⟨hsrcTau, ⟨g', hg', hgk⟩, hendTau, hjTau, hpLe⟩ hp
        let z := A p
        have hzn : z < n := hrow.value_lt p hp
        let tau0 := tau.setVar u z
        have huz : tau0.vars u = z := by simp [tau0]
        have eu : (Expr.var u).evalB B tau0 = some z := by
          have h := evalB_var (B := B) (x := u) (σ := tau0)
            (by rw [huz]; omega)
          rwa [huz] at h
        have hstamp : tau0.arrs s = arrOf n g' := by
          simpa [tau0] using hg'
        have hslot : z < (tau0.arrs s).length := by
          rw [hstamp, length_arrOf]
          exact hzn
        let tau1 := tau0.setArr s z b
        have hr : Run B (.store s (.var u) (.lit b)) tau0 tau1 3 :=
          Run.store eu (evalB_lit hbB) hslot
        refine ⟨tau1, 3, hr, le_rfl, ?_, ?_⟩
        · simp [tau1, tau0, hju, hjTau]
        refine ⟨?_, ?_, ?_, by simp, by omega⟩
        · rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hst), arrs_setVar]
          exact hsrcTau
        · refine ⟨fun k => if k = z then b else g' k, ?_, fun k hk => ?_⟩
          · rw [arrs_setVar, arrs_setArr, if_pos rfl, hstamp, set_arrOf]
          rw [bufferAcc_succ]
          change (if k = z then b else g' k) =
            if k ∈ bufferAcc p A (fun y => ({y} : Finset ℕ)) ∪ {A p}
              then b else g k
          by_cases hkz : k = z
          · subst k
            simp [z]
          · rw [if_neg hkz, hgk k hk]
            by_cases hkp : k ∈ bufferAcc p A (fun y => ({y} : Finset ℕ))
            · simp [hkp]
            · simp [hkp, hkz, z]
        · simp [tau1, tau0, Ne.symm hjje, hjeu, hendTau])
      hstart
  have hset : bufferAcc tail A (fun z => ({z} : Finset ℕ)) = valSet S := by
    rw [bufferAcc_eq_biUnion_valSet hrow]
    simp
  dsimp only [I] at hI
  rw [hset] at hI
  refine ⟨sigma', K, hrun, ?_, hI.2.1⟩
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hK
  omega

/-! ## Axiom audit -/

#print axioms rowList_succ_upd
#print axioms RowFillAcc.toSetRowRep
#print axioms rowFillAcc_emits
#print axioms bufferScanC_run
#print axioms emitBuffer_run
#print axioms stampBuffer_run
#print axioms providesRows_of_setRows

end Lax3Proofs.Refine.OrderVirtualSetRow
