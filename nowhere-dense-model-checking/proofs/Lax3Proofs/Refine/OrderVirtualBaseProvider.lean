import Lax3Proofs.Refine.OrderVirtualLoop

/-!
# CSR row provider for the virtual ordering engine

The base graph is already present as the compact CSR of the active arena.
This provider copies only the requested row into the reusable carrier-sized
buffer.  It is the executable base case of the recursive virtual providers.
-/

namespace Lax3Proofs.Refine.OrderVirtualBaseProvider

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation (nbrsIn)
open Lax3Proofs.RamBfs
open Lax3Proofs.RamElim (CsrSimple card_liveSlots liveSlots masked_of_all_alive
  card_nbrsIn_lt)
open Lax3Proofs.Refine.OrderVirtualRowRep
open Lax3Proofs.Refine.OrderVirtualProvider

/-- The function stored by a direct copy of CSR row `w`. -/
def csrRowFun (O T : ℕ → ℕ) (w p : ℕ) : ℕ := T (O w + p)

/-- A simple CSR row is already an exact duplicate-free virtual row. -/
theorem csrRowRep {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (w : Fin n) :
    RowRep G w (Csr.rowLen O (w : ℕ)) (csrRowFun O T (w : ℕ)) := by
  classical
  have hmono : O (w : ℕ) ≤ O ((w : ℕ) + 1) :=
    hcsr.csr.mono (w : ℕ) w.isLt
  have hend : O ((w : ℕ) + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  have hcard : Csr.rowLen O (w : ℕ) =
      (nbrsIn G Finset.univ w).card := by
    have hc := card_liveSlots (M := fun _ => 1) hcsr w.isLt (by simp)
    have hlive : liveSlots O T (fun _ => 1) (w : ℕ) =
        Finset.Ico (O (w : ℕ)) (O ((w : ℕ) + 1)) := by
      ext j
      simp [liveSlots]
    rw [hlive, Nat.card_Ico,
      masked_of_all_alive G (by simp)] at hc
    simpa only [Csr.rowLen] using hc
  refine ⟨?_, ?_, ?_, ?_, hcard⟩
  · rw [hcard]
    exact (card_nbrsIn_lt Finset.univ w).le
  · intro p hp
    apply hcsr.csr.target_lt
    dsimp [csrRowFun]
    have : O (w : ℕ) + p < O ((w : ℕ) + 1) := by
      simp only [Csr.rowLen] at hp
      omega
    omega
  · rw [List.nodup_iff_injective_getElem]
    intro i j hij
    apply Fin.ext
    have hi : (i : ℕ) < Csr.rowLen O (w : ℕ) := by
      simpa using i.isLt
    have hj : (j : ℕ) < Csr.rowLen O (w : ℕ) := by
      simpa using j.isLt
    have habsI : O (w : ℕ) + (i : ℕ) < O ((w : ℕ) + 1) := by
      simp only [Csr.rowLen] at hi
      omega
    have habsJ : O (w : ℕ) + (j : ℕ) < O ((w : ℕ) + 1) := by
      simp only [Csr.rowLen] at hj
      omega
    have ht : T (O (w : ℕ) + (i : ℕ)) =
        T (O (w : ℕ) + (j : ℕ)) := by
      simpa [rowList, csrRowFun] using hij
    have hs := hcsr.nodup (w : ℕ) w.isLt
      (O (w : ℕ) + (i : ℕ)) (O (w : ℕ) + (j : ℕ))
      (by omega) habsI (by omega) habsJ ht
    omega
  · intro u
    rw [G.adj_comm, hcsr.csr.adj_iff, mem_rowList_iff]
    constructor
    · rintro ⟨q, hq₀, hq₁, hTq⟩
      refine ⟨q - O (w : ℕ), ?_, ?_⟩
      · simp only [Csr.rowLen]
        omega
      · dsimp [csrRowFun]
        rw [show O (w : ℕ) + (q - O (w : ℕ)) = q by omega]
        exact hTq
    · rintro ⟨p, hp, hTp⟩
      refine ⟨O (w : ℕ) + p, by omega, ?_, hTp⟩
      simp only [Csr.rowLen] at hp
      omega

/-- Persistent input of the base provider.  The row buffer is represented by
its length because its contents are deliberately overwritten. -/
structure BaseCsrMem (n nt : ℕ) (o t : String) (O T : ℕ → ℕ)
    (σ : Env) : Prop where
  off_eq : σ.arrs o = arrOf (n + 1) O
  tgt_eq : σ.arrs t = arrOf nt T
  row_length : (σ.arrs "vrow").length = n

theorem baseCsrMem_engineClosed {n nt : ℕ} {o t : String} {O T : ℕ → ℕ}
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames) :
    EngineClosed (BaseCsrMem n nt o t O T) := by
  constructor
  · intro σ a v ha hP
    exact ⟨by simpa using hP.off_eq, by simpa using hP.tgt_eq,
      by simpa using hP.row_length⟩
  · intro σ a i v ha hP
    have hao : a ≠ o := fun h => ho (h ▸ ha)
    have hat : a ≠ t := fun h => ht (h ▸ ha)
    refine ⟨by simpa [Ne.symm hao] using hP.off_eq,
      by simpa [Ne.symm hat] using hP.tgt_eq, ?_⟩
    simpa using (length_arrs_setArr (σ := σ) (a := a) (i := i) (v := v)
      (b := "vrow")).trans hP.row_length

theorem baseCsrMem_engineRunClosed {n nt : ℕ} {o t : String}
    {O T : ℕ → ℕ} (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames) :
    EngineRunClosed (BaseCsrMem n nt o t O T) := by
  intro B K c σ σ' hr hwv hwa hP
  have hoc : o ∉ c.warrs := fun h => ho (hwa o h)
  have htc : t ∉ c.warrs := fun h => ht (hwa t h)
  refine ⟨by rw [hr.frame_arr o hoc]; exact hP.off_eq,
    by rw [hr.frame_arr t htc]; exact hP.tgt_eq, ?_⟩
  rw [Lax3Proofs.RamDriver.run_length_arrs hr "vrow", hP.row_length]

/-! ## Program text -/

def baseRowSlot (t : String) : Com :=
  .seq (.assign "u" (.get t (.var "j")))
    (.seq (.store "vrow" (.var "vtail") (.var "u"))
      (.seq (.assign "vtail" (.add (.var "vtail") (.lit 1)))
        (.assign "j" (.add (.var "j") (.lit 1)))))

def baseProvide (o t : String) : Com :=
  .seq (.assign "vtail" (.lit 0))
    (.seq (Csr.loadRow o "w" "j" "jend")
      (Csr.scan "j" "jend" (baseRowSlot t)))

def baseProvideCost (O : ℕ → ℕ) (w : ℕ) : ℕ :=
  24 * Csr.rowLen O w + 14

/-! ## The row-copy scan -/

/-- State carried while copying one CSR row.  In addition to the provider
and engine frame, it records that the live prefix of `vrow` is precisely the
prefix of the requested CSR row already visited by `j`. -/
structure BaseScanInv (n W nt : ℕ) (o t : String) (O T : ℕ → ℕ)
    (w : ℕ) (E D R ID BH BV BN : ℕ → ℕ) (base : Env)
    (sigma : Env) : Prop where
  mem : BaseCsrMem n nt o t O T sigma
  engine : EngineArrays n W E D R ID BH BV BN sigma
  stable : ProviderStable base sigma
  jend_eq : sigma.vars "jend" = O (w + 1)
  j_lo : O w ≤ sigma.vars "j"
  j_hi : sigma.vars "j" ≤ O (w + 1)
  tail_eq : sigma.vars "vtail" = sigma.vars "j" - O w
  row : ∃ A, sigma.arrs "vrow" = arrOf n A ∧
    ∀ p, p < sigma.vars "vtail" → A p = csrRowFun O T w p

/-- One occupied CSR slot extends the exact copied prefix by one. -/
theorem baseRowSlot_run {B n ns nt W w : ℕ} {G : SimpleGraph (Fin n)}
    {o t : String} {O T E D R ID BH BV BN : ℕ → ℕ} {base sigma : Env}
    (hcsr : CsrSimple G ns O T) (hnsnt : ns ≤ nt) (hB : n + W + 1 < B)
    (hnsB : ns < B) (hw : w < n)
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames)
    (hI : BaseScanInv n W nt o t O T w E D R ID BH BV BN base sigma)
    (hjlt : sigma.vars "j" < O (w + 1)) :
    ∃ sigma' K, Run B (baseRowSlot t) sigma sigma' K ∧
      BaseScanInv n W nt o t O T w E D R ID BH BV BN base sigma' ∧
      sigma'.vars "j" = sigma.vars "j" + 1 ∧ K ≤ 20 := by
  classical
  obtain ⟨hmem, heng, hstable, hjend, hjlo, hjhi, htail, A, hA, hprefix⟩ := hI
  have hendns : O (w + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  have hjns : sigma.vars "j" < ns := lt_of_lt_of_le hjlt hendns
  have hjnt : sigma.vars "j" < nt := lt_of_lt_of_le hjns hnsnt
  have hjB : sigma.vars "j" < B := lt_trans hjns hnsB
  have hTn : T (sigma.vars "j") < n := hcsr.csr.target_lt _ hjns
  have hTB : T (sigma.vars "j") < B := by omega
  have hrow := csrRowRep hcsr ⟨w, hw⟩
  have htailLt : sigma.vars "vtail" < Csr.rowLen O w := by
    simp only [Csr.rowLen]
    omega
  have htailN : sigma.vars "vtail" < n :=
    lt_of_lt_of_le htailLt hrow.tail_le
  have htailB : sigma.vars "vtail" < B := by omega
  have htail1B : sigma.vars "vtail" + 1 < B := by omega
  have hj1B : sigma.vars "j" + 1 < B := by omega
  have hread : (Expr.get t (.var "j")).evalB B sigma =
      some (T (sigma.vars "j")) :=
    evalB_get (evalB_var hjB)
      (by rw [hmem.tgt_eq, getElem?_arrOf T hjnt]) hTB
  let sigma1 := sigma.setVar "u" (T (sigma.vars "j"))
  have r1 : Run B (.assign "u" (.get t (.var "j"))) sigma sigma1 3 :=
    Run.assign hread
  have htailEval1 : (Expr.var "vtail").evalB B sigma1 =
      some (sigma.vars "vtail") := by
    simpa [sigma1] using (evalB_var (B := B) (x := "vtail") (σ := sigma1)
      (by simp [sigma1, htailB]))
  have huEval1 : (Expr.var "u").evalB B sigma1 =
      some (T (sigma.vars "j")) := by
    simpa [sigma1] using (evalB_var (B := B) (x := "u") (σ := sigma1)
      (by simp [sigma1, hTB]))
  have hrowLen1 : sigma1.vars "vtail" < (sigma1.arrs "vrow").length := by
    simp [sigma1, hmem.row_length, htailN]
  let sigma2 := sigma1.setArr "vrow" (sigma.vars "vtail") (T (sigma.vars "j"))
  have r2 : Run B (.store "vrow" (.var "vtail") (.var "u")) sigma1 sigma2 3 :=
    Run.store htailEval1 huEval1 hrowLen1
  have htailEval2 : (Expr.var "vtail").evalB B sigma2 =
      some (sigma.vars "vtail") := by
    simpa [sigma2, sigma1] using (evalB_var (B := B) (x := "vtail") (σ := sigma2)
      (by simp [sigma2, sigma1, htailB]))
  have htailInc : (Expr.add (.var "vtail") (.lit 1)).evalB B sigma2 =
      some (sigma.vars "vtail" + 1) :=
    evalB_bin htailEval2 (evalB_lit (by omega)) (by simpa using htail1B)
  let sigma3 := sigma2.setVar "vtail" (sigma.vars "vtail" + 1)
  have r3 : Run B (.assign "vtail" (.add (.var "vtail") (.lit 1))) sigma2 sigma3 4 :=
    Run.assign htailInc
  have hjEval3 : (Expr.var "j").evalB B sigma3 = some (sigma.vars "j") := by
    simpa [sigma3, sigma2, sigma1] using
      (evalB_var (B := B) (x := "j") (σ := sigma3)
        (by simp [sigma3, sigma2, sigma1, hjB]))
  have hjInc : (Expr.add (.var "j") (.lit 1)).evalB B sigma3 =
      some (sigma.vars "j" + 1) :=
    evalB_bin hjEval3 (evalB_lit (by omega)) (by simpa using hj1B)
  let sigma4 := sigma3.setVar "j" (sigma.vars "j" + 1)
  have r4 : Run B (.assign "j" (.add (.var "j") (.lit 1))) sigma3 sigma4 4 :=
    Run.assign hjInc
  have hrun : Run B (baseRowSlot t) sigma sigma4 14 := r1.seq (r2.seq (r3.seq r4))
  refine ⟨sigma4, 14, hrun, ?_, by simp [sigma4], by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [sigma4, sigma3, sigma2, sigma1, Ne.symm (show "vrow" ≠ o by
        intro h; exact ho (h ▸ by simp [engineArrNames]))] using hmem.off_eq
    · simpa [sigma4, sigma3, sigma2, sigma1, Ne.symm (show "vrow" ≠ t by
        intro h; exact ht (h ▸ by simp [engineArrNames]))] using hmem.tgt_eq
    · simpa [sigma4, sigma3, sigma2, sigma1] using
        (length_arrs_setArr (σ := sigma1) (a := "vrow")
          (i := sigma.vars "vtail") (v := T (sigma.vars "j")) (b := "vrow")).trans
          (by simpa [sigma1] using hmem.row_length)
  · refine ⟨by simp [sigma4, sigma3, sigma2, sigma1, heng.n_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, heng.elm_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, heng.deg_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, heng.rank_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, heng.idg_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, heng.head_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, heng.val_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, heng.next_eq]⟩
  · refine ⟨by simp [sigma4, sigma3, sigma2, sigma1, hstable.n_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, hstable.w_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, hstable.i_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, hstable.sp_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, hstable.ls_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, hstable.cnt_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, hstable.mind_eq],
      by simp [sigma4, sigma3, sigma2, sigma1, hstable.kmax_eq]⟩
  · simpa [sigma4, sigma3, sigma2, sigma1] using hjend
  · simp [sigma4]; omega
  · simp [sigma4]; omega
  · simp [sigma4, sigma3, sigma2, sigma1]; omega
  · refine ⟨upd A (sigma.vars "vtail") (T (sigma.vars "j")), ?_, ?_⟩
    · simp [sigma4, sigma3, sigma2, sigma1, hA, set_arrOf_eq_upd]
    · intro p hp
      simp [sigma4, sigma3, sigma2, sigma1] at hp
      by_cases hpeq : p = sigma.vars "vtail"
      · rw [hpeq, upd_self]
        dsimp [csrRowFun]
        congr 1
        omega
      · rw [upd_of_ne _ hpeq]
        exact hprefix p (by omega)

/-- Copy the complete requested row into the reusable carrier buffer. -/
theorem baseScan_spec {B n ns nt W w : ℕ} {G : SimpleGraph (Fin n)}
    {o t : String} {O T E D R ID BH BV BN : ℕ → ℕ} {base : Env}
    (hcsr : CsrSimple G ns O T) (hnsnt : ns ≤ nt) (hB : n + W + 1 < B)
    (hnsB : ns < B) (hw : w < n)
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames) :
    Spec B
      (fun sigma => BaseScanInv n W nt o t O T w E D R ID BH BV BN base sigma ∧
        sigma.vars "j" = O w)
      (Csr.scan "j" "jend" (baseRowSlot t))
      (fun _ sigma' => BaseScanInv n W nt o t O T w E D R ID BH BV BN base sigma' ∧
        sigma'.vars "j" = O (w + 1))
      (24 * Csr.rowLen O w + 4) := by
  have hend : O (w + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  refine Csr.rowScan_spec B (24 * Csr.rowLen O w + 4) (O (w + 1)) 20
    "j" "jend" (baseRowSlot t)
    (BaseScanInv n W nt o t O T w E D R ID BH BV BN base)
    (by omega) (fun sigma hI => ⟨hI.jend_eq, hI.j_hi⟩)
    (fun sigma hI hlt => ?_) (fun _ h => h.1) (fun sigma h => ?_)
  · obtain ⟨sigma', K, hr, hI', hj, hK⟩ :=
      baseRowSlot_run hcsr hnsnt hB hnsB hw ho ht hI hlt
    exact ⟨sigma', K, hr, hI', hj, hK⟩
  · rw [h.2]
    simp only [Csr.rowLen]
    omega

/-! ## Provider contract -/

/-- The resident input CSR supplies exact rows to the virtual elimination
engine.  Its only mutable storage is the carrier-sized `vrow` buffer. -/
theorem baseProvidesRows {B n ns nt W : ℕ} {G : SimpleGraph (Fin n)}
    {o t : String} {O T : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) (hnsnt : ns ≤ nt)
    (hB : n + W + 1 < B) (hnsB : ns < B)
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames) :
    ProvidesRows B n W G (BaseCsrMem n nt o t O T)
      (baseProvide o t) (baseProvideCost O) := by
  classical
  intro w E D R ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  let sigma1 := sigma.setVar "vtail" 0
  have r1 : Run B (.assign "vtail" (.lit 0)) sigma sigma1 2 :=
    Run.assign (evalB_lit (by omega))
  have hmem1 : BaseCsrMem n nt o t O T sigma1 := by
    exact ⟨by simpa [sigma1] using hmem.off_eq,
      by simpa [sigma1] using hmem.tgt_eq,
      by simpa [sigma1] using hmem.row_length⟩
  have heng1 : EngineArrays n W E D R ID BH BV BN sigma1 := by
    exact ⟨by simpa [sigma1] using heng.n_eq,
      by simpa [sigma1] using heng.elm_eq,
      by simpa [sigma1] using heng.deg_eq,
      by simpa [sigma1] using heng.rank_eq,
      by simpa [sigma1] using heng.idg_eq,
      by simpa [sigma1] using heng.head_eq,
      by simpa [sigma1] using heng.val_eq,
      by simpa [sigma1] using heng.next_eq⟩
  have hcsrW1 : CsrWide.CsrW o t n ns nt n O T sigma1 :=
    ⟨hmem1.off_eq, hmem1.tgt_eq, fun i hi => hcsr.csr.mono i hi,
      hcsr.csr.last, hnsnt, fun p hp => hcsr.csr.target_lt p hp⟩
  have hloadPre : CsrWide.RowPreW o t "w" n ns nt n B O T sigma1 := by
    refine ⟨⟨hcsrW1, by omega, hnsB⟩, ?_, ?_⟩
    · simpa [sigma1, hw] using w.isLt
    · simp [sigma1, hw]
      omega
  obtain ⟨sigma2, r2, hload⟩ :=
    (CsrWide.loadRow_spec B n ns nt n o t "w" "j" "jend" O T
      (by decide) (by decide)).run hloadPre
  obtain ⟨hcsrW2, hj2, hjend2, hsigma2⟩ := hload
  have hj2' : sigma2.vars "j" = O (w : ℕ) := by
    rw [hj2]
    simp [sigma1, hw]
  have hjend2' : sigma2.vars "jend" = O ((w : ℕ) + 1) := by
    rw [hjend2]
    simp [sigma1, hw]
  have hmem2 : BaseCsrMem n nt o t O T sigma2 := by
    exact ⟨hcsrW2.offArr, hcsrW2.tgtArr,
      by simpa [hsigma2, sigma1] using hmem.row_length⟩
  have heng2 : EngineArrays n W E D R ID BH BV BN sigma2 := by
    exact ⟨by simpa [hsigma2, sigma1] using heng.n_eq,
      by simpa [hsigma2, sigma1] using heng.elm_eq,
      by simpa [hsigma2, sigma1] using heng.deg_eq,
      by simpa [hsigma2, sigma1] using heng.rank_eq,
      by simpa [hsigma2, sigma1] using heng.idg_eq,
      by simpa [hsigma2, sigma1] using heng.head_eq,
      by simpa [hsigma2, sigma1] using heng.val_eq,
      by simpa [hsigma2, sigma1] using heng.next_eq⟩
  have hstable2 : ProviderStable sigma sigma2 := by
    exact ⟨by simp [hsigma2, sigma1], by simp [hsigma2, sigma1],
      by simp [hsigma2, sigma1], by simp [hsigma2, sigma1],
      by simp [hsigma2, sigma1], by simp [hsigma2, sigma1],
      by simp [hsigma2, sigma1], by simp [hsigma2, sigma1]⟩
  obtain ⟨A0, hA0⟩ := Lax3Proofs.RamDriver.exists_arrOf hmem2.row_length
  have hmono : O (w : ℕ) ≤ O ((w : ℕ) + 1) :=
    hcsr.csr.mono (w : ℕ) w.isLt
  have hI2 : BaseScanInv n W nt o t O T (w : ℕ) E D R ID BH BV BN sigma sigma2 := by
    refine ⟨hmem2, heng2, hstable2, hjend2', by rw [hj2'],
      by rw [hj2']; exact hmono, ?_, A0, hA0, ?_⟩
    · rw [hj2']
      simp [hsigma2, sigma1]
    · intro p hp
      simp [hsigma2, sigma1] at hp
  obtain ⟨sigma3, r3, hI3, hj3⟩ :=
    (baseScan_spec (base := sigma) hcsr hnsnt hB hnsB w.isLt ho ht).run
      ⟨hI2, hj2'⟩
  obtain ⟨hmem3, heng3, hstable3, -, -, -, htail3, A, hA, hprefix⟩ := hI3
  have htail : sigma3.vars "vtail" = Csr.rowLen O (w : ℕ) := by
    rw [htail3, hj3]
    rfl
  have hrow : RowRep G w (Csr.rowLen O (w : ℕ)) A := by
    apply (csrRowRep hcsr w).congr_prefix
    intro p hp
    exact hprefix p (by rw [htail]; exact hp)
  refine ⟨sigma3, baseProvideCost O (w : ℕ), ?_, le_rfl,
    hmem3, heng3, hstable3, Csr.rowLen O (w : ℕ), A, hrow, htail, hA⟩
  rw [show baseProvideCost O (w : ℕ) =
      2 + (8 + (24 * Csr.rowLen O (w : ℕ) + 4)) by
    simp only [baseProvideCost]
    omega]
  simpa only [baseProvide] using r1.seq (r2.seq r3)

/-! ## Axiom audit -/

#print axioms csrRowRep
#print axioms baseRowSlot_run
#print axioms baseScan_spec
#print axioms baseProvidesRows

end Lax3Proofs.Refine.OrderVirtualBaseProvider
