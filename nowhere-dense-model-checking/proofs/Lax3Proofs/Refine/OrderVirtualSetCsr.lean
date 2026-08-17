import Lax3Proofs.Refine.OrderVirtualSetRow

/-!
# Exact finite-set rows stored as a compact block structure

The virtual provider cache stores only selected incoming rows.  This module
reuses the verified CSR row copier for an arbitrary family of exact finite
sets; unlike `CsrSimple`, the rows need not form an undirected graph.
-/

namespace Lax3Proofs.Refine.OrderVirtualSetCsr

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.OrderVirtualBaseProvider

/-- A compact block structure whose row `w` represents exactly `S w`.
`bounded` contains precisely the machine-address facts used by the shared
copy loop. -/
structure SetCsrRows {n : ℕ} (S : Fin n → Finset (Fin n))
    (ns : ℕ) (O T : ℕ → ℕ) : Prop where
  bounded : BoundedCsr n ns O T
  last : O n = ns
  row : ∀ w : Fin n,
    SetRowRep (S w) (Csr.rowLen O (w : ℕ))
      (csrRowFun O T (w : ℕ))

/-- The generic CSR copier exposed at the exact-set provider surface. -/
theorem setCsrProvidesSetRows {B n ns nt W : ℕ}
    {S : Fin n → Finset (Fin n)} {o t : String} {O T : ℕ → ℕ}
    (hrows : SetCsrRows S ns O T) (hnsnt : ns ≤ nt)
    (hB : n + W + 1 < B) (hnsB : ns < B)
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames) :
    ProvidesSetRows B n W S (BaseCsrMem n nt o t O T) "vrow"
      (baseProvide o t) (baseProvideCost O) := by
  classical
  intro w E D R ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  let sigma1 := sigma.setVar "vtail" 0
  have r1 : Run B (.assign "vtail" (.lit 0)) sigma sigma1 2 :=
    Run.assign (evalB_lit (by omega))
  have hmem1 : BaseCsrMem n nt o t O T sigma1 :=
    ⟨by simpa [sigma1] using hmem.off_eq,
      by simpa [sigma1] using hmem.tgt_eq,
      by simpa [sigma1] using hmem.row_length⟩
  have heng1 : EngineArrays n W E D R ID BH BV BN sigma1 :=
    ⟨by simpa [sigma1] using heng.n_eq,
      by simpa [sigma1] using heng.elm_eq,
      by simpa [sigma1] using heng.deg_eq,
      by simpa [sigma1] using heng.rank_eq,
      by simpa [sigma1] using heng.idg_eq,
      by simpa [sigma1] using heng.head_eq,
      by simpa [sigma1] using heng.val_eq,
      by simpa [sigma1] using heng.next_eq⟩
  have hcsrW1 : CsrWide.CsrW o t n ns nt n O T sigma1 :=
    ⟨hmem1.off_eq, hmem1.tgt_eq, hrows.bounded.mono, hrows.last,
      hnsnt, hrows.bounded.target_lt⟩
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
  have hmem2 : BaseCsrMem n nt o t O T sigma2 :=
    ⟨hcsrW2.offArr, hcsrW2.tgtArr,
      by simpa [hsigma2, sigma1] using hmem.row_length⟩
  have heng2 : EngineArrays n W E D R ID BH BV BN sigma2 :=
    ⟨by simpa [hsigma2, sigma1] using heng.n_eq,
      by simpa [hsigma2, sigma1] using heng.elm_eq,
      by simpa [hsigma2, sigma1] using heng.deg_eq,
      by simpa [hsigma2, sigma1] using heng.rank_eq,
      by simpa [hsigma2, sigma1] using heng.idg_eq,
      by simpa [hsigma2, sigma1] using heng.head_eq,
      by simpa [hsigma2, sigma1] using heng.val_eq,
      by simpa [hsigma2, sigma1] using heng.next_eq⟩
  have hstable2 : ProviderStable sigma sigma2 :=
    ⟨by simp [hsigma2, sigma1], by simp [hsigma2, sigma1],
      by simp [hsigma2, sigma1], by simp [hsigma2, sigma1],
      by simp [hsigma2, sigma1], by simp [hsigma2, sigma1],
      by simp [hsigma2, sigma1], by simp [hsigma2, sigma1]⟩
  obtain ⟨A0, hA0⟩ := Lax3Proofs.RamDriver.exists_arrOf hmem2.row_length
  have hmono : O (w : ℕ) ≤ O ((w : ℕ) + 1) :=
    hrows.bounded.mono (w : ℕ) w.isLt
  have hI2 : BaseScanInv n W nt o t O T (w : ℕ)
      E D R ID BH BV BN sigma sigma2 := by
    refine ⟨hmem2, heng2, hstable2, hjend2', by rw [hj2'],
      by rw [hj2']; exact hmono, ?_, A0, hA0, ?_⟩
    · rw [hj2']
      simp [hsigma2, sigma1]
    · intro p hp
      simp [hsigma2, sigma1] at hp
  obtain ⟨sigma3, r3, hI3, hj3⟩ :=
    (baseScan_spec (base := sigma) hrows.bounded hnsnt hB hnsB
      w.isLt ho ht).run ⟨hI2, hj2'⟩
  obtain ⟨hmem3, heng3, hstable3, -, -, -, htail3, A, hA, hprefix⟩ := hI3
  have htail : sigma3.vars "vtail" = Csr.rowLen O (w : ℕ) := by
    rw [htail3, hj3]
    rfl
  have hrow : SetRowRep (S w) (Csr.rowLen O (w : ℕ)) A := by
    apply (hrows.row w).congr_prefix
    intro p hp
    exact hprefix p (by rw [htail]; exact hp)
  refine ⟨sigma3, baseProvideCost O (w : ℕ), ?_, le_rfl,
    hmem3, heng3, hstable3, Csr.rowLen O (w : ℕ), A,
    hrow, htail, hA⟩
  rw [show baseProvideCost O (w : ℕ) =
      2 + (8 + (24 * Csr.rowLen O (w : ℕ) + 4)) by
    simp only [baseProvideCost]
    omega]
  simpa only [baseProvide] using r1.seq (r2.seq r3)

/-! ## Axiom audit -/

#print axioms setCsrProvidesSetRows

end Lax3Proofs.Refine.OrderVirtualSetCsr
