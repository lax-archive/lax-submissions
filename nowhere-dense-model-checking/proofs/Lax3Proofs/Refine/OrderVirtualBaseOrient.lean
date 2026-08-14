import Lax3Proofs.Refine.OrderVirtualSetRow

/-!
# Virtual rows of the base elimination orientation

The input graph remains in its original CSR.  Given a saved elimination
rank, one scan of a requested CSR row filters it into either the incoming or
the outgoing row of the induced orientation.  Only the requested row is
materialized, in a carrier-sized reusable buffer.
-/

namespace Lax3Proofs.Refine.OrderVirtualBaseOrient

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamElim (CsrSimple ElimCert)
open Lax3Proofs.RamAugment (outSet mem_outSet)
open Lax3Proofs.RamDriverAugment
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualBaseProvider
open Lax3Proofs.Refine.OrderVirtualSetRow

inductive RankDir where
  | incoming
  | outgoing
  deriving DecidableEq

def RankDir.keep (dir : RankDir) (R : ℕ → ℕ) (w z : ℕ) : Prop :=
  match dir with
  | .incoming => R z < R w
  | .outgoing => R w < R z

instance (dir : RankDir) (R : ℕ → ℕ) (w z : ℕ) :
    Decidable (dir.keep R w z) := by
  cases dir <;> simp only [RankDir.keep] <;> infer_instance

def rankFilterSet (dir : RankDir) (R : ℕ → ℕ) (w : ℕ)
    (S : Finset ℕ) : Finset ℕ :=
  S.filter (dir.keep R w)

@[simp] theorem rankFilterSet_empty (dir : RankDir) (R : ℕ → ℕ) (w : ℕ) :
    rankFilterSet dir R w ∅ = ∅ := by
  simp [rankFilterSet]

theorem rankFilterSet_insert {dir : RankDir} {R : ℕ → ℕ} {w z : ℕ}
    {S : Finset ℕ} (hz : dir.keep R w z) :
    rankFilterSet dir R w (insert z S) = insert z (rankFilterSet dir R w S) := by
  rw [rankFilterSet, Finset.filter_insert]
  simp only [hz, ↓reduceIte, rankFilterSet]

theorem rankFilterSet_insert_of_not {dir : RankDir} {R : ℕ → ℕ} {w z : ℕ}
    {S : Finset ℕ} (hz : ¬ dir.keep R w z) :
    rankFilterSet dir R w (insert z S) = rankFilterSet dir R w S := by
  rw [rankFilterSet, Finset.filter_insert]
  simp only [hz, ↓reduceIte, rankFilterSet]

/-- The raw CSR slots already visited are `S`; the output buffer contains
exactly those members of `S` selected by the rank comparison. -/
def RankFilterAcc (dst rk : String) (n : ℕ) (dir : RankDir) (R : ℕ → ℕ)
    (w : ℕ) (S : Finset ℕ) (tau : Env) : Prop :=
  S ⊆ Finset.range n ∧
    RowFillAcc dst n (rankFilterSet dir R w (Finset.range n))
      (rankFilterSet dir R w S) tau ∧
    tau.arrs rk = arrOf n R ∧ tau.vars "w" = w

namespace RankFilterAcc

theorem setVar {dst : String} {n : ℕ} {dir : RankDir} {R : ℕ → ℕ}
    {rk : String} {w : ℕ} {S : Finset ℕ} {tau : Env}
    (h : RankFilterAcc dst rk n dir R w S tau) {y : String}
    (hy : y ≠ "c") (hyw : y ≠ "w") (x : ℕ) :
    RankFilterAcc dst rk n dir R w S (tau.setVar y x) :=
  ⟨h.1, h.2.1.setVar hy x, by simpa using h.2.2.1,
    by rw [vars_setVar, if_neg (Ne.symm hyw)]; exact h.2.2.2⟩

theorem setArr_of_ne {dst a : String} {n : ℕ} {dir : RankDir}
    {rk : String} {R : ℕ → ℕ} {w : ℕ} {S : Finset ℕ} {tau : Env}
    (h : RankFilterAcc dst rk n dir R w S tau)
    (ha : a ≠ dst) (har : a ≠ rk) (p x : ℕ) :
    RankFilterAcc dst rk n dir R w S (tau.setArr a p x) :=
  ⟨h.1, h.2.1.setArr_of_ne ha p x,
    by rw [arrs_setArr, if_neg (Ne.symm har)]; exact h.2.2.1,
    by simpa using h.2.2.2⟩

end RankFilterAcc

def rankCond (dir : RankDir) (rk : String) : Cond :=
  match dir with
  | .incoming => .lt (.get rk (.var "u")) (.get rk (.var "w"))
  | .outgoing => .lt (.get rk (.var "w")) (.get rk (.var "u"))

def rankFilterAct (dir : RankDir) (rk dst : String) : Com :=
  .ite (rankCond dir rk) (rowFillAct dst) .skip

theorem rankCond_eval {B n w z : ℕ} {dir : RankDir} {rk : String}
    {R : ℕ → ℕ} {tau : Env}
    (hnB : n < B) (hw : w < n) (hz : z < n)
    (hR : ∀ v, v < n → R v < n)
    (hrk : tau.arrs rk = arrOf n R)
    (hvw : tau.vars "w" = w) (hvu : tau.vars "u" = z) :
    (rankCond dir rk).evalB B tau = some (decide (dir.keep R w z)) := by
  have ew : (Expr.var "w").evalB B tau = some w := by
    have h := evalB_var (B := B) (x := "w") (σ := tau) (by rw [hvw]; omega)
    rwa [hvw] at h
  have eu : (Expr.var "u").evalB B tau = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := tau) (by rw [hvu]; omega)
    rwa [hvu] at h
  have erw : (Expr.get rk (.var "w")).evalB B tau = some (R w) :=
    evalB_get ew (by rw [hrk, getElem?_arrOf R hw]) (by have := hR w hw; omega)
  have erz : (Expr.get rk (.var "u")).evalB B tau = some (R z) :=
    evalB_get eu (by rw [hrk, getElem?_arrOf R hz]) (by have := hR z hz; omega)
  cases dir with
  | incoming => exact evalB_condLt erz erw
  | outgoing => exact evalB_condLt erw erz

/-- Filtering a fresh raw CSR target either appends it to the exact output
or leaves the output unchanged. -/
theorem rankFilterAcc_emits {B n w : ℕ} {dir : RankDir} {rk dst : String}
    {R : ℕ → ℕ}
    (hnB : n < B) (hw : w < n) (hR : ∀ v, v < n → R v < n)
    (hrd : rk ≠ dst) (hra : rk ≠ "@") :
    Emits B n 15 dst "@" (rankFilterAct dir rk dst) (Finset.range n)
      (RankFilterAcc dst rk n dir R w) := by
  classical
  rintro S tau z hA hu hzn hzS hzCap
  have ec := rankCond_eval (dir := dir) hnB hw hzn hR hA.2.2.1 hA.2.2.2 hu
  by_cases hk : dir.keep R w z
  · have hzFilt : z ∈ rankFilterSet dir R w (Finset.range n) := by
      simp [rankFilterSet, hk, hzn]
    have hzOld : z ∉ rankFilterSet dir R w S := by
      intro h
      exact hzS (Finset.mem_filter.1 h).1
    obtain ⟨tau', K, hr, hK, hfill, hfv, hfa⟩ :=
      rowFillAcc_emits (dst := dst) (Cap := rankFilterSet dir R w (Finset.range n))
        hnB (by intro z hz; exact (Finset.mem_filter.1 hz).1)
        (rankFilterSet dir R w S) tau z hA.2.1 hu hzn hzOld hzFilt
    refine ⟨tau', 1 + (rankCond dir rk).size + K, ?_, ?_, ?_, hfv, hfa⟩
    · simpa only [rankFilterAct] using Run.ite_true (by rw [ec]; simp [hk]) hr
    · cases dir <;> simp [rankCond, Cond.size, Expr.size] <;> omega
    refine ⟨Finset.insert_subset hzCap hA.1, ?_, ?_, ?_⟩
    · rw [rankFilterSet_insert hk]
      exact hfill
    · rw [hfa rk hrd hra]
      exact hA.2.2.1
    · rw [hfv "w" (by decide)]
      exact hA.2.2.2
  · refine ⟨tau, 1 + (rankCond dir rk).size + 1, ?_, ?_,
      ?_, fun _ _ => rfl, fun _ _ _ => rfl⟩
    · simpa only [rankFilterAct] using Run.ite_false (by rw [ec]; simp [hk]) Run.skip
    · cases dir <;> simp [rankCond, Cond.size, Expr.size] <;> omega
    refine ⟨Finset.insert_subset hzCap hA.1, ?_, hA.2.2.1, hA.2.2.2⟩
    rw [rankFilterSet_insert_of_not hk]
    exact hA.2.1

/-! ## The filtered set is the orientation row -/

def orientSet (dir : RankDir) {n : ℕ} (D : Orientation n) (w : Fin n) :
    Finset (Fin n) :=
  match dir with
  | .incoming => D.inN w
  | .outgoing => outSet D w

/-- A raw row of the simple input CSR is the numeric image of the graph
neighbourhood. -/
theorem baseRowTgt_eq {n ns : ℕ} {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    (hcsr : CsrSimple G ns O T) {w : ℕ} (hw : w < n) :
    rowTgt O T w = valSet (nbrsIn G Finset.univ ⟨w, hw⟩) := by
  classical
  ext z
  rw [mem_rowTgt, mem_valSet]
  constructor
  · rintro ⟨p, hp₀, hp₁, hpT⟩
    have hpn : p < ns := lt_of_lt_of_le hp₁ (hcsr.csr.le_ns (by omega))
    have hzn : z < n := hpT ▸ hcsr.csr.target_lt p hpn
    refine ⟨hzn, mem_nbrsIn.2 ⟨by simp, ?_⟩⟩
    have hadj := (hcsr.csr.adj_iff
      ⟨w, hw⟩ ⟨T p, hcsr.csr.target_lt p hpn⟩).2 ⟨p, hp₀, hp₁, rfl⟩
    have he : (⟨T p, hcsr.csr.target_lt p hpn⟩ : Fin n) = ⟨z, hzn⟩ :=
      Fin.ext hpT
    rw [← he]
    exact hadj.symm
  · rintro ⟨hzn, hz⟩
    have hadj : G.Adj ⟨w, hw⟩ ⟨z, hzn⟩ := (mem_nbrsIn.1 hz).2.symm
    obtain ⟨p, hp₀, hp₁, hpT⟩ :=
      (hcsr.csr.adj_iff ⟨w, hw⟩ ⟨z, hzn⟩).1 hadj
    exact ⟨p, hp₀, hp₁, hpT⟩

/-- Filtering that raw row by the saved rank gives either exact row of the
base elimination orientation. -/
theorem rankFilterSet_base_eq {n ns : ℕ} {G : SimpleGraph (Fin n)}
    {O T R : ℕ → ℕ} {rho : Fin n → ℕ} (dir : RankDir)
    (hcsr : CsrSimple G ns O T) (hrho : ∀ v : Fin n, rho v = R (v : ℕ))
    {w : ℕ} (hw : w < n) :
    rankFilterSet dir R w (rowTgt O T w) =
      valSet (orientSet dir (ElimCert.elimOr G rho) ⟨w, hw⟩) := by
  classical
  rw [baseRowTgt_eq hcsr hw]
  ext z
  cases dir with
  | incoming =>
      simp only [rankFilterSet, Finset.mem_filter, mem_valSet, orientSet,
        ElimCert.mem_elimOr, RankDir.keep]
      constructor
      · rintro ⟨⟨hzn, hz⟩, hlt⟩
        refine ⟨hzn, ?_⟩
        rw [hrho ⟨z, hzn⟩, hrho ⟨w, hw⟩]
        exact ⟨(mem_nbrsIn.1 hz).2, hlt⟩
      · rintro ⟨hzn, hadj, hlt⟩
        refine ⟨⟨hzn, mem_nbrsIn.2 ⟨by simp, hadj⟩⟩, ?_⟩
        rwa [hrho ⟨z, hzn⟩, hrho ⟨w, hw⟩] at hlt
  | outgoing =>
      simp only [rankFilterSet, Finset.mem_filter, mem_valSet, orientSet,
        mem_outSet, ElimCert.mem_elimOr, RankDir.keep]
      constructor
      · rintro ⟨⟨hzn, hz⟩, hlt⟩
        refine ⟨hzn, ?_⟩
        rw [hrho ⟨w, hw⟩, hrho ⟨z, hzn⟩]
        exact ⟨(mem_nbrsIn.1 hz).2.symm, hlt⟩
      · rintro ⟨hzn, hadj, hlt⟩
        refine ⟨⟨hzn, mem_nbrsIn.2 ⟨by simp, hadj.symm⟩⟩, ?_⟩
        rwa [hrho ⟨w, hw⟩, hrho ⟨z, hzn⟩] at hlt

/-! ## Persistent memory and frame lemmas -/

structure BaseOrientInput (n nt : ℕ) (o t rk : String)
    (O T R : ℕ → ℕ) (sigma : Env) : Prop where
  off_eq : sigma.arrs o = arrOf (n + 1) O
  tgt_eq : sigma.arrs t = arrOf nt T
  rank_eq : sigma.arrs rk = arrOf n R

structure BaseOrientMem (n nt : ℕ) (o t rk dst : String)
    (O T R : ℕ → ℕ) (sigma : Env) : Prop where
  input : BaseOrientInput n nt o t rk O T R sigma
  dst_length : (sigma.arrs dst).length = n

namespace BaseOrientInput

theorem setVar {n nt : ℕ} {o t rk : String} {O T R : ℕ → ℕ}
    {sigma : Env} (h : BaseOrientInput n nt o t rk O T R sigma)
    (y : String) (x : ℕ) :
    BaseOrientInput n nt o t rk O T R (sigma.setVar y x) :=
  ⟨by simpa using h.off_eq, by simpa using h.tgt_eq, by simpa using h.rank_eq⟩

theorem of_emit_frame {n nt : ℕ} {o t rk dst : String}
    {O T R : ℕ → ℕ} {sigma sigma' : Env}
    (h : BaseOrientInput n nt o t rk O T R sigma)
    (hod : o ≠ dst) (hoa : o ≠ "@")
    (htd : t ≠ dst) (hta : t ≠ "@")
    (hrd : rk ≠ dst) (hra : rk ≠ "@")
    (hfa : ∀ a, a ≠ dst → a ≠ "@" → sigma'.arrs a = sigma.arrs a) :
    BaseOrientInput n nt o t rk O T R sigma' :=
  ⟨by rw [hfa o hod hoa]; exact h.off_eq,
    by rw [hfa t htd hta]; exact h.tgt_eq,
    by rw [hfa rk hrd hra]; exact h.rank_eq⟩

end BaseOrientInput

namespace EngineArrays

/-- An emitting action whose private arrays are outside the engine preserves
all virtual-elimination arrays. -/
theorem of_emit_frame {n W : ℕ} {E D R ID BH BV BN : ℕ → ℕ}
    {dst : String} {sigma sigma' : Env}
    (h : EngineArrays n W E D R ID BH BV BN sigma)
    (hdst : dst ∉ engineArrNames)
    (hfv : ∀ y, y ≠ "c" → sigma'.vars y = sigma.vars y)
    (hfa : ∀ a, a ≠ dst → a ≠ "@" → sigma'.arrs a = sigma.arrs a) :
    EngineArrays n W E D R ID BH BV BN sigma' := by
  have hne : ∀ a ∈ engineArrNames, a ≠ dst := by
    intro a ha had
    exact hdst (had ▸ ha)
  exact ⟨by rw [hfv "n" (by decide)]; exact h.n_eq,
    by rw [hfa "elm" (hne "elm" (by simp [engineArrNames])) (by decide)]; exact h.elm_eq,
    by rw [hfa "deg" (hne "deg" (by simp [engineArrNames])) (by decide)]; exact h.deg_eq,
    by rw [hfa "rnk" (hne "rnk" (by simp [engineArrNames])) (by decide)]; exact h.rank_eq,
    by rw [hfa "idg" (hne "idg" (by simp [engineArrNames])) (by decide)]; exact h.idg_eq,
    by rw [hfa "bh" (hne "bh" (by simp [engineArrNames])) (by decide)]; exact h.head_eq,
    by rw [hfa "bv" (hne "bv" (by simp [engineArrNames])) (by decide)]; exact h.val_eq,
    by rw [hfa "bn" (hne "bn" (by simp [engineArrNames])) (by decide)]; exact h.next_eq⟩

end EngineArrays

namespace ProviderStable

theorem setVar_of_private {base sigma : Env} (h : ProviderStable base sigma)
    {y : String}
    (hn : y ≠ "n") (hw : y ≠ "w") (hi : y ≠ "i")
    (hsp : y ≠ "sp") (hls : y ≠ "ls") (hcnt : y ≠ "cnt")
    (hmind : y ≠ "mind") (hkmax : y ≠ "kmax") (x : ℕ) :
    ProviderStable base (sigma.setVar y x) :=
  ⟨by rw [vars_setVar, if_neg (Ne.symm hn)]; exact h.n_eq,
    by rw [vars_setVar, if_neg (Ne.symm hw)]; exact h.w_eq,
    by rw [vars_setVar, if_neg (Ne.symm hi)]; exact h.i_eq,
    by rw [vars_setVar, if_neg (Ne.symm hsp)]; exact h.sp_eq,
    by rw [vars_setVar, if_neg (Ne.symm hls)]; exact h.ls_eq,
    by rw [vars_setVar, if_neg (Ne.symm hcnt)]; exact h.cnt_eq,
    by rw [vars_setVar, if_neg (Ne.symm hmind)]; exact h.mind_eq,
    by rw [vars_setVar, if_neg (Ne.symm hkmax)]; exact h.kmax_eq⟩

theorem of_emit_frame {base sigma sigma' : Env}
    (h : ProviderStable base sigma)
    (hfv : ∀ y, y ≠ "c" → sigma'.vars y = sigma.vars y) :
    ProviderStable base sigma' :=
  ⟨by rw [hfv "n" (by decide)]; exact h.n_eq,
    by rw [hfv "w" (by decide)]; exact h.w_eq,
    by rw [hfv "i" (by decide)]; exact h.i_eq,
    by rw [hfv "sp" (by decide)]; exact h.sp_eq,
    by rw [hfv "ls" (by decide)]; exact h.ls_eq,
    by rw [hfv "cnt" (by decide)]; exact h.cnt_eq,
    by rw [hfv "mind" (by decide)]; exact h.mind_eq,
    by rw [hfv "kmax" (by decide)]; exact h.kmax_eq⟩

end ProviderStable

theorem baseOrientMem_engineClosed {n nt : ℕ} {o t rk dst : String}
    {O T R : ℕ → ℕ}
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames)
    (hrk : rk ∉ engineArrNames) (hdst : dst ∉ engineArrNames) :
    EngineClosed (BaseOrientMem n nt o t rk dst O T R) := by
  constructor
  · intro sigma a v ha hP
    exact ⟨hP.input.setVar a v, by simpa using hP.dst_length⟩
  · intro sigma a i v ha hP
    have hao : a ≠ o := fun h => ho (h ▸ ha)
    have hat : a ≠ t := fun h => ht (h ▸ ha)
    have har : a ≠ rk := fun h => hrk (h ▸ ha)
    have had : a ≠ dst := fun h => hdst (h ▸ ha)
    refine ⟨⟨by rw [arrs_setArr, if_neg (Ne.symm hao)]; exact hP.input.off_eq,
      by rw [arrs_setArr, if_neg (Ne.symm hat)]; exact hP.input.tgt_eq,
      by rw [arrs_setArr, if_neg (Ne.symm har)]; exact hP.input.rank_eq⟩, ?_⟩
    rw [arrs_setArr, if_neg (Ne.symm had)]
    exact hP.dst_length

theorem baseOrientMem_engineRunClosed {n nt : ℕ} {o t rk dst : String}
    {O T R : ℕ → ℕ}
    (ho : o ∉ engineArrNames) (ht : t ∉ engineArrNames)
    (hrk : rk ∉ engineArrNames) (hdst : dst ∉ engineArrNames) :
    EngineRunClosed (BaseOrientMem n nt o t rk dst O T R) := by
  intro B K c sigma sigma' hrun hwv hwa hP
  have hoc : o ∉ c.warrs := fun h => ho (hwa o h)
  have htc : t ∉ c.warrs := fun h => ht (hwa t h)
  have hrc : rk ∉ c.warrs := fun h => hrk (hwa rk h)
  refine ⟨⟨by rw [hrun.frame_arr o hoc]; exact hP.input.off_eq,
    by rw [hrun.frame_arr t htc]; exact hP.input.tgt_eq,
    by rw [hrun.frame_arr rk hrc]; exact hP.input.rank_eq⟩, ?_⟩
  rw [Lax3Proofs.RamDriver.run_length_arrs hrun dst, hP.dst_length]

/-! ## Executable provider -/

def baseOrientProvide (dir : RankDir) (o t rk dst : String) : Com :=
  .seq (.assign "c" (.lit 0))
    (.seq (Lax3Proofs.RamAugment.blockScan o t "w" "oj" "ojend" "u"
      (rankFilterAct dir rk dst))
      (.assign "vtail" (.var "c")))

def baseOrientCost (O : ℕ → ℕ) (w : ℕ) : ℕ :=
  26 * Csr.rowLen O w + 16

/-- The original CSR and a saved rank supply either exact row of the base
orientation, in one scan of the original undirected row. -/
theorem baseOrientProvidesSetRows {B n ns nt W : ℕ}
    {G : SimpleGraph (Fin n)} {O T R : ℕ → ℕ} {rho : Fin n → ℕ}
    {o t rk dst : String} (dir : RankDir)
    (hcsr : CsrSimple G ns O T) (hnsnt : ns ≤ nt)
    (hrho : ∀ v : Fin n, rho v = R (v : ℕ))
    (hR : ∀ v, v < n → R v < n)
    (hnB : n < B) (hnsB : ns < B)
    (hod : o ≠ dst) (hoa : o ≠ "@")
    (htd : t ≠ dst) (hta : t ≠ "@")
    (hrd : rk ≠ dst) (hra : rk ≠ "@")
    (hdst : dst ∉ engineArrNames) :
    ProvidesSetRows B n W
      (fun w => orientSet dir (ElimCert.elimOr G rho) w)
      (BaseOrientMem n nt o t rk dst O T R) dst
      (baseOrientProvide dir o t rk dst) (baseOrientCost O) := by
  classical
  intro w E D ER ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hwv⟩ := hpre
  let sigma1 := sigma.setVar "c" 0
  have r1 : Run B (.assign "c" (.lit 0)) sigma sigma1 2 :=
    Run.assign (evalB_lit (by omega))
  have hinput1 : BaseOrientInput n nt o t rk O T R sigma1 :=
    hmem.input.setVar "c" 0
  have heng1 : EngineArrays n W E D ER ID BH BV BN sigma1 :=
    ⟨by simpa [sigma1] using heng.n_eq,
      by simpa [sigma1] using heng.elm_eq,
      by simpa [sigma1] using heng.deg_eq,
      by simpa [sigma1] using heng.rank_eq,
      by simpa [sigma1] using heng.idg_eq,
      by simpa [sigma1] using heng.head_eq,
      by simpa [sigma1] using heng.val_eq,
      by simpa [sigma1] using heng.next_eq⟩
  have hstable1 : ProviderStable sigma sigma1 :=
    ⟨by simp [sigma1], by simp [sigma1], by simp [sigma1], by simp [sigma1],
      by simp [sigma1], by simp [sigma1], by simp [sigma1], by simp [sigma1]⟩
  obtain ⟨A0, hA0⟩ := Lax3Proofs.RamDriver.exists_arrOf hmem.dst_length
  have hfill1 : RowFillAcc dst n (rankFilterSet dir R (w : ℕ) (Finset.range n))
      (rankFilterSet dir R (w : ℕ) ∅) sigma1 := by
    refine ⟨by simp, A0, by simpa [sigma1] using hA0, by simp [sigma1],
      by simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList], ?_⟩
    intro z
    simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
  have hfilter1 : RankFilterAcc dst rk n dir R (w : ℕ) ∅ sigma1 :=
    ⟨by simp, hfill1, hinput1.rank_eq, by simpa [sigma1] using hwv⟩
  let Walk : Finset ℕ → Env → Prop := fun S tau =>
    RankFilterAcc dst rk n dir R (w : ℕ) S tau ∧
      BaseOrientInput n nt o t rk O T R tau ∧
      EngineArrays n W E D ER ID BH BV BN tau ∧
      ProviderStable sigma tau
  have hEmit : Emits B n 15 dst "@" (rankFilterAct dir rk dst)
      (Finset.range n) Walk := by
    rintro S tau z hWalk hu hzn hzS hzCap
    obtain ⟨tau', K, hr, hK, hfilter', hfv, hfa⟩ :=
      rankFilterAcc_emits hnB w.isLt hR hrd hra
        S tau z hWalk.1 hu hzn hzS hzCap
    refine ⟨tau', K, hr, hK, ⟨hfilter', ?_, ?_, ?_⟩, hfv, hfa⟩
    · exact hWalk.2.1.of_emit_frame hod hoa htd hta hrd hra hfa
    · exact Lax3Proofs.Refine.OrderVirtualBaseOrient.EngineArrays.of_emit_frame
        hWalk.2.2.1 hdst hfv hfa
    · exact Lax3Proofs.Refine.OrderVirtualBaseOrient.ProviderStable.of_emit_frame
        hWalk.2.2.2 hfv
  have hWalk1 : Walk ∅ sigma1 :=
    ⟨hfilter1, hinput1, heng1, hstable1⟩
  have hmono : O (w : ℕ) ≤ O ((w : ℕ) + 1) :=
    hcsr.csr.mono (w : ℕ) w.isLt
  have hend : O ((w : ℕ) + 1) ≤ ns := hcsr.csr.le_ns (by omega)
  have hWalkVar : ∀ S tau (y : String) (z : ℕ),
      (y = "oj" ∨ y = "ojend" ∨ y = "u") → Walk S tau →
      Walk S (tau.setVar y z) := by
    intro S tau y z hy hWalk
    rcases hy with rfl | rfl | rfl
    · exact ⟨hWalk.1.setVar (by decide) (by decide) z,
        hWalk.2.1.setVar "oj" z,
        ⟨by simpa using hWalk.2.2.1.n_eq,
          by simpa using hWalk.2.2.1.elm_eq,
          by simpa using hWalk.2.2.1.deg_eq,
          by simpa using hWalk.2.2.1.rank_eq,
          by simpa using hWalk.2.2.1.idg_eq,
          by simpa using hWalk.2.2.1.head_eq,
          by simpa using hWalk.2.2.1.val_eq,
          by simpa using hWalk.2.2.1.next_eq⟩,
        Lax3Proofs.Refine.OrderVirtualBaseOrient.ProviderStable.setVar_of_private
          hWalk.2.2.2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) z⟩
    · exact ⟨hWalk.1.setVar (by decide) (by decide) z,
        hWalk.2.1.setVar "ojend" z,
        ⟨by simpa using hWalk.2.2.1.n_eq,
          by simpa using hWalk.2.2.1.elm_eq,
          by simpa using hWalk.2.2.1.deg_eq,
          by simpa using hWalk.2.2.1.rank_eq,
          by simpa using hWalk.2.2.1.idg_eq,
          by simpa using hWalk.2.2.1.head_eq,
          by simpa using hWalk.2.2.1.val_eq,
          by simpa using hWalk.2.2.1.next_eq⟩,
        Lax3Proofs.Refine.OrderVirtualBaseOrient.ProviderStable.setVar_of_private
          hWalk.2.2.2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) z⟩
    · exact ⟨hWalk.1.setVar (by decide) (by decide) z,
        hWalk.2.1.setVar "u" z,
        ⟨by simpa using hWalk.2.2.1.n_eq,
          by simpa using hWalk.2.2.1.elm_eq,
          by simpa using hWalk.2.2.1.deg_eq,
          by simpa using hWalk.2.2.1.rank_eq,
          by simpa using hWalk.2.2.1.idg_eq,
          by simpa using hWalk.2.2.1.head_eq,
          by simpa using hWalk.2.2.1.val_eq,
          by simpa using hWalk.2.2.1.next_eq⟩,
        Lax3Proofs.Refine.OrderVirtualBaseOrient.ProviderStable.setVar_of_private
          hWalk.2.2.2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) z⟩
  have hfresh : ∀ p, O (w : ℕ) ≤ p → p < O ((w : ℕ) + 1) →
      T p ∉ (∅ : Finset ℕ) ∪ accUpto O T (fun z => {z}) (w : ℕ) p := by
    intro p hp₀ hp₁ hp
    simp only [Finset.empty_union] at hp
    obtain ⟨q, hq₀, hqp, hqT⟩ := mem_accUpto.1 hp
    have he' : T p = T q := by simpa using hqT
    have he : T q = T p := he'.symm
    have hqp' := hcsr.nodup (w : ℕ) w.isLt q p hq₀ (by omega) hp₀ hp₁ he
    omega
  obtain ⟨sigma2, K2, r2, hK2, hWalk2, -, -⟩ :=
    emitAllRow_run (B := B) (o := o) (t := t) (x := "w")
      (j := "oj") (jend := "ojend") (a₁ := dst) (a₂ := "@")
      (n := n) (nv := n) (len := nt) (v := (w : ℕ)) (Ka := 15)
      (off := O) (tgt := T) (E₀ := ∅) (Cap := Finset.range n)
      (σ := sigma1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) w.isLt (by omega) hnB hinput1.off_eq hmono
      (le_trans hend hnsnt) (by omega) (by simpa [sigma1] using hwv)
      (fun _ _ h => h.2.1.tgt_eq)
      (fun p hp => hcsr.csr.target_lt p (lt_of_lt_of_le hp hend))
      hWalkVar hfresh
      (fun p _ hp => Finset.mem_range.2
        (hcsr.csr.target_lt p (lt_of_lt_of_le hp hend)))
      hEmit hWalk1
  simp only [Finset.empty_union] at hWalk2
  have hseteq : rankFilterSet dir R (w : ℕ) (rowTgt O T (w : ℕ)) =
      valSet (orientSet dir (ElimCert.elimOr G rho) w) := by
    simpa using rankFilterSet_base_eq dir hcsr hrho w.isLt
  have hrowFill := hWalk2.1.2.1
  rw [hseteq] at hrowFill
  obtain ⟨A, hA, hc, hrow⟩ := hrowFill.toSetRowRep
  have hcardLe : (orientSet dir (ElimCert.elimOr G rho) w).card ≤ n :=
    by simpa only [Fintype.card_fin] using
      Finset.card_le_univ (orientSet dir (ElimCert.elimOr G rho) w)
  have hcB : sigma2.vars "c" < B := by rw [hc]; omega
  have ec : (Expr.var "c").evalB B sigma2 =
      some (orientSet dir (ElimCert.elimOr G rho) w).card := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma2) hcB
    rwa [hc] at h
  let sigma3 := sigma2.setVar "vtail"
    (orientSet dir (ElimCert.elimOr G rho) w).card
  have r3 : Run B (.assign "vtail" (.var "c")) sigma2 sigma3 2 :=
    Run.assign ec
  have hmem3 : BaseOrientMem n nt o t rk dst O T R sigma3 :=
    ⟨hWalk2.2.1.setVar "vtail" _, by simpa [sigma3, hA]⟩
  have heng3 : EngineArrays n W E D ER ID BH BV BN sigma3 :=
    ⟨by simpa [sigma3] using hWalk2.2.2.1.n_eq,
      by simpa [sigma3] using hWalk2.2.2.1.elm_eq,
      by simpa [sigma3] using hWalk2.2.2.1.deg_eq,
      by simpa [sigma3] using hWalk2.2.2.1.rank_eq,
      by simpa [sigma3] using hWalk2.2.2.1.idg_eq,
      by simpa [sigma3] using hWalk2.2.2.1.head_eq,
      by simpa [sigma3] using hWalk2.2.2.1.val_eq,
      by simpa [sigma3] using hWalk2.2.2.1.next_eq⟩
  have hstable3 : ProviderStable sigma sigma3 :=
    Lax3Proofs.Refine.OrderVirtualBaseOrient.ProviderStable.setVar_of_private
      hWalk2.2.2.2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) _
  refine ⟨sigma3, 2 + K2 + 2, ?_, ?_, hmem3, heng3, hstable3,
    (orientSet dir (ElimCert.elimOr G rho) w).card, A, hrow, ?_, ?_⟩
  · simpa only [baseOrientProvide] using r1.seq (r2.seq r3)
  · simp only [baseOrientCost, Csr.rowLen]
    have := hK2
    simp only [Csr.rowLen] at this
    omega
  · simp [sigma3]
  · simpa [sigma3] using hA

/-! ## Axiom audit -/

#print axioms rankFilterAcc_emits
#print axioms rankFilterSet_base_eq
#print axioms baseOrientProvidesSetRows

end Lax3Proofs.Refine.OrderVirtualBaseOrient
