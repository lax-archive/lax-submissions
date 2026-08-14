import Lax3Proofs.Refine.OrderVirtualBaseFrat
import Lax3Proofs.Refine.OrderVirtualRename

/-!
# A compositional virtual fraternity provider

`OrderVirtualBaseFrat` proves the first implicit fraternity row directly from
the input CSR.  Later augmentation rounds need the same nested out-row/in-row
walk with those two rows supplied by an earlier virtual provider.  This file
separates that composition from the base representation.

The child providers share the scalar row-provider convention.  Four caller
scalars are therefore saved in a private constant-size array around an inner
call.  Private arrays are renamed at each fixed augmentation depth by
`OrderVirtualRename`; no augmented CSR is ever allocated.
-/

namespace Lax3Proofs.Refine.OrderVirtualFrat

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamAugment (outSet fratNbrs)
open Lax3Proofs.RamDriverAugment
  (Marks Emits Guarded valSet valSet_lt fratGuard guardFrat_of_emits)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.OrderVirtualBaseFrat
  (fratFe fratStep fratNum fratNum_eq inValSet_of_lt root_not_mem_fratVal)

variable {n : ℕ}

/-- Arrays owned by one compositional fraternity provider.  Only their
lengths are persistent, except for the stamp, which is restored to zero at
the provider boundary.  The child-persistent predicate deliberately does not
mention this level's stamp: a child is invoked while the outer stamp is live.
-/
structure FratWorkspace (n : ℕ) (P : Env → Prop) (sigma : Env) : Prop where
  persistent : P sigma
  vout_length : (sigma.arrs "vout").length = n
  vin_length : (sigma.arrs "vin").length = n
  vrow_length : (sigma.arrs "vrow").length = n
  save_length : (sigma.arrs "vsave").length = 4
  stamp_zero : sigma.arrs "stf" = arrOf n (fun _ => 0)

/-- Closure needed from the child-persistent state while the parent performs
its own scalar bookkeeping and writes its three private arrays. -/
structure FratScratchClosed (P : Env → Prop) : Prop where
  setVar : ∀ {sigma : Env} {a : String} {x : ℕ}, a ≠ "n" →
    P sigma → P (sigma.setVar a x)
  setVrow : ∀ {sigma : Env} {p x : ℕ}, P sigma →
    P (sigma.setArr "vrow" p x)
  setStamp : ∀ {sigma : Env} {p x : ℕ}, P sigma →
    P (sigma.setArr "stf" p x)
  setSave : ∀ {sigma : Env} {p x : ℕ}, P sigma →
    P (sigma.setArr "vsave" p x)

/-- The four scalar values retained across an inner provider call. -/
def fratSave (slot : ℕ) (value : Expr) : Com :=
  .store "vsave" (.lit slot) value

def fratRestore (name : String) (slot : ℕ) : Com :=
  .assign name (.get "vsave" (.lit slot))

/-- Save the caller-owned scalars that a recursively nested provider may use
as scratch. -/
def fratSaveState : Com :=
  .seq (fratSave 0 (.var "c"))
    (.seq (fratSave 1 (.var "froot"))
      (.seq (fratSave 2 (.var "fend"))
        (fratSave 3 (.var "fj"))))

/-- Restore the caller-owned scalars after a recursively nested provider. -/
def fratRestoreState : Com :=
  .seq (fratRestore "c" 0)
    (.seq (fratRestore "froot" 1)
      (.seq (fratRestore "fend" 2)
        (fratRestore "fj" 3)))

/-- The exact contents of the four-cell save area after `fratSaveState`. -/
def fratSavedValues (count root finish pos : ℕ) : ℕ → ℕ
  | 0 => count
  | 1 => root
  | 2 => finish
  | 3 => pos
  | _ => 0

/-- Saving the four caller scalars preserves both the child's persistent
memory and the elimination engine. -/
theorem fratSaveState_run {B n W count root finish pos : ℕ}
    {P : Env → Prop} {E D R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (hclose : FratScratchClosed P) (hP : P sigma)
    (heng : EngineArrays n W E D R ID BH BV BN sigma)
    (hlen : (sigma.arrs "vsave").length = 4)
    (hcount : sigma.vars "c" = count)
    (hroot : sigma.vars "froot" = root)
    (hfinish : sigma.vars "fend" = finish)
    (hpos : sigma.vars "fj" = pos)
    (hB4 : 3 < B)
    (hcountB : count < B) (hrootB : root < B)
    (hfinishB : finish < B) (hposB : pos < B) :
    ∃ tau,
      Run B fratSaveState sigma tau 12 ∧ P tau ∧
      EngineArrays n W E D R ID BH BV BN tau ∧
      tau.arrs "vsave" = arrOf 4 (fratSavedValues count root finish pos) := by
  obtain ⟨A, hA⟩ := Lax3Proofs.RamDriver.exists_arrOf hlen
  have ec : (Expr.var "c").evalB B sigma = some count := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma) (by rw [hcount]; exact hcountB)
    rwa [hcount] at h
  have hslot0 : 0 < (sigma.arrs "vsave").length := by omega
  let sigma1 := sigma.setArr "vsave" 0 count
  have r1 : Run B (fratSave 0 (.var "c")) sigma sigma1 3 :=
    Run.store (evalB_lit (by omega)) ec hslot0
  have eroot : (Expr.var "froot").evalB B sigma1 = some root := by
    have h := evalB_var (B := B) (x := "froot") (σ := sigma1)
      (by simp [sigma1, hroot, hrootB])
    simpa [sigma1, hroot] using h
  have hslot1 : 1 < (sigma1.arrs "vsave").length := by
    have hlen1 : (sigma1.arrs "vsave").length = 4 := by
      simpa [sigma1] using hlen
    rw [hlen1]
    omega
  let sigma2 := sigma1.setArr "vsave" 1 root
  have r2 : Run B (fratSave 1 (.var "froot")) sigma1 sigma2 3 :=
    Run.store (evalB_lit (by omega)) eroot hslot1
  have efinish : (Expr.var "fend").evalB B sigma2 = some finish := by
    have h := evalB_var (B := B) (x := "fend") (σ := sigma2)
      (by simp [sigma2, sigma1, hfinish, hfinishB])
    simpa [sigma2, sigma1, hfinish] using h
  have hslot2 : 2 < (sigma2.arrs "vsave").length := by
    have hlen2 : (sigma2.arrs "vsave").length = 4 := by
      simpa [sigma2, sigma1] using hlen
    rw [hlen2]
    omega
  let sigma3 := sigma2.setArr "vsave" 2 finish
  have r3 : Run B (fratSave 2 (.var "fend")) sigma2 sigma3 3 :=
    Run.store (evalB_lit (by omega)) efinish hslot2
  have epos : (Expr.var "fj").evalB B sigma3 = some pos := by
    have h := evalB_var (B := B) (x := "fj") (σ := sigma3)
      (by simp [sigma3, sigma2, sigma1, hpos, hposB])
    simpa [sigma3, sigma2, sigma1, hpos] using h
  have hslot3 : 3 < (sigma3.arrs "vsave").length := by
    have hlen3 : (sigma3.arrs "vsave").length = 4 := by
      simpa [sigma3, sigma2, sigma1] using hlen
    rw [hlen3]
    omega
  let sigma4 := sigma3.setArr "vsave" 3 pos
  have r4 : Run B (fratSave 3 (.var "fj")) sigma3 sigma4 3 :=
    Run.store (evalB_lit (by omega)) epos hslot3
  have hP4 : P sigma4 :=
    hclose.setSave (hclose.setSave (hclose.setSave (hclose.setSave hP)))
  have heng4 : EngineArrays n W E D R ID BH BV BN sigma4 := by
    refine ⟨by simpa [sigma4, sigma3, sigma2, sigma1] using heng.n_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.elm_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.deg_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.rank_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.idg_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.head_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.val_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.next_eq⟩
  have hsave4 : sigma4.arrs "vsave" =
      arrOf 4 (fratSavedValues count root finish pos) := by
    change ((((sigma.arrs "vsave").set 0 count).set 1 root).set 2 finish).set 3 pos =
      arrOf 4 (fratSavedValues count root finish pos)
    rw [hA, set_arrOf_eq_upd, set_arrOf_eq_upd, set_arrOf_eq_upd,
      set_arrOf_eq_upd]
    apply arrOf_congr
    intro i hi
    interval_cases i <;> simp [fratSavedValues, upd]
  refine ⟨sigma4, ?_, hP4, heng4, hsave4⟩
  simpa only [fratSaveState] using r1.seq (r2.seq (r3.seq r4))

/-- Restoring from the save area returns the four caller scalars exactly and
again preserves both persistent memory and the elimination engine. -/
theorem fratRestoreState_run {B n W count root finish pos : ℕ}
    {P : Env → Prop} {E D R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (hclose : FratScratchClosed P) (hP : P sigma)
    (heng : EngineArrays n W E D R ID BH BV BN sigma)
    (hsave : sigma.arrs "vsave" =
      arrOf 4 (fratSavedValues count root finish pos))
    (hB4 : 3 < B)
    (hcountB : count < B) (hrootB : root < B)
    (hfinishB : finish < B) (hposB : pos < B) :
    ∃ tau,
      Run B fratRestoreState sigma tau 12 ∧ P tau ∧
      EngineArrays n W E D R ID BH BV BN tau ∧
      tau.vars "c" = count ∧ tau.vars "froot" = root ∧
      tau.vars "fend" = finish ∧ tau.vars "fj" = pos := by
  have getSaved (slot value : ℕ) (hslot : slot < 4)
      (hvalue : fratSavedValues count root finish pos slot = value)
      (hvalueB : value < B) :
      (Expr.get "vsave" (.lit slot)).evalB B sigma = some value := by
    have hget : (sigma.arrs "vsave").getD slot 0 = value := by
      rw [hsave, getD_arrOf _ hslot, hvalue]
    have hbounded : (sigma.arrs "vsave").getD slot 0 < B := by
      rw [hget]
      exact hvalueB
    have h := RunStep.eval_get B sigma "vsave" (.lit slot) slot
      (evalB_lit (by omega)) (by rw [hsave, length_arrOf]; exact hslot) hbounded
    rwa [hget] at h
  have e0 := getSaved 0 count (by omega) (by rfl) hcountB
  let sigma1 := sigma.setVar "c" count
  have r1 : Run B (fratRestore "c" 0) sigma sigma1 3 := Run.assign e0
  have e1sigma : (Expr.get "vsave" (.lit 1)).evalB B sigma = some root :=
    getSaved 1 root (by omega) (by rfl) hrootB
  have e1 : (Expr.get "vsave" (.lit 1)).evalB B sigma1 = some root := by
    simpa [sigma1] using e1sigma
  let sigma2 := sigma1.setVar "froot" root
  have r2 : Run B (fratRestore "froot" 1) sigma1 sigma2 3 := Run.assign e1
  have e2sigma : (Expr.get "vsave" (.lit 2)).evalB B sigma = some finish :=
    getSaved 2 finish (by omega) (by rfl) hfinishB
  have e2 : (Expr.get "vsave" (.lit 2)).evalB B sigma2 = some finish := by
    simpa [sigma2, sigma1] using e2sigma
  let sigma3 := sigma2.setVar "fend" finish
  have r3 : Run B (fratRestore "fend" 2) sigma2 sigma3 3 := Run.assign e2
  have e3sigma : (Expr.get "vsave" (.lit 3)).evalB B sigma = some pos :=
    getSaved 3 pos (by omega) (by rfl) hposB
  have e3 : (Expr.get "vsave" (.lit 3)).evalB B sigma3 = some pos := by
    simpa [sigma3, sigma2, sigma1] using e3sigma
  let sigma4 := sigma3.setVar "fj" pos
  have r4 : Run B (fratRestore "fj" 3) sigma3 sigma4 3 := Run.assign e3
  have hP4 : P sigma4 :=
    hclose.setVar (by decide)
      (hclose.setVar (by decide)
        (hclose.setVar (by decide) (hclose.setVar (by decide) hP)))
  have heng4 : EngineArrays n W E D R ID BH BV BN sigma4 := by
    refine ⟨by simpa [sigma4, sigma3, sigma2, sigma1] using heng.n_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.elm_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.deg_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.rank_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.idg_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.head_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.val_eq,
      by simpa [sigma4, sigma3, sigma2, sigma1] using heng.next_eq⟩
  refine ⟨sigma4, ?_, hP4, heng4,
    by simp [sigma4, sigma3, sigma2, sigma1],
    by simp [sigma4, sigma3, sigma2, sigma1],
    by simp [sigma4, sigma3, sigma2, sigma1],
    by simp [sigma4, sigma3, sigma2, sigma1]⟩
  simpa only [fratRestoreState] using r1.seq (r2.seq (r3.seq r4))

/-- One outer-row slot.  Save the output count, root, outer endpoint and scan
position; invoke the incoming-row provider at the current neighbour; restore
the parent state; then emit the generated incoming row through the fraternity
stamp. -/
def virtualFratInner (provideIn : Com) : Com :=
  .seq fratSaveState
    (.seq (.assign "w" (.var "u"))
      (.seq provideIn
        (.seq fratRestoreState
          (bufferScan "vin" "fk" "vtail" "u"
            (fratGuard (rowFillAct "vrow"))))))

/-- Generate one exact fraternity row from two virtual orientation-row
providers and restore the shared stamp to zero. -/
def virtualFratProvide (provideOut provideIn : Com) : Com :=
  .seq provideOut
    (.seq (.assign "froot" (.var "w"))
      (.seq (.assign "fend" (.var "vtail"))
        (.seq (.assign "c" (.lit 0))
          (.seq (.store "stf" (.var "w") (.lit 1))
            (.seq (bufferScan "vout" "fj" "fend" "u"
                (virtualFratInner provideIn))
              (.seq (bufferScan "vrow" "fc" "c" "u"
                  (.store "stf" (.var "u") (.lit 0)))
                (.seq (.assign "u" (.var "froot"))
                  (.seq (.store "stf" (.var "u") (.lit 0))
                    (.seq (.assign "w" (.var "froot"))
                      (.assign "vtail" (.var "c")))))))))))

/-! ## Closure at the generic elimination boundary -/

theorem fratWorkspace_engineClosed {P : Env → Prop}
    (hP : EngineClosed P) : EngineClosed (FratWorkspace n P) := by
  constructor
  · intro sigma a x ha hmem
    refine ⟨hP.setVar ha hmem.persistent, by simpa using hmem.vout_length,
      by simpa using hmem.vin_length, by simpa using hmem.vrow_length,
      by simpa using hmem.save_length, by simpa using hmem.stamp_zero⟩
  · intro sigma a i x ha hmem
    have hvout : a ≠ "vout" := by
      intro h; subst a; simpa [engineArrNames] using ha
    have hvin : a ≠ "vin" := by
      intro h; subst a; simpa [engineArrNames] using ha
    have hvsave : a ≠ "vsave" := by
      intro h; subst a; simpa [engineArrNames] using ha
    have hstf : a ≠ "stf" := by
      intro h; subst a; simpa [engineArrNames] using ha
    refine ⟨hP.setArr ha hmem.persistent,
      by rw [length_arrs_setArr,
        hmem.vout_length],
      by rw [length_arrs_setArr,
        hmem.vin_length],
      by rw [length_arrs_setArr,
        hmem.vrow_length],
      by rw [length_arrs_setArr,
        hmem.save_length], ?_⟩
    rw [arrs_setArr, if_neg (Ne.symm hstf)]
    exact hmem.stamp_zero

theorem fratWorkspace_engineRunClosed {P : Env → Prop}
    (hP : EngineRunClosed P) : EngineRunClosed (FratWorkspace n P) := by
  intro B K c sigma sigma' hrun hwv hwa hmem
  have frame (a : String) (ha : a ∉ engineArrNames) :
      sigma'.arrs a = sigma.arrs a := by
    apply hrun.frame_arr a
    intro hac
    exact ha (hwa a hac)
  refine ⟨hP hrun hwv hwa hmem.persistent,
    by rw [congrArg List.length (frame "vout" (by decide)),
      hmem.vout_length],
    by rw [congrArg List.length (frame "vin" (by decide)),
      hmem.vin_length],
    by rw [Lax3Proofs.RamDriver.run_length_arrs hrun "vrow",
      hmem.vrow_length],
    by rw [congrArg List.length (frame "vsave" (by decide)),
      hmem.save_length],
    by rw [frame "stf" (by decide)]; exact hmem.stamp_zero⟩

/-! ## Generic nested-scan invariants -/

/-- State carried by the outer scan of a provider-composed fraternity row. -/
structure VirtualOuterAcc (n W : ℕ) (P : Env → Prop)
    (D : Orientation n) (root : Fin n) (Cap : Finset ℕ)
    (outTail : ℕ) (Aout : ℕ → ℕ) (p : ℕ)
    (E Deg ER ID BH BV BN : ℕ → ℕ) (tau : Env) : Prop where
  marks : Marks "stf" n 1
    ({(root : ℕ)} ∪ bufferAcc p Aout (fratStep D (root : ℕ))) (fun _ => 0) tau
  fill : RowFillAcc "vrow" n Cap
    (bufferAcc p Aout (fratStep D (root : ℕ))) tau
  persistent : P tau
  engine : EngineArrays n W E Deg ER ID BH BV BN tau
  out_eq : tau.arrs "vout" = arrOf n Aout
  vin_length : (tau.arrs "vin").length = n
  save_length : (tau.arrs "vsave").length = 4
  root_eq : tau.vars "froot" = (root : ℕ)
  end_eq : tau.vars "fend" = outTail

namespace VirtualOuterAcc

theorem setVarPrivate {n W : ℕ} {P : Env → Prop}
    {D : Orientation n} {root : Fin n} {Cap : Finset ℕ}
    {outTail : ℕ} {Aout : ℕ → ℕ} {p : ℕ}
    {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (hclose : FratScratchClosed P)
    (h : VirtualOuterAcc n W P D root Cap outTail Aout p
      E Deg ER ID BH BV BN tau)
    {y : String} (hyn : y ≠ "n") (hyr : y ≠ "froot")
    (hye : y ≠ "fend") (hyc : y ≠ "c") (x : ℕ) :
    VirtualOuterAcc n W P D root Cap outTail Aout p
      E Deg ER ID BH BV BN (tau.setVar y x) := by
  refine ⟨h.marks.setVar y x, h.fill.setVar hyc x,
    hclose.setVar hyn h.persistent, ?_, by simpa using h.out_eq,
    by simpa using h.vin_length, by simpa using h.save_length, ?_, ?_⟩
  · exact ⟨by rw [vars_setVar, if_neg (Ne.symm hyn)]; exact h.engine.n_eq,
      by simpa using h.engine.elm_eq, by simpa using h.engine.deg_eq,
      by simpa using h.engine.rank_eq, by simpa using h.engine.idg_eq,
      by simpa using h.engine.head_eq, by simpa using h.engine.val_eq,
      by simpa using h.engine.next_eq⟩
  · rw [vars_setVar, if_neg (Ne.symm hyr)]
    exact h.root_eq
  · rw [vars_setVar, if_neg (Ne.symm hye)]
    exact h.end_eq

end VirtualOuterAcc

/-- State carried by the guarded incoming-row scan after the nested provider
has returned and the caller scalars have been restored. -/
structure VirtualInnerAcc (n W : ℕ) (P : Env → Prop)
    (root : Fin n) (Cap : Finset ℕ) (outTail outerPos : ℕ)
    (Aout Ain : ℕ → ℕ) (inTail : ℕ)
    (E Deg ER ID BH BV BN : ℕ → ℕ) (S : Finset ℕ) (tau : Env) : Prop where
  fill : RowFillAcc "vrow" n Cap S tau
  persistent : P tau
  engine : EngineArrays n W E Deg ER ID BH BV BN tau
  out_eq : tau.arrs "vout" = arrOf n Aout
  in_eq : tau.arrs "vin" = arrOf n Ain
  save_length : (tau.arrs "vsave").length = 4
  in_tail_eq : tau.vars "vtail" = inTail
  root_eq : tau.vars "froot" = (root : ℕ)
  end_eq : tau.vars "fend" = outTail
  outer_eq : tau.vars "fj" = outerPos

namespace FratScratchClosed

/-- The concrete append action performs exactly one permitted row store and
one permitted scalar assignment. -/
theorem run_rowFillAct {B K : ℕ} {P : Env → Prop} {sigma tau : Env}
    (hclose : FratScratchClosed P) (hP : P sigma)
    (hr : Run B (rowFillAct "vrow") sigma tau K) : P tau := by
  obtain ⟨k, hk, hrun⟩ := hr
  rw [rowFillAct] at hrun
  cases hrun with
  | seq hstore hassign =>
      cases hstore with
      | store _ _ _ =>
          cases hassign with
          | assign _ =>
              exact hclose.setVar (by decide) (hclose.setVrow hP)

/-- Any command whose effects are confined to the fraternity scratch names
preserves the child-persistent predicate.  This is used for the final stamp
cleanup loop, whose operational theorem deliberately knows nothing about
the caller's predicate. -/
theorem run {B K : ℕ} {P : Env → Prop} {c : Com} {sigma tau : Env}
    (hclose : FratScratchClosed P)
    (hr : Run B c sigma tau K)
    (hvars : ∀ a ∈ c.wvars, a ≠ "n")
    (harrs : ∀ a ∈ c.warrs,
      a = "vrow" ∨ a = "stf" ∨ a = "vsave")
    (hreads : ¬ c.reads) (hwrites : c.NoWrite)
    (hP : P sigma) : P tau := by
  obtain ⟨k, hk, hrun⟩ := hr
  clear hk K
  induction hrun with
  | skip => exact hP
  | assign he =>
      exact hclose.setVar (hvars _ (by simp [Com.wvars])) hP
  | @store sigma0 a i e idx value hi he hslot =>
      have ha := harrs a (by simp [Com.warrs])
      rcases ha with ha | ha | ha
      · subst a
        exact hclose.setVrow hP
      · subst a
        exact hclose.setStamp hP
      · subst a
        exact hclose.setSave hP
  | @seq c0 c1 sigma0 sigma1 sigma2 k0 k1 hc hd ihc ihd =>
      have hv : ∀ a ∈ c0.wvars, a ≠ "n" := by
        intro a ha
        exact hvars a (by simp [Com.wvars, ha])
      have hv' : ∀ a ∈ c1.wvars, a ≠ "n" := by
        intro a ha
        exact hvars a (by simp [Com.wvars, ha])
      have ha : ∀ a ∈ c0.warrs,
          a = "vrow" ∨ a = "stf" ∨ a = "vsave" := by
        intro a h
        exact harrs a (by simp [Com.warrs, h])
      have ha' : ∀ a ∈ c1.warrs,
          a = "vrow" ∨ a = "stf" ∨ a = "vsave" := by
        intro a h
        exact harrs a (by simp [Com.warrs, h])
      have hr0 : ¬ c0.reads := by
        have h : ¬ c0.reads ∧ ¬ c1.reads := by
          simpa [Com.reads] using hreads
        exact h.1
      have hr1 : ¬ c1.reads := by
        have h : ¬ c0.reads ∧ ¬ c1.reads := by
          simpa [Com.reads] using hreads
        exact h.2
      have hw0 : c0.NoWrite := by
        have h : c0.NoWrite ∧ c1.NoWrite := by
          simpa [Com.NoWrite] using hwrites
        exact h.1
      have hw1 : c1.NoWrite := by
        have h : c0.NoWrite ∧ c1.NoWrite := by
          simpa [Com.NoWrite] using hwrites
        exact h.2
      exact ihd hv' ha' hr1 hw1 (ihc hv ha hr0 hw0 hP)
  | @ite_true b c0 c1 sigma0 sigma1 k0 hb hc ih =>
      have hv : ∀ a ∈ c0.wvars, a ≠ "n" := by
        intro a ha
        exact hvars a (by simp [Com.wvars, ha])
      have ha : ∀ a ∈ c0.warrs,
          a = "vrow" ∨ a = "stf" ∨ a = "vsave" := by
        intro a h
        exact harrs a (by simp [Com.warrs, h])
      have hr0 : ¬ c0.reads := by
        have h : ¬ c0.reads ∧ ¬ c1.reads := by
          simpa [Com.reads] using hreads
        exact h.1
      have hw0 : c0.NoWrite := by
        have h : c0.NoWrite ∧ c1.NoWrite := by
          simpa [Com.NoWrite] using hwrites
        exact h.1
      exact ih hv ha hr0 hw0 hP
  | @ite_false b c0 c1 sigma0 sigma1 k0 hb hd ih =>
      have hv : ∀ a ∈ c1.wvars, a ≠ "n" := by
        intro a ha
        exact hvars a (by simp [Com.wvars, ha])
      have ha : ∀ a ∈ c1.warrs,
          a = "vrow" ∨ a = "stf" ∨ a = "vsave" := by
        intro a h
        exact harrs a (by simp [Com.warrs, h])
      have hr0 : ¬ c1.reads := by
        have h : ¬ c0.reads ∧ ¬ c1.reads := by
          simpa [Com.reads] using hreads
        exact h.2
      have hw0 : c1.NoWrite := by
        have h : c0.NoWrite ∧ c1.NoWrite := by
          simpa [Com.NoWrite] using hwrites
        exact h.2
      exact ih hv ha hr0 hw0 hP
  | @while_true b c0 sigma0 sigma1 sigma2 k0 k1 hb hc hw ihc ihw =>
      have hv : ∀ a ∈ c0.wvars, a ≠ "n" := by
        intro a ha
        exact hvars a (by simpa [Com.wvars] using ha)
      have ha : ∀ a ∈ c0.warrs,
          a = "vrow" ∨ a = "stf" ∨ a = "vsave" := by
        intro a h
        exact harrs a (by simpa [Com.warrs] using h)
      have hr0 : ¬ c0.reads := by
        simpa [Com.reads] using hreads
      have hw0 : c0.NoWrite := by
        simpa [Com.NoWrite] using hwrites
      exact ihw hvars harrs hreads hwrites (ihc hv ha hr0 hw0 hP)
  | while_false hb => exact hP
  | read h =>
      exact False.elim (hreads (by simp [Com.reads]))
  | write he =>
      exact False.elim (by simpa [Com.NoWrite] using hwrites)

end FratScratchClosed

namespace VirtualInnerAcc

theorem setVarPrivate {n W : ℕ} {P : Env → Prop}
    {root : Fin n} {Cap : Finset ℕ} {outTail outerPos : ℕ}
    {Aout Ain : ℕ → ℕ} {inTail : ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ}
    {S : Finset ℕ} {tau : Env}
    (hclose : FratScratchClosed P)
    (h : VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S tau)
    {y : String} (hyc : y ≠ "c") (hyn : y ≠ "n")
    (hyvt : y ≠ "vtail") (hyr : y ≠ "froot") (hye : y ≠ "fend")
    (hyo : y ≠ "fj") (x : ℕ) :
    VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S (tau.setVar y x) := by
  refine ⟨h.fill.setVar hyc x, hclose.setVar hyn h.persistent, ?_,
    by simpa using h.out_eq, by simpa using h.in_eq,
    by simpa using h.save_length, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [vars_setVar, if_neg (Ne.symm hyn)]; exact h.engine.n_eq,
      by simpa using h.engine.elm_eq, by simpa using h.engine.deg_eq,
      by simpa using h.engine.rank_eq, by simpa using h.engine.idg_eq,
      by simpa using h.engine.head_eq, by simpa using h.engine.val_eq,
      by simpa using h.engine.next_eq⟩
  · rw [vars_setVar, if_neg (Ne.symm hyvt)]
    exact h.in_tail_eq
  · rw [vars_setVar, if_neg (Ne.symm hyr)]
    exact h.root_eq
  · rw [vars_setVar, if_neg (Ne.symm hye)]
    exact h.end_eq
  · rw [vars_setVar, if_neg (Ne.symm hyo)]
    exact h.outer_eq

theorem setStamp {n W : ℕ} {P : Env → Prop}
    {root : Fin n} {Cap : Finset ℕ} {outTail outerPos : ℕ}
    {Aout Ain : ℕ → ℕ} {inTail : ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ}
    {S : Finset ℕ} {tau : Env}
    (hclose : FratScratchClosed P)
    (h : VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S tau) (p x : ℕ) :
    VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S (tau.setArr "stf" p x) := by
  refine ⟨h.fill.setArr_of_ne (by decide) p x,
    hclose.setStamp h.persistent, ?_, by simpa using h.out_eq,
    by simpa using h.in_eq, by simpa using h.save_length,
    by simpa using h.in_tail_eq, by simpa using h.root_eq,
    by simpa using h.end_eq, by simpa using h.outer_eq⟩
  exact ⟨by simpa using h.engine.n_eq, by simpa using h.engine.elm_eq,
    by simpa using h.engine.deg_eq, by simpa using h.engine.rank_eq,
    by simpa using h.engine.idg_eq, by simpa using h.engine.head_eq,
    by simpa using h.engine.val_eq, by simpa using h.engine.next_eq⟩

end VirtualInnerAcc

/-- Extending a generic fraternity row preserves the child-persistent state. -/
theorem virtualInnerAcc_emits {B n W : ℕ} {P : Env → Prop}
    {root : Fin n} {Cap : Finset ℕ} {outTail outerPos : ℕ}
    {Aout Ain : ℕ → ℕ} {inTail : ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ}
    (hclose : FratScratchClosed P)
    (hnB : n < B) (hCap : Cap ⊆ Finset.range n) :
    Emits B n 7 "vrow" "@" (rowFillAct "vrow") Cap
      (VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
        E Deg ER ID BH BV BN) := by
  rintro S tau z hA hu hzn hzS hzCap
  obtain ⟨tau', K, hr, hK, hfill, hfv, hfa⟩ :=
    rowFillAcc_emits (dst := "vrow") hnB hCap S tau z hA.fill hu hzn hzS hzCap
  refine ⟨tau', K, hr, hK, ?_, hfv, hfa⟩
  refine ⟨hfill, hclose.run_rowFillAct hA.persistent hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [hfv "n" (by decide)]; exact hA.engine.n_eq,
      by rw [hfa "elm" (by decide) (by decide)]; exact hA.engine.elm_eq,
      by rw [hfa "deg" (by decide) (by decide)]; exact hA.engine.deg_eq,
      by rw [hfa "rnk" (by decide) (by decide)]; exact hA.engine.rank_eq,
      by rw [hfa "idg" (by decide) (by decide)]; exact hA.engine.idg_eq,
      by rw [hfa "bh" (by decide) (by decide)]; exact hA.engine.head_eq,
      by rw [hfa "bv" (by decide) (by decide)]; exact hA.engine.val_eq,
      by rw [hfa "bn" (by decide) (by decide)]; exact hA.engine.next_eq⟩
  · rw [hfa "vout" (by decide) (by decide)]
    exact hA.out_eq
  · rw [hfa "vin" (by decide) (by decide)]
    exact hA.in_eq
  · rw [congrArg List.length (hfa "vsave" (by decide) (by decide))]
    exact hA.save_length
  · rw [hfv "vtail" (by decide)]
    exact hA.in_tail_eq
  · rw [hfv "froot" (by decide)]
    exact hA.root_eq
  · rw [hfv "fend" (by decide)]
    exact hA.end_eq
  · rw [hfv "fj" (by decide)]
    exact hA.outer_eq

/-- The standard fraternity stamp guard over the generic accumulator. -/
theorem virtualInnerAcc_guarded {B n W : ℕ} {P : Env → Prop}
    {root : Fin n} {Cap : Finset ℕ} {outTail outerPos : ℕ}
    {Aout Ain : ℕ → ℕ} {inTail : ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ}
    (hclose : FratScratchClosed P)
    (hB1 : 1 < B) (hnB : n < B) (hCap : Cap ⊆ Finset.range n) :
    Guarded B n 15 (fratGuard (rowFillAct "vrow"))
      (fratFe (root : ℕ)) Cap
      (fun S tau => Marks "stf" n 1 ({(root : ℕ)} ∪ S) (fun _ => 0) tau ∧
        VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
          E Deg ER ID BH BV BN S tau) := by
  have he := virtualInnerAcc_emits (B := B) (n := n) (W := W) (P := P)
    (root := root) (Cap := Cap) (outTail := outTail) (outerPos := outerPos)
    (Aout := Aout) (Ain := Ain) (inTail := inTail) (E := E) (Deg := Deg)
    (ER := ER) (ID := ID) (BH := BH) (BV := BV) (BN := BN)
    hclose hnB hCap
  have hg := guardFrat_of_emits (B := B) (n := n) (Ka := 7)
    (i := (root : ℕ)) (a₁ := "vrow") (a₂ := "@")
    (act := rowFillAct "vrow") (Cap := Cap)
    (ha₁ := by decide) (ha₂ := by decide) hB1 hnB
    (fun _ _ p x h => h.setStamp hclose p x) he
  simpa only [fratGuard, fratFe, Nat.reduceAdd] using hg

/-- Run the guarded incoming-buffer scan after the nested provider has
returned and the parent state has been restored. -/
theorem virtualInnerBuffer_run {B n W : ℕ} {P : Env → Prop}
    {D : Orientation n} {root : Fin n} {z : ℕ} (hz : z < n)
    {Cap S : Finset ℕ} {outTail outerPos inTail : ℕ}
    {Aout Ain : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (hclose : FratScratchClosed P)
    (hB1 : 1 < B) (hnB : n < B) (hCap : Cap ⊆ Finset.range n)
    (hrow : SetRowRep (D.inN ⟨z, hz⟩) inTail Ain)
    (hfeCap : ∀ p, p < inTail → fratFe (root : ℕ) (Ain p) ⊆ Cap)
    (hmarks : Marks "stf" n 1 ({(root : ℕ)} ∪ S) (fun _ => 0) tau)
    (hacc : VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S tau) :
    ∃ tau' K,
      Run B (bufferScan "vin" "fk" "vtail" "u"
        (fratGuard (rowFillAct "vrow"))) tau tau' K ∧
      K ≤ inTail * 26 + 6 ∧
      Marks "stf" n 1 ({(root : ℕ)} ∪ (S ∪ fratStep D (root : ℕ) z))
        (fun _ => 0) tau' ∧
      VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
        E Deg ER ID BH BV BN (S ∪ fratStep D (root : ℕ) z) tau' := by
  let J : Finset ℕ → Env → Prop := fun U sigma =>
    Marks "stf" n 1 ({(root : ℕ)} ∪ U) (fun _ => 0) sigma ∧
      VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
        E Deg ER ID BH BV BN U sigma
  obtain ⟨tau', K, hr, hK, hJ⟩ :=
    emitBuffer_run (B := B) (n := n) (tail := inTail) (Kg := 15)
      (src := "vin") (j := "fk") (jend := "vtail")
      (grd := fratGuard (rowFillAct "vrow"))
      (S := D.inN ⟨z, hz⟩) (A := Ain) (fe := fratFe (root : ℕ))
      (J := J) (E0 := S) (Cap := Cap) (sigma := tau)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hB1 hnB hrow hacc.in_tail_eq hacc.in_eq
      (fun _ _ h => h.2.in_eq)
      (by
        intro U sigma y x hy hJ
        refine ⟨hJ.1.setVar y x, ?_⟩
        rcases hy with rfl | rfl
        · exact hJ.2.setVarPrivate hclose (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) x
        · exact hJ.2.setVarPrivate hclose (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) x)
      hfeCap (virtualInnerAcc_guarded hclose hB1 hnB hCap) ⟨hmarks, hacc⟩
  have hstep : bufferAcc inTail Ain (fratFe (root : ℕ)) =
      fratStep D (root : ℕ) z := by
    rw [bufferAcc_eq_biUnion_valSet hrow, fratStep, inValSet_of_lt D hz]
  rw [hstep] at hJ
  exact ⟨tau', K, hr, by omega, hJ.1, hJ.2⟩

/-! ## One generic outer slot -/

/-- Provider commands may use their own scratch scalars, but not the scalar
state owned by the virtual elimination engine.  `w` is the row argument and
is restored explicitly by the parent provider. -/
structure FratStableFrames (provide : Com) : Prop where
  n : "n" ∉ provide.wvars
  i : "i" ∉ provide.wvars
  sp : "sp" ∉ provide.wvars
  ls : "ls" ∉ provide.wvars
  cnt : "cnt" ∉ provide.wvars
  mind : "mind" ∉ provide.wvars
  kmax : "kmax" ∉ provide.wvars

/-- Arrays of the outer fraternity walk that an incoming-row child must not
overwrite.  A recursively nested provider obtains these facts after its
private arrays have been renamed. -/
structure FratIncomingFrames (provide : Com) : Prop where
  stable : FratStableFrames provide
  vout : "vout" ∉ provide.warrs
  vrow : "vrow" ∉ provide.warrs
  stamp : "stf" ∉ provide.warrs
  save : "vsave" ∉ provide.warrs

/-- Arrays that an outgoing-row child must leave for the parent workspace. -/
structure FratOutgoingFrames (provide : Com) : Prop where
  stable : FratStableFrames provide
  vin : "vin" ∉ provide.warrs
  vrow : "vrow" ∉ provide.warrs
  stamp : "stf" ∉ provide.warrs
  save : "vsave" ∉ provide.warrs

/-- One complete outer-row slot, including save/restore around the nested
incoming provider. -/
theorem virtualFratInner_run {B n W : ℕ} {P : Env → Prop}
    {provideIn : Com} {kin : ℕ → ℕ}
    {D : Orientation n} {root : Fin n} {outTail p : ℕ}
    {Aout : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (hclose : FratScratchClosed P) (hframes : FratIncomingFrames provideIn)
    (hB4 : 3 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W (fun w => D.inN w) P "vin" provideIn kin)
    (hout : SetRowRep (outSet D root) outTail Aout)
    (hp : p < outTail) (hfj : tau.vars "fj" = p)
    (houter : VirtualOuterAcc n W P D root (fratNum D root)
      outTail Aout p E Deg ER ID BH BV BN tau) :
    ∃ tau' K,
      Run B (virtualFratInner provideIn) (tau.setVar "u" (Aout p)) tau' K ∧
      K ≤ kin (Aout p) +
        26 * (D.inN ⟨Aout p, hout.value_lt p hp⟩).card + 32 ∧
      tau'.vars "fj" = p ∧
      VirtualOuterAcc n W P D root (fratNum D root)
        outTail Aout (p + 1) E Deg ER ID BH BV BN tau' := by
  classical
  let z := Aout p
  have hz : z < n := hout.value_lt p hp
  let S := bufferAcc p Aout (fratStep D (root : ℕ))
  have hCap : fratNum D root ⊆ Finset.range n := by
    rw [fratNum_eq]
    intro y hy
    exact Finset.mem_range.2 (valSet_lt hy)
  obtain ⟨hSsub, Acur, hAcur, hc, hnd, hmem⟩ := houter.fill
  change S ⊆ fratNum D root at hSsub
  have hScard : S.card < B := by
    have hle := Finset.card_le_card (hSsub.trans hCap)
    rw [Finset.card_range] at hle
    omega
  have hrootB : (root : ℕ) < B := lt_trans root.isLt hnB
  have houtTailB : outTail < B := lt_of_le_of_lt hout.tail_le hnB
  have hpB : p < B := lt_trans hp houtTailB
  let sigma0 := tau.setVar "u" z
  have hP0 : P sigma0 := hclose.setVar (by decide) houter.persistent
  have heng0 : EngineArrays n W E Deg ER ID BH BV BN sigma0 := by
    refine ⟨by simpa [sigma0] using houter.engine.n_eq,
      by simpa [sigma0] using houter.engine.elm_eq,
      by simpa [sigma0] using houter.engine.deg_eq,
      by simpa [sigma0] using houter.engine.rank_eq,
      by simpa [sigma0] using houter.engine.idg_eq,
      by simpa [sigma0] using houter.engine.head_eq,
      by simpa [sigma0] using houter.engine.val_eq,
      by simpa [sigma0] using houter.engine.next_eq⟩
  have hsaveLen0 : (sigma0.arrs "vsave").length = 4 := by
    simpa [sigma0] using houter.save_length
  have hc0 : sigma0.vars "c" = S.card := by
    simpa [sigma0] using hc
  have hroot0 : sigma0.vars "froot" = (root : ℕ) := by
    simpa [sigma0] using houter.root_eq
  have hend0 : sigma0.vars "fend" = outTail := by
    simpa [sigma0] using houter.end_eq
  have hfj0 : sigma0.vars "fj" = p := by
    simpa [sigma0] using hfj
  obtain ⟨sigma1, r1, hP1, heng1, hsave1⟩ :=
    fratSaveState_run hclose hP0 heng0 hsaveLen0 hc0 hroot0 hend0 hfj0
      hB4 hScard hrootB houtTailB hpB
  have hu1 : sigma1.vars "u" = z := by
    rw [r1.frame_var "u" (by decide)]
    simp [sigma0]
  have eu1 : (Expr.var "u").evalB B sigma1 = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := sigma1)
      (by rw [hu1]; exact lt_trans hz hnB)
    rwa [hu1] at h
  let sigma2 := sigma1.setVar "w" z
  have r2 : Run B (.assign "w" (.var "u")) sigma1 sigma2 2 := Run.assign eu1
  have hP2 : P sigma2 := hclose.setVar (by decide) hP1
  have heng2 : EngineArrays n W E Deg ER ID BH BV BN sigma2 := by
    refine ⟨by simpa [sigma2] using heng1.n_eq,
      by simpa [sigma2] using heng1.elm_eq,
      by simpa [sigma2] using heng1.deg_eq,
      by simpa [sigma2] using heng1.rank_eq,
      by simpa [sigma2] using heng1.idg_eq,
      by simpa [sigma2] using heng1.head_eq,
      by simpa [sigma2] using heng1.val_eq,
      by simpa [sigma2] using heng1.next_eq⟩
  have hw2 : sigma2.vars "w" = z := by simp [sigma2]
  obtain ⟨sigma3, r3, hP3, heng3, -, inTail, Ain, hrowIn, htail3, hAin3⟩ :=
    (hpin ⟨z, hz⟩ E Deg ER ID BH BV BN).run ⟨hP2, heng2, hw2⟩
  have hsave3 : sigma3.arrs "vsave" =
      arrOf 4 (fratSavedValues S.card (root : ℕ) outTail p) := by
    rw [r3.frame_arr "vsave" hframes.save]
    simpa [sigma2] using hsave1
  obtain ⟨sigma4, r4, hP4, heng4, hc4, hroot4, hend4, hfj4⟩ :=
    fratRestoreState_run hclose hP3 heng3 hsave3 hB4
      hScard hrootB houtTailB hpB
  have hvrow4 : sigma4.arrs "vrow" = tau.arrs "vrow" := by
    rw [r4.frame_arr "vrow" (by decide), r3.frame_arr "vrow" hframes.vrow,
      r2.frame_arr "vrow" (by decide), r1.frame_arr "vrow" (by decide)]
    rfl
  have hvout4 : sigma4.arrs "vout" = tau.arrs "vout" := by
    rw [r4.frame_arr "vout" (by decide), r3.frame_arr "vout" hframes.vout,
      r2.frame_arr "vout" (by decide), r1.frame_arr "vout" (by decide)]
    rfl
  have hstf4 : sigma4.arrs "stf" = tau.arrs "stf" := by
    rw [r4.frame_arr "stf" (by decide), r3.frame_arr "stf" hframes.stamp,
      r2.frame_arr "stf" (by decide), r1.frame_arr "stf" (by decide)]
    rfl
  have hvin4 : sigma4.arrs "vin" = arrOf n Ain := by
    rw [r4.frame_arr "vin" (by decide)]
    exact hAin3
  have htail4 : sigma4.vars "vtail" = inTail := by
    rw [r4.frame_var "vtail" (by decide)]
    exact htail3
  have hsaveLen4 : (sigma4.arrs "vsave").length = 4 := by
    rw [r4.frame_arr "vsave" (by decide), hsave3, length_arrOf]
  have hfill4 : RowFillAcc "vrow" n (fratNum D root) S sigma4 := by
    exact ⟨hSsub, Acur, hvrow4.trans hAcur, hc4, hnd, hmem⟩
  have hmarks4 : Marks "stf" n 1 ({(root : ℕ)} ∪ S) (fun _ => 0) sigma4 :=
    houter.marks.of_eq hstf4
  have hinner4 : VirtualInnerAcc n W P root (fratNum D root)
      outTail p Aout Ain inTail E Deg ER ID BH BV BN S sigma4 :=
    ⟨hfill4, hP4, heng4, hvout4.trans houter.out_eq, hvin4,
      hsaveLen4, htail4, hroot4, hend4, hfj4⟩
  have hfeCap : ∀ q, q < inTail →
      fratFe (root : ℕ) (Ain q) ⊆ fratNum D root := by
    intro q hq y hy
    rw [fratNum, Finset.mem_biUnion]
    refine ⟨z, (hout.mem_valSet_iff z).2 ⟨p, hp, rfl⟩, ?_⟩
    rw [fratStep, inValSet_of_lt D hz, Finset.mem_biUnion]
    exact ⟨Ain q, (hrowIn.mem_valSet_iff (Ain q)).2 ⟨q, hq, rfl⟩, hy⟩
  obtain ⟨sigma5, K5, r5, hK5, hmarks5, hacc5⟩ :=
    virtualInnerBuffer_run (D := D) (root := root) (z := z) hz hclose
      (by omega) hnB hCap hrowIn hfeCap hmarks4 hinner4
  have houter5 : VirtualOuterAcc n W P D root (fratNum D root)
      outTail Aout (p + 1) E Deg ER ID BH BV BN sigma5 := by
    refine ⟨?_, ?_, hacc5.persistent, hacc5.engine, hacc5.out_eq,
      by rw [hacc5.in_eq, length_arrOf], hacc5.save_length,
      hacc5.root_eq, hacc5.end_eq⟩
    · simpa only [S, z, bufferAcc_succ] using hmarks5
    · simpa only [S, z, bufferAcc_succ] using hacc5.fill
  refine ⟨sigma5, 12 + (2 + (kin z + (12 + K5))), ?_, ?_, hacc5.outer_eq,
    houter5⟩
  · simpa only [virtualFratInner, sigma0, z] using
      r1.seq (r2.seq (r3.seq (r4.seq r5)))
  · have htailCard : inTail =
        (D.inN ⟨Aout p, hout.value_lt p hp⟩).card := by
      simpa [z] using hrowIn.tail_eq
    rw [htailCard] at hK5
    dsimp [z]
    omega

/-! ## The complete generic outer scan -/

/-- Totalized charge of one nested incoming-provider call. -/
noncomputable def virtualFratRawBudget {n : ℕ} (kin : ℕ → ℕ)
    (D : Orientation n) (z : ℕ) : ℕ :=
  if hz : z < n then kin z + 26 * (D.inN ⟨z, hz⟩).card + 32 else 0

@[simp] theorem virtualFratRawBudget_of_lt {n : ℕ} (kin : ℕ → ℕ)
    (D : Orientation n) {z : ℕ} (hz : z < n) :
    virtualFratRawBudget kin D z =
      kin z + 26 * (D.inN ⟨z, hz⟩).card + 32 := by
  simp [virtualFratRawBudget, hz]

/-- Per-outgoing-slot charge, including the reusable-buffer scanner. -/
noncomputable def virtualFratSlotBudget {n : ℕ} (kin : ℕ → ℕ)
    (D : Orientation n) (z : ℕ) : ℕ :=
  virtualFratRawBudget kin D z + 11

@[simp] theorem virtualFratSlotBudget_of_lt {n : ℕ} (kin : ℕ → ℕ)
    (D : Orientation n) {z : ℕ} (hz : z < n) :
    virtualFratSlotBudget kin D z =
      kin z + 26 * (D.inN ⟨z, hz⟩).card + 43 := by
  rw [virtualFratSlotBudget, virtualFratRawBudget_of_lt kin D hz]

/-- Lift the checked nested call through the exact outgoing row. -/
theorem virtualFratOuter_run {B n W : ℕ} {P : Env → Prop}
    {provideIn : Com} {kin : ℕ → ℕ}
    {D : Orientation n} {root : Fin n} {outTail : ℕ}
    {Aout : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (hclose : FratScratchClosed P) (hframes : FratIncomingFrames provideIn)
    (hB4 : 3 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W (fun w => D.inN w) P "vin" provideIn kin)
    (hout : SetRowRep (outSet D root) outTail Aout)
    (houter0 : VirtualOuterAcc n W P D root (fratNum D root)
      outTail Aout 0 E Deg ER ID BH BV BN sigma) :
    ∃ sigma' K,
      Run B (bufferScan "vout" "fj" "fend" "u"
        (virtualFratInner provideIn)) sigma sigma' K ∧
      K ≤ (∑ z ∈ valSet (outSet D root),
        virtualFratSlotBudget kin D z) + 6 ∧
      VirtualOuterAcc n W P D root (fratNum D root)
        outTail Aout outTail E Deg ER ID BH BV BN sigma' := by
  let costs : ℕ → ℕ := fun p => virtualFratRawBudget kin D (Aout p)
  let I : ℕ → Env → Prop := fun p tau =>
    VirtualOuterAcc n W P D root (fratNum D root)
      outTail Aout p E Deg ER ID BH BV BN tau ∧
      tau.vars "fend" = outTail ∧ tau.vars "fj" = p ∧ p ≤ outTail
  have hstart : I 0 (sigma.setVar "fj" 0) := by
    refine ⟨houter0.setVarPrivate hclose (by decide) (by decide) (by decide)
      (by decide) 0, ?_, by simp, by omega⟩
    simpa using houter0.end_eq
  obtain ⟨sigma', K, hr, hK, hI⟩ :=
    bufferScanC_run (B := B) (len := n) (hi := outTail)
      (src := "vout") (j := "fj") (jend := "fend") (u := "u")
      (body := virtualFratInner provideIn)
      (costs := costs) (A := Aout) (I := I) (sigma := sigma)
      (by decide) (lt_of_le_of_lt hout.tail_le hnB) (by omega) hout.tail_le
      houter0.end_eq
      (fun _ _ h => h.1.out_eq)
      (fun p hp => lt_trans (hout.value_lt p hp) hnB)
      (fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
      (by
        intro p tau hIp hp
        obtain ⟨tau', K', hr', hK', hfj', houter'⟩ :=
          virtualFratInner_run hclose hframes hB4 hnB hpin hout hp
            hIp.2.2.1 hIp.1
        refine ⟨tau', K', hr', ?_, hfj', ?_⟩
        · simpa only [costs, virtualFratRawBudget_of_lt kin D
            (hout.value_lt p hp)] using hK'
        refine ⟨houter'.setVarPrivate hclose (by decide) (by decide) (by decide)
          (by decide) (p + 1), ?_, by simp, by omega⟩
        rw [vars_setVar, if_neg (by decide)]
        exact houter'.end_eq)
      hstart
  have hsum := hout.sum_slots (virtualFratSlotBudget kin D)
  have hcostEq : (∑ p ∈ Finset.range outTail, (costs p + 11)) =
      ∑ z ∈ valSet (outSet D root), virtualFratSlotBudget kin D z := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [costs, virtualFratSlotBudget]
  rw [hcostEq] at hK
  exact ⟨sigma', K, hr, hK, hI.1⟩

/-! ## Complete compositional provider -/

/-- Total charge of one fraternity row generated from two earlier virtual
orientation providers. -/
noncomputable def virtualFratCost {n : ℕ} (kout kin : ℕ → ℕ)
    (D : Orientation n) (w : ℕ) : ℕ :=
  if hw : w < n then
    kout w +
      (∑ z ∈ valSet (outSet D ⟨w, hw⟩), virtualFratSlotBudget kin D z) +
      14 * (fratNbrs D ⟨w, hw⟩).card + 30
  else 0

@[simp] theorem virtualFratCost_of_lt {n : ℕ} (kout kin : ℕ → ℕ)
    (D : Orientation n) {w : ℕ} (hw : w < n) :
    virtualFratCost kout kin D w =
      kout w +
        (∑ z ∈ valSet (outSet D ⟨w, hw⟩), virtualFratSlotBudget kin D z) +
        14 * (fratNbrs D ⟨w, hw⟩).card + 30 := by
  simp [virtualFratCost, hw]

/-- Two exact orientation-row providers compose to an exact fraternity-row
provider.  The resulting persistent predicate includes only carrier-sized
private buffers; the earlier providers' own persistent state is retained as
`P`. -/
theorem virtualFratProvidesSetRows {B n W : ℕ} {P : Env → Prop}
    {provideOut provideIn : Com} {kout kin : ℕ → ℕ} {D : Orientation n}
    (hclose : FratScratchClosed P)
    (hfin : FratIncomingFrames provideIn)
    (hfout : FratOutgoingFrames provideOut)
    (hB4 : 3 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W (fun w => D.inN w)
      P "vin" provideIn kin)
    (hpout : ProvidesSetRows B n W (fun w => outSet D w)
      P "vout" provideOut kout) :
    ProvidesSetRows B n W (fratNbrs D) (FratWorkspace n P) "vrow"
      (virtualFratProvide provideOut provideIn)
      (virtualFratCost kout kin D) := by
  classical
  intro root E Deg ER ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  have hrootB : (root : ℕ) < B := lt_trans root.isLt hnB
  obtain ⟨sigma1, r1, hP1, heng1, hstable1,
      outTail, Aout, hrowOut, htail1, hAout1⟩ :=
    (hpout root E Deg ER ID BH BV BN).run ⟨hmem.persistent, heng, hw⟩
  have hw1 : sigma1.vars "w" = (root : ℕ) := by
    rw [hstable1.w_eq, hw]
  have ew1 : (Expr.var "w").evalB B sigma1 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "w") (σ := sigma1)
      (by rw [hw1]; exact hrootB)
    rwa [hw1] at h
  let sigma2 := sigma1.setVar "froot" (root : ℕ)
  have r2 : Run B (.assign "froot" (.var "w")) sigma1 sigma2 2 := Run.assign ew1
  have houtTailB : outTail < B := lt_of_le_of_lt hrowOut.tail_le hnB
  have evtail2 : (Expr.var "vtail").evalB B sigma2 = some outTail := by
    have htail2 : sigma2.vars "vtail" = outTail := by simpa [sigma2] using htail1
    have h := evalB_var (B := B) (x := "vtail") (σ := sigma2)
      (by rw [htail2]; exact houtTailB)
    rwa [htail2] at h
  let sigma3 := sigma2.setVar "fend" outTail
  have r3 : Run B (.assign "fend" (.var "vtail")) sigma2 sigma3 2 :=
    Run.assign evtail2
  let sigma4 := sigma3.setVar "c" 0
  have r4 : Run B (.assign "c" (.lit 0)) sigma3 sigma4 2 :=
    Run.assign (evalB_lit (by omega))
  have ew4 : (Expr.var "w").evalB B sigma4 = some (root : ℕ) := by
    simpa [sigma4, sigma3, sigma2] using ew1
  have hstf1 : sigma1.arrs "stf" = arrOf n (fun _ => 0) := by
    rw [r1.frame_arr "stf" hfout.stamp]
    exact hmem.stamp_zero
  have hstf4 : sigma4.arrs "stf" = arrOf n (fun _ => 0) := by
    simpa [sigma4, sigma3, sigma2] using hstf1
  have hrootSlot : (root : ℕ) < (sigma4.arrs "stf").length := by
    rw [hstf4, length_arrOf]
    exact root.isLt
  let sigma5 := sigma4.setArr "stf" (root : ℕ) 1
  have r5 : Run B (.store "stf" (.var "w") (.lit 1)) sigma4 sigma5 3 :=
    Run.store ew4 (evalB_lit (by omega)) hrootSlot
  have hstf5 : sigma5.arrs "stf" =
      arrOf n (fun k => if k = (root : ℕ) then 1 else 0) := by
    simp [sigma5, hstf4, set_arrOf]
  have hmarks5 : Marks "stf" n 1
      ({(root : ℕ)} ∪ bufferAcc 0 Aout (fratStep D (root : ℕ)))
      (fun _ => 0) sigma5 := by
    refine ⟨fun k => if k = (root : ℕ) then 1 else 0, hstf5, ?_⟩
    intro k hk
    simp
  have hvrow1 : (sigma1.arrs "vrow").length = n := by
    rw [r1.frame_arr "vrow" hfout.vrow]
    exact hmem.vrow_length
  have hvrow5 : (sigma5.arrs "vrow").length = n := by
    simpa [sigma5, sigma4, sigma3, sigma2] using hvrow1
  obtain ⟨A0, hA0⟩ := Lax3Proofs.RamDriver.exists_arrOf hvrow5
  have hfill5 : RowFillAcc "vrow" n (fratNum D root)
      (bufferAcc 0 Aout (fratStep D (root : ℕ))) sigma5 := by
    refine ⟨by simp, A0, hA0, by simp [sigma5, sigma4], ?_, ?_⟩
    · simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
    · intro z
      simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
  have hvin1 : (sigma1.arrs "vin").length = n := by
    rw [r1.frame_arr "vin" hfout.vin]
    exact hmem.vin_length
  have hvin5 : (sigma5.arrs "vin").length = n := by
    simpa [sigma5, sigma4, sigma3, sigma2] using hvin1
  have hsave1 : (sigma1.arrs "vsave").length = 4 := by
    rw [r1.frame_arr "vsave" hfout.save]
    exact hmem.save_length
  have hsave5 : (sigma5.arrs "vsave").length = 4 := by
    simpa [sigma5, sigma4, sigma3, sigma2] using hsave1
  have hP5 : P sigma5 :=
    hclose.setStamp
      (hclose.setVar (by decide)
        (hclose.setVar (by decide) (hclose.setVar (by decide) hP1)))
  have heng5 : EngineArrays n W E Deg ER ID BH BV BN sigma5 := by
    refine ⟨by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.n_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.elm_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.deg_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.rank_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.idg_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.head_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.val_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.next_eq⟩
  have hout5 : sigma5.arrs "vout" = arrOf n Aout := by
    simpa [sigma5, sigma4, sigma3, sigma2] using hAout1
  have houter5 : VirtualOuterAcc n W P D root (fratNum D root)
      outTail Aout 0 E Deg ER ID BH BV BN sigma5 := by
    refine ⟨hmarks5, hfill5, hP5, heng5, hout5, hvin5, hsave5, ?_, ?_⟩
    · simp [sigma5, sigma4, sigma3, sigma2]
    · simp [sigma5, sigma4, sigma3]
  obtain ⟨sigma6, K6, r6, hK6, houter6⟩ :=
    virtualFratOuter_run hclose hfin hB4 hnB hpin hrowOut houter5
  have hfull : bufferAcc outTail Aout (fratStep D (root : ℕ)) =
      fratNum D root := by
    simpa only [fratNum] using
      bufferAcc_eq_biUnion_valSet hrowOut (fratStep D (root : ℕ))
  have hmarks6 := houter6.marks
  have hfill6 := houter6.fill
  rw [hfull, fratNum_eq D root] at hmarks6 hfill6
  obtain ⟨Arow, hArow6, hc6, hrow⟩ := hfill6.toSetRowRep
  obtain ⟨g, hstf6, hg⟩ := hmarks6
  obtain ⟨sigma7, K7, r7, hK7, hclear7⟩ :=
    stampBuffer_run (B := B) (n := n) (tail := (fratNbrs D root).card)
      (b := 0) (src := "vrow") (j := "fc") (jend := "c")
      (u := "u") (s := "stf") (S := fratNbrs D root) (A := Arow)
      (g := g) (sigma := sigma6) (by decide) (by decide) (by decide)
      (by decide) (by omega) hnB (by omega) hrow hc6 hArow6 hstf6
  have hP7 : P sigma7 := by
    apply hclose.run r7
    · intro a ha
      intro han
      subst a
      simpa [bufferScan, Lax3Proofs.RamDriverAugment.scanBody, Csr.scan,
        Com.wvars] using ha
    · intro a ha
      simp [bufferScan, Lax3Proofs.RamDriverAugment.scanBody, Csr.scan,
        Com.warrs] at ha
      exact Or.inr (Or.inl ha)
    · decide
    · decide
    · exact houter6.persistent
  obtain ⟨g7, hstf7, hg7⟩ := hclear7
  have hg7root : ∀ k < n,
      g7 k = if k = (root : ℕ) then 1 else 0 := by
    intro k hk
    rw [hg7 k hk, hg k hk]
    by_cases hkS : k ∈ valSet (fratNbrs D root)
    · have hkr : k ≠ (root : ℕ) := by
        intro hkr
        apply root_not_mem_fratVal root
        simpa [hkr] using hkS
      simp [hkS, hkr]
    · simp [hkS]
  have hstf7root : sigma7.arrs "stf" =
      arrOf n (fun k => if k = (root : ℕ) then 1 else 0) :=
    hstf7.trans (arrOf_congr hg7root)
  have hfroot7 : sigma7.vars "froot" = (root : ℕ) := by
    rw [r7.frame_var "froot" (by decide)]
    exact houter6.root_eq
  have efroot7 : (Expr.var "froot").evalB B sigma7 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "froot") (σ := sigma7)
      (by rw [hfroot7]; exact hrootB)
    rwa [hfroot7] at h
  let sigma8 := sigma7.setVar "u" (root : ℕ)
  have r8 : Run B (.assign "u" (.var "froot")) sigma7 sigma8 2 :=
    Run.assign efroot7
  have hP8 : P sigma8 := hclose.setVar (by decide) hP7
  have eu8 : (Expr.var "u").evalB B sigma8 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "u") (σ := sigma8)
      (by simp [sigma8, hrootB])
    simpa [sigma8] using h
  have hrootSlot8 : (root : ℕ) < (sigma8.arrs "stf").length := by
    rw [arrs_setVar, hstf7root, length_arrOf]
    exact root.isLt
  let sigma9 := sigma8.setArr "stf" (root : ℕ) 0
  have r9 : Run B (.store "stf" (.var "u") (.lit 0)) sigma8 sigma9 3 :=
    Run.store eu8 (evalB_lit (by omega)) hrootSlot8
  have hP9 : P sigma9 := hclose.setStamp hP8
  have hstf9 : sigma9.arrs "stf" = arrOf n (fun _ => 0) := by
    change (sigma8.setArr "stf" (root : ℕ) 0).arrs "stf" =
      arrOf n (fun _ => 0)
    rw [arrs_setArr, if_pos rfl, arrs_setVar, hstf7root, set_arrOf]
    apply arrOf_congr
    intro k hk
    by_cases hkr : k = (root : ℕ) <;> simp [hkr]
  have hfroot9 : sigma9.vars "froot" = (root : ℕ) := by
    simp [sigma9, sigma8, hfroot7]
  have efroot9 : (Expr.var "froot").evalB B sigma9 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "froot") (σ := sigma9)
      (by rw [hfroot9]; exact hrootB)
    rwa [hfroot9] at h
  let sigma10 := sigma9.setVar "w" (root : ℕ)
  have r10 : Run B (.assign "w" (.var "froot")) sigma9 sigma10 2 :=
    Run.assign efroot9
  have hP10 : P sigma10 := hclose.setVar (by decide) hP9
  have hc7 : sigma7.vars "c" = (fratNbrs D root).card := by
    rw [r7.frame_var "c" (by decide)]
    exact hc6
  have hc10 : sigma10.vars "c" = (fratNbrs D root).card := by
    simpa [sigma10, sigma9, sigma8] using hc7
  have hcardB : (fratNbrs D root).card < B :=
    lt_of_le_of_lt hrow.tail_le hnB
  have ec10 : (Expr.var "c").evalB B sigma10 =
      some (fratNbrs D root).card := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma10)
      (by rw [hc10]; exact hcardB)
    rwa [hc10] at h
  let sigma11 := sigma10.setVar "vtail" (fratNbrs D root).card
  have r11 : Run B (.assign "vtail" (.var "c")) sigma10 sigma11 2 :=
    Run.assign ec10
  have hP11 : P sigma11 := hclose.setVar (by decide) hP10
  have rAll : Run B (virtualFratProvide provideOut provideIn) sigma sigma11
      (kout (root : ℕ) +
        (2 + (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2)))))))))) := by
    simpa only [virtualFratProvide] using
      r1.seq (r2.seq (r3.seq (r4.seq (r5.seq
        (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq r11)))))))))
  have hcost : kout (root : ℕ) +
        (2 + (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2))))))))) ≤
      virtualFratCost kout kin D (root : ℕ) := by
    rw [virtualFratCost_of_lt kout kin D root.isLt]
    have hroot : (⟨(root : ℕ), root.isLt⟩ : Fin n) = root := Fin.ext rfl
    rw [hroot]
    omega
  have heng7 : EngineArrays n W E Deg ER ID BH BV BN sigma7 := by
    refine ⟨by rw [r7.frame_var "n" (by decide)]; exact houter6.engine.n_eq,
      by rw [r7.frame_arr "elm" (by decide)]; exact houter6.engine.elm_eq,
      by rw [r7.frame_arr "deg" (by decide)]; exact houter6.engine.deg_eq,
      by rw [r7.frame_arr "rnk" (by decide)]; exact houter6.engine.rank_eq,
      by rw [r7.frame_arr "idg" (by decide)]; exact houter6.engine.idg_eq,
      by rw [r7.frame_arr "bh" (by decide)]; exact houter6.engine.head_eq,
      by rw [r7.frame_arr "bv" (by decide)]; exact houter6.engine.val_eq,
      by rw [r7.frame_arr "bn" (by decide)]; exact houter6.engine.next_eq⟩
  have heng11 : EngineArrays n W E Deg ER ID BH BV BN sigma11 := by
    refine ⟨by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.n_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.elm_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.deg_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.rank_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.idg_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.head_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.val_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.next_eq⟩
  have hvout7 : sigma7.arrs "vout" = arrOf n Aout := by
    rw [r7.frame_arr "vout" (by decide)]
    exact houter6.out_eq
  have hvin7 : (sigma7.arrs "vin").length = n := by
    rw [congrArg List.length (r7.frame_arr "vin" (by decide))]
    exact houter6.vin_length
  have hvrow7 : sigma7.arrs "vrow" = arrOf n Arow := by
    rw [r7.frame_arr "vrow" (by decide)]
    exact hArow6
  have hsave7 : (sigma7.arrs "vsave").length = 4 := by
    rw [congrArg List.length (r7.frame_arr "vsave" (by decide))]
    exact houter6.save_length
  have hmem11 : FratWorkspace n P sigma11 := by
    refine ⟨hP11, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [sigma11, sigma10, sigma9, sigma8] using
        congrArg List.length hvout7
    · simpa [sigma11, sigma10, sigma9, sigma8] using hvin7
    · simpa [sigma11, sigma10, sigma9, sigma8] using
        congrArg List.length hvrow7
    · simpa [sigma11, sigma10, sigma9, sigma8] using hsave7
    · simpa [sigma11, sigma10] using hstf9
  have hstable11 : ProviderStable sigma sigma11 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply rAll.frame_var "n"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan, fratGuard,
        rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.n, hfin.stable.n]
    · calc
        sigma11.vars "w" = (root : ℕ) := by simp [sigma11, sigma10]
        _ = sigma.vars "w" := hw.symm
    · apply rAll.frame_var "i"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan, fratGuard,
        rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.i, hfin.stable.i]
    · apply rAll.frame_var "sp"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan, fratGuard,
        rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.sp, hfin.stable.sp]
    · apply rAll.frame_var "ls"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan, fratGuard,
        rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.ls, hfin.stable.ls]
    · apply rAll.frame_var "cnt"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan, fratGuard,
        rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.cnt, hfin.stable.cnt]
    · apply rAll.frame_var "mind"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan, fratGuard,
        rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.mind, hfin.stable.mind]
    · apply rAll.frame_var "kmax"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan, fratGuard,
        rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.kmax, hfin.stable.kmax]
  refine ⟨sigma11,
    kout (root : ℕ) +
      (2 + (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2))))))))),
    rAll, hcost, hmem11, heng11, hstable11,
    (fratNbrs D root).card, Arow, hrow, ?_, ?_⟩
  · simp [sigma11]
  · simpa [sigma11, sigma10, sigma9, sigma8] using hvrow7

/-! ## Axiom audit for the representation boundary -/

#print axioms fratWorkspace_engineClosed
#print axioms fratWorkspace_engineRunClosed

end Lax3Proofs.Refine.OrderVirtualFrat
