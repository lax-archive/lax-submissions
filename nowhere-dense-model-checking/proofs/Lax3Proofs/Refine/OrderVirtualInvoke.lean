import Lax3Proofs.Refine.OrderVirtualAugGuard

/-!
# Calling a virtual row provider inside another provider

The recursive augmentation provider repeatedly asks a child provider for a
row while its own output count and stamp arrays are live.  This module gives
that call one verified wrapper: save the output count, restore the requested
root, run the child, remember its returned tail, restore the count and root,
and expose the child's exact row in `vtmp`.
-/

namespace Lax3Proofs.Refine.OrderVirtualInvoke

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow

/-- Parent scratch operations under which the child's persistent state must
remain closed. -/
structure AugInvokeClosed (P : Env → Prop) : Prop where
  setVar : ∀ {sigma : Env} {a : String} {x : ℕ}, a ≠ "n" →
    P sigma → P (sigma.setVar a x)
  setSave : ∀ {sigma : Env} {p x : ℕ},
    P sigma → P (sigma.setArr "avsave" p x)

/-- A nested child must leave the parent result and its three live stamps
untouched, as well as the scalar and one-cell array used across the call. -/
structure AugInvokeFrames (provide : Com) : Prop where
  root : "avroot" ∉ provide.wvars
  output : "vrow" ∉ provide.warrs
  adjacency : "sta" ∉ provide.warrs
  opposite : "std" ∉ provide.warrs
  emitted : "ste" ∉ provide.warrs
  save : "avsave" ∉ provide.warrs

def virtualInvoke (provide : Com) : Com :=
  .seq (.store "avsave" (.lit 0) (.var "c"))
    (.seq (.assign "w" (.var "avroot"))
      (.seq provide
        (.seq (.assign "avend" (.var "vtail"))
          (.seq (.assign "c" (.get "avsave" (.lit 0)))
            (.assign "w" (.var "avroot"))))))

/-- One wrapped child call preserves the parent live arrays and returns an
exact row in `vtmp`, with `avend` holding its live prefix. -/
theorem virtualInvoke_run {B n W count : ℕ} {P : Env → Prop}
    {S : Fin n → Finset (Fin n)} {provide : Com} {kappa : ℕ → ℕ}
    {root : Fin n} {E D R ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (hclose : AugInvokeClosed P) (hframes : AugInvokeFrames provide)
    (hB1 : 1 < B) (hnB : n < B)
    (hp : ProvidesSetRows B n W S P "vtmp" provide kappa)
    (hP : P sigma) (heng : EngineArrays n W E D R ID BH BV BN sigma)
    (hw : sigma.vars "w" = (root : ℕ))
    (hroot : sigma.vars "avroot" = (root : ℕ))
    (hc : sigma.vars "c" = count) (hcountB : count < B)
    (hsave : (sigma.arrs "avsave").length = 1) :
    ∃ tau tail A,
      Run B (virtualInvoke provide) sigma tau (kappa (root : ℕ) + 12) ∧
      P tau ∧ EngineArrays n W E D R ID BH BV BN tau ∧
      ProviderStable sigma tau ∧
      SetRowRep (S root) tail A ∧
      tau.arrs "vtmp" = arrOf n A ∧ tau.vars "avend" = tail ∧
      tau.vars "c" = count ∧ tau.vars "w" = (root : ℕ) ∧
      tau.vars "avroot" = (root : ℕ) ∧
      (tau.arrs "avsave").length = 1 ∧
      tau.arrs "vrow" = sigma.arrs "vrow" ∧
      tau.arrs "sta" = sigma.arrs "sta" ∧
      tau.arrs "std" = sigma.arrs "std" ∧
      tau.arrs "ste" = sigma.arrs "ste" := by
  have hrootB : (root : ℕ) < B := lt_trans root.isLt hnB
  obtain ⟨As, hAs⟩ := Lax3Proofs.RamDriver.exists_arrOf hsave
  have ec : (Expr.var "c").evalB B sigma = some count := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma) (by rw [hc]; exact hcountB)
    rwa [hc] at h
  have hslot : 0 < (sigma.arrs "avsave").length := by omega
  let sigma1 := sigma.setArr "avsave" 0 count
  have r1 : Run B (.store "avsave" (.lit 0) (.var "c")) sigma sigma1 3 :=
    Run.store (evalB_lit (by omega)) ec hslot
  have hP1 : P sigma1 := hclose.setSave hP
  have heng1 : EngineArrays n W E D R ID BH BV BN sigma1 := by
    exact ⟨by simpa [sigma1] using heng.n_eq,
      by simpa [sigma1] using heng.elm_eq, by simpa [sigma1] using heng.deg_eq,
      by simpa [sigma1] using heng.rank_eq, by simpa [sigma1] using heng.idg_eq,
      by simpa [sigma1] using heng.head_eq, by simpa [sigma1] using heng.val_eq,
      by simpa [sigma1] using heng.next_eq⟩
  have eroot1 : (Expr.var "avroot").evalB B sigma1 = some (root : ℕ) := by
    have hr1 : sigma1.vars "avroot" = (root : ℕ) := by simpa [sigma1] using hroot
    have h := evalB_var (B := B) (x := "avroot") (σ := sigma1)
      (by rw [hr1]; exact hrootB)
    rwa [hr1] at h
  let sigma2 := sigma1.setVar "w" (root : ℕ)
  have r2 : Run B (.assign "w" (.var "avroot")) sigma1 sigma2 2 :=
    Run.assign eroot1
  have hP2 : P sigma2 := hclose.setVar (by decide) hP1
  have heng2 : EngineArrays n W E D R ID BH BV BN sigma2 := by
    exact ⟨by simpa [sigma2] using heng1.n_eq,
      by simpa [sigma2] using heng1.elm_eq, by simpa [sigma2] using heng1.deg_eq,
      by simpa [sigma2] using heng1.rank_eq, by simpa [sigma2] using heng1.idg_eq,
      by simpa [sigma2] using heng1.head_eq, by simpa [sigma2] using heng1.val_eq,
      by simpa [sigma2] using heng1.next_eq⟩
  have hw2 : sigma2.vars "w" = (root : ℕ) := by simp [sigma2]
  obtain ⟨sigma3, r3, hP3, heng3, hstable3, tail, A, hrow, htail3, htmp3⟩ :=
    (hp root E D R ID BH BV BN).run ⟨hP2, heng2, hw2⟩
  have htailB : tail < B := lt_of_le_of_lt hrow.tail_le hnB
  have etail3 : (Expr.var "vtail").evalB B sigma3 = some tail := by
    have h := evalB_var (B := B) (x := "vtail") (σ := sigma3)
      (by rw [htail3]; exact htailB)
    rwa [htail3] at h
  let sigma4 := sigma3.setVar "avend" tail
  have r4 : Run B (.assign "avend" (.var "vtail")) sigma3 sigma4 2 :=
    Run.assign etail3
  have hP4 : P sigma4 := hclose.setVar (by decide) hP3
  have heng4 : EngineArrays n W E D R ID BH BV BN sigma4 := by
    exact ⟨by simpa [sigma4] using heng3.n_eq,
      by simpa [sigma4] using heng3.elm_eq, by simpa [sigma4] using heng3.deg_eq,
      by simpa [sigma4] using heng3.rank_eq, by simpa [sigma4] using heng3.idg_eq,
      by simpa [sigma4] using heng3.head_eq, by simpa [sigma4] using heng3.val_eq,
      by simpa [sigma4] using heng3.next_eq⟩
  have hsave1 : sigma1.arrs "avsave" = arrOf 1 (upd As 0 count) := by
    simp [sigma1, hAs, set_arrOf_eq_upd]
  have hsave3 : sigma3.arrs "avsave" = arrOf 1 (upd As 0 count) := by
    rw [r3.frame_arr "avsave" hframes.save]
    simpa [sigma2] using hsave1
  have esave4 : (Expr.get "avsave" (.lit 0)).evalB B sigma4 = some count := by
    apply evalB_get (evalB_lit (by omega))
    · rw [arrs_setVar, hsave3, getElem?_arrOf (upd As 0 count) (by omega)]
      simp [upd]
    · exact hcountB
  let sigma5 := sigma4.setVar "c" count
  have r5 : Run B (.assign "c" (.get "avsave" (.lit 0))) sigma4 sigma5 3 :=
    Run.assign esave4
  have hP5 : P sigma5 := hclose.setVar (by decide) hP4
  have heng5 : EngineArrays n W E D R ID BH BV BN sigma5 := by
    exact ⟨by simpa [sigma5] using heng4.n_eq,
      by simpa [sigma5] using heng4.elm_eq, by simpa [sigma5] using heng4.deg_eq,
      by simpa [sigma5] using heng4.rank_eq, by simpa [sigma5] using heng4.idg_eq,
      by simpa [sigma5] using heng4.head_eq, by simpa [sigma5] using heng4.val_eq,
      by simpa [sigma5] using heng4.next_eq⟩
  have hroot3 : sigma3.vars "avroot" = (root : ℕ) := by
    rw [r3.frame_var "avroot" hframes.root]
    simpa [sigma2, sigma1] using hroot
  have eroot5 : (Expr.var "avroot").evalB B sigma5 = some (root : ℕ) := by
    have hr5 : sigma5.vars "avroot" = (root : ℕ) := by
      simpa [sigma5, sigma4] using hroot3
    have h := evalB_var (B := B) (x := "avroot") (σ := sigma5)
      (by rw [hr5]; exact hrootB)
    rwa [hr5] at h
  let sigma6 := sigma5.setVar "w" (root : ℕ)
  have r6 : Run B (.assign "w" (.var "avroot")) sigma5 sigma6 2 :=
    Run.assign eroot5
  have hP6 : P sigma6 := hclose.setVar (by decide) hP5
  have heng6 : EngineArrays n W E D R ID BH BV BN sigma6 := by
    exact ⟨by simpa [sigma6] using heng5.n_eq,
      by simpa [sigma6] using heng5.elm_eq, by simpa [sigma6] using heng5.deg_eq,
      by simpa [sigma6] using heng5.rank_eq, by simpa [sigma6] using heng5.idg_eq,
      by simpa [sigma6] using heng5.head_eq, by simpa [sigma6] using heng5.val_eq,
      by simpa [sigma6] using heng5.next_eq⟩
  have frameArr (a : String) (haSave : a ≠ "avsave") (haChild : a ∉ provide.warrs) :
      sigma6.arrs a = sigma.arrs a := by
    simp only [sigma6, sigma5, sigma4, arrs_setVar]
    rw [r3.frame_arr a haChild, arrs_setVar, arrs_setArr, if_neg haSave]
  have htmp6 : sigma6.arrs "vtmp" = arrOf n A := by
    simpa [sigma6, sigma5, sigma4] using htmp3
  have hsave6 : (sigma6.arrs "avsave").length = 1 := by
    rw [show sigma6.arrs "avsave" = sigma3.arrs "avsave" by
      simp [sigma6, sigma5, sigma4], hsave3, length_arrOf]
  have hstable6 : ProviderStable sigma sigma6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [sigma6, sigma5, sigma4, sigma2, sigma1] using hstable3.n_eq
    · simp [sigma6, hw]
    · simpa [sigma6, sigma5, sigma4, sigma2, sigma1] using hstable3.i_eq
    · simpa [sigma6, sigma5, sigma4, sigma2, sigma1] using hstable3.sp_eq
    · simpa [sigma6, sigma5, sigma4, sigma2, sigma1] using hstable3.ls_eq
    · simpa [sigma6, sigma5, sigma4, sigma2, sigma1] using hstable3.cnt_eq
    · simpa [sigma6, sigma5, sigma4, sigma2, sigma1] using hstable3.mind_eq
    · simpa [sigma6, sigma5, sigma4, sigma2, sigma1] using hstable3.kmax_eq
  refine ⟨sigma6, tail, A, ?_, hP6, heng6, hstable6, hrow, htmp6, ?_,
    by simp [sigma6, sigma5],
    by simp [sigma6], ?_, hsave6, ?_, ?_, ?_, ?_⟩
  · simpa only [virtualInvoke] using
      (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by omega)
  · simp [sigma6, sigma5, sigma4]
  · simpa [sigma6, sigma5, sigma4] using hroot3
  · exact frameArr "vrow" (by decide) hframes.output
  · exact frameArr "sta" (by decide) hframes.adjacency
  · exact frameArr "std" (by decide) hframes.opposite
  · exact frameArr "ste" (by decide) hframes.emitted

#print axioms virtualInvoke_run

end Lax3Proofs.Refine.OrderVirtualInvoke
