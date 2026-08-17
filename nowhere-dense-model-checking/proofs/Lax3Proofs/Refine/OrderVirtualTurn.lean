import Lax3Proofs.Refine.OrderVirtualTake

/-!
# One turn of the virtual greedy eliminator

This is the ordinary lazy-bucket turn with the resident CSR row replaced by
the verified row-provider boundary.  The three semantic cases are kept
separate below because their exact scalar effects are the credits used by the
amortized loop proof.
-/

namespace Lax3Proofs.Refine.OrderVirtualTurn

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamElim (Elim Buck)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualInit (virtualDegree)
open Lax3Proofs.Refine.OrderVirtualBucket (bucketExtra)
open Lax3Proofs.Refine.OrderVirtualEnsure
open Lax3Proofs.Refine.OrderVirtualTake

def virtualTakeChoice (provide : Com) : Com :=
  .ite (.eq (.get "deg" (.var "w")) (.var "mind"))
    (virtualElimVertex provide) .skip

def virtualAliveChoice (provide : Com) : Com :=
  .ite (.lt (.get "elm" (.var "w")) (.lit 1))
    (virtualTakeChoice provide) .skip

/-- The bucket turn after the capacity guard has run. -/
def virtualCoreTurn (provide : Com) : Com :=
  .ite (.eq (.get "bh" (.var "mind")) (.lit 0))
    (.assign "mind" (.add (.var "mind") (.lit 1)))
    (.seq (.assign "p" (.get "bh" (.var "mind")))
      (.seq (.assign "w" (.get "bv" (.var "p")))
        (.seq (.store "bh" (.var "mind") (.get "bn" (.var "p")))
          (.seq (.assign "ls" (.sub (.var "ls") (.lit 1)))
            (virtualAliveChoice provide)))))

structure VirtualBumpEffect (σ σ' : Env) (K : ℕ) : Prop where
  cost : K ≤ 30
  mind_eq : σ'.vars "mind" = σ.vars "mind" + 1
  ls_eq : σ'.vars "ls" = σ.vars "ls"
  sp_eq : σ'.vars "sp" = σ.vars "sp"
  cnt_eq : σ'.vars "cnt" = σ.vars "cnt"
  elm_eq : σ'.arrs "elm" = σ.arrs "elm"

structure VirtualStaleEffect (σ σ' : Env) (K : ℕ) : Prop where
  cost : K ≤ 40
  ls_pos : 0 < σ.vars "ls"
  mind_eq : σ'.vars "mind" = σ.vars "mind"
  ls_eq : σ'.vars "ls" = σ.vars "ls" - 1
  sp_eq : σ'.vars "sp" = σ.vars "sp"
  cnt_eq : σ'.vars "cnt" = σ.vars "cnt"
  elm_eq : σ'.arrs "elm" = σ.arrs "elm"

def VirtualTakeEffect (n : ℕ) (G : SimpleGraph (Fin n))
    (κ E : ℕ → ℕ) (σ σ' : Env) (K : ℕ) : Prop :=
  ∃ w < n, E w = 0 ∧
    K ≤ κ w + 47 * virtualDegree G w + 70 ∧
    σ'.vars "sp" ≤ σ.vars "sp" + virtualDegree G w ∧
    σ'.vars "ls" ≤ σ.vars "ls" - 1 + virtualDegree G w ∧
    σ'.vars "cnt" = σ.vars "cnt" + 1 ∧
    σ'.vars "mind" = σ.vars "mind" - 1 ∧
    σ'.vars "kmax" = max (σ.vars "kmax") (σ.vars "mind") ∧
    σ'.arrs "elm" = arrOf n (upd E w 1)

def VirtualCoreEffect (n : ℕ) (G : SimpleGraph (Fin n))
    (κ E : ℕ → ℕ) (σ σ' : Env) (K : ℕ) : Prop :=
  VirtualBumpEffect σ σ' K ∨ VirtualStaleEffect σ σ' K ∨
    VirtualTakeEffect n G κ E σ σ' K

/-- If the selected live vertex has a stale degree, the provider branch is
not entered. -/
theorem virtualSkipMin_spec (B : ℕ) (provide : Com) :
    Spec B (fun τ => τ.vars "w" < (τ.arrs "deg").length ∧
        (τ.arrs "deg").getD (τ.vars "w") 0 < B ∧
        τ.vars "w" < B ∧ τ.vars "mind" < B ∧
        (τ.arrs "deg").getD (τ.vars "w") 0 ≠ τ.vars "mind")
      (virtualTakeChoice provide)
      (fun τ τ' => τ' = τ) 6 := by
  rintro τ ⟨hlen, hval, hwB, hmB, hne⟩
  have hb : (Cond.eq (.get "deg" (.var "w")) (.var "mind")).evalB B τ =
      some false := by
    rw [evalB_condEq
      (RunStep.eval_get B τ "deg" (.var "w") (τ.vars "w")
        (evalB_var hwB) hlen hval)
      (evalB_var hmB)]
    simpa using hne
  exact ⟨τ, (Run.ite_false hb Run.skip).mono (by
    simp [virtualTakeChoice, Cond.size, Expr.size]), rfl⟩

/-- A machine-level stale head walks across both nested tests without ever
entering the provider. -/
theorem virtualAliveChoice_stale_spec (B : ℕ) (provide : Com) :
    Spec B (fun τ =>
        τ.vars "w" < (τ.arrs "elm").length ∧
        τ.vars "w" < (τ.arrs "deg").length ∧
        (τ.arrs "elm").getD (τ.vars "w") 0 < B ∧
        (τ.arrs "deg").getD (τ.vars "w") 0 < B ∧
        τ.vars "w" < B ∧ τ.vars "mind" < B ∧
        ¬ ((τ.arrs "elm").getD (τ.vars "w") 0 < 1 ∧
          (τ.arrs "deg").getD (τ.vars "w") 0 = τ.vars "mind"))
      (virtualAliveChoice provide)
      (fun τ τ' => τ' = τ) 12 := by
  rintro τ ⟨helmLen, hdegLen, helmB, hdegB, hwB, hmindB, hstale⟩
  have hget : (Expr.get "elm" (.var "w")).evalB B τ =
      some ((τ.arrs "elm").getD (τ.vars "w") 0) :=
    RunStep.eval_get B τ "elm" (.var "w") (τ.vars "w")
      (evalB_var hwB) helmLen helmB
  have hcond : (Cond.lt (.get "elm" (.var "w")) (.lit 1)).evalB B τ =
      some (decide ((τ.arrs "elm").getD (τ.vars "w") 0 < 1)) :=
    evalB_condLt hget (evalB_lit (by omega : 1 < B))
  by_cases halive : (τ.arrs "elm").getD (τ.vars "w") 0 < 1
  · have hne : (τ.arrs "deg").getD (τ.vars "w") 0 ≠ τ.vars "mind" :=
      fun heq => hstale ⟨halive, heq⟩
    have hcondTrue : (Cond.lt (.get "elm" (.var "w")) (.lit 1)).evalB B τ =
        some true := by
      simpa only [halive] using hcond
    obtain ⟨τ', hr, heq⟩ := (virtualSkipMin_spec B provide).run
      ⟨hdegLen, hdegB, hwB, hmindB, hne⟩
    subst τ'
    exact ⟨τ, (Run.ite_true hcondTrue hr).mono (by
      simp [virtualAliveChoice, Cond.size, Expr.size]), rfl⟩
  · have hcondFalse : (Cond.lt (.get "elm" (.var "w")) (.lit 1)).evalB B τ =
        some false := by
      simpa only [halive] using hcond
    exact ⟨τ, (Run.ite_false hcondFalse Run.skip).mono (by
      simp [virtualAliveChoice, Cond.size, Expr.size]), rfl⟩

/-- A genuine live minimum walks through both tests and then invokes the
verified extraction. -/
theorem virtualAliveChoice_take_spec {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n (bucketExtra n) G P provide κ)
    (hclosed : EngineClosed P) (hrunClosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B)
    {E D R ID BH BV BN : ℕ → ℕ} {w : Fin n} :
    Spec B
      (TakePre n G P E D R ID BH BV BN w)
      (virtualAliveChoice provide)
      (fun σ σ' =>
        VirtualElimInv n G P σ' ∧
        σ'.vars "sp" ≤ σ.vars "sp" + virtualDegree G (w : ℕ) ∧
        σ'.vars "ls" ≤ σ.vars "ls" + virtualDegree G (w : ℕ) ∧
        σ'.vars "cnt" = σ.vars "cnt" + 1 ∧
        σ'.vars "mind" = σ.vars "mind" - 1 ∧
        σ'.vars "kmax" = max (σ.vars "kmax") (σ.vars "mind") ∧
        σ'.arrs "elm" = arrOf n (upd E (w : ℕ) 1))
      (κ (w : ℕ) + 47 * virtualDegree G (w : ℕ) + 45) := by
  intro σ hpre
  have heng := hpre.arrays
  have helmlen : (σ.arrs "elm").length = n := by
    rw [heng.elm_eq, length_arrOf]
  have hdeglen : (σ.arrs "deg").length = n := heng.deg_length
  have hwB : σ.vars "w" < B := by rw [hpre.w_eq]; omega
  have hmindB : σ.vars "mind" < B := by
    have := hpre.mind_le
    omega
  have helmRead : (σ.arrs "elm").getD (σ.vars "w") 0 = E (w : ℕ) := by
    rw [hpre.w_eq, heng.elm_eq, getD_arrOf E w.isLt]
  have hdegRead : (σ.arrs "deg").getD (σ.vars "w") 0 = D (w : ℕ) := by
    rw [hpre.w_eq, heng.deg_eq, getD_arrOf D w.isLt]
  have helmVal : (σ.arrs "elm").getD (σ.vars "w") 0 = 0 := by
    rw [helmRead, hpre.alive]
  have helmB : (σ.arrs "elm").getD (σ.vars "w") 0 < B := by
    rw [helmVal]
    omega
  have hElmCond : (Cond.lt (.get "elm" (.var "w")) (.lit 1)).evalB B σ =
      some true := by
    rw [evalB_condLt
      (RunStep.eval_get B σ "elm" (.var "w") (σ.vars "w")
        (evalB_var hwB) (by rw [helmlen, hpre.w_eq]; exact w.isLt) helmB)
      (evalB_lit (by omega : 1 < B))]
    rw [helmVal]
    rfl
  have hdegVal : (σ.arrs "deg").getD (σ.vars "w") 0 = σ.vars "mind" := by
    rw [hdegRead, hpre.minimum]
  have hdegB : (σ.arrs "deg").getD (σ.vars "w") 0 < B := by
    rw [hdegVal]
    exact hmindB
  have hDegCond : (Cond.eq (.get "deg" (.var "w")) (.var "mind")).evalB B σ =
      some true := by
    rw [evalB_condEq
      (RunStep.eval_get B σ "deg" (.var "w") (σ.vars "w")
        (evalB_var hwB) (by rw [hdeglen, hpre.w_eq]; exact w.isLt) hdegB)
      (evalB_var hmindB)]
    rw [hdegVal]
    simp
  obtain ⟨σ', hr, hpost⟩ :=
    (virtualElimVertex_spec hp hclosed hrunClosed hB).run hpre
  refine ⟨σ', (Run.ite_true hElmCond (Run.ite_true hDegCond hr)).mono ?_, hpost⟩
  simp [virtualAliveChoice, virtualTakeChoice, Cond.size, Expr.size]
  omega

/-- An empty bucket advances the degree pointer by exactly one. -/
theorem virtualBump_run {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com}
    (hclosed : EngineClosed P) (hB : 3 * n + 3 < B)
    {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (hst : VirtualElimSt n G P E D R ID BH BV BN σ)
    (hcnt : σ.vars "cnt" < n) (hbh0 : BH (σ.vars "mind") = 0) :
    ∃ σ' K, Run B (virtualCoreTurn provide) σ σ' K ∧ K ≤ 30 ∧
      VirtualElimInv n G P σ' ∧
      σ'.vars "mind" = σ.vars "mind" + 1 ∧
      σ'.vars "ls" = σ.vars "ls" ∧
      σ'.vars "sp" = σ.vars "sp" ∧
      σ'.vars "cnt" = σ.vars "cnt" ∧
      σ'.arrs "elm" = σ.arrs "elm" := by
  obtain ⟨hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩ := hst
  obtain ⟨v₀, hv₀, hEv₀⟩ := helim.exists_alive hcnt
  have hmindn : σ.vars "mind" < n := helim.mind_lt hv₀ hEv₀
  have hbhlen : (σ.arrs "bh").length = n + 1 := by
    rw [heng.head_eq, length_arrOf]
  have hbhv : (σ.arrs "bh").getD (σ.vars "mind") 0 =
      BH (σ.vars "mind") := by
    rw [heng.head_eq, getD_arrOf BH (by omega)]
  have hbhB : (σ.arrs "bh").getD (σ.vars "mind") 0 < B := by
    rw [hbhv, hbh0]
    omega
  have hnod : ∀ v < n, E v = 0 → D v ≠ σ.vars "mind" :=
    fun v hv hEv => hbuck.no_deg hbh0 hv hEv
  have hmind1 : σ.vars "mind" + 1 ≤ n := by
    have h₁ := helim.min_le v₀ hv₀ hEv₀
    have h₂ := hnod v₀ hv₀ hEv₀
    have h₃ := hD v₀ hv₀
    omega
  run_vcg [virtualSkipMin_spec B provide]
  · refine ⟨?_, by simp, by simp, by simp, by simp, by simp⟩
    refine ⟨E, D, R, ID, BH, BV, BN, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, hD, ?_, ?_, ?_, ?_⟩
    · exact hclosed.setVar (a := "mind") (by simp [engineVarNames]) hP
    · exact ⟨by simp [heng.n_eq], by simp [heng.elm_eq],
        by simp [heng.deg_eq], by simp [heng.rank_eq], by simp [heng.idg_eq],
        by simp [heng.head_eq], by simp [heng.val_eq], by simp [heng.next_eq]⟩
    · simpa using helim.bump hnod
    · simpa using hbuck
    · simp
      omega
    · simp
      omega
    · simp
      omega
    · simp [hkmax]
  all_goals exfalso
  all_goals omega

/-- A stale head is removed without invoking the row provider. -/
theorem virtualStale_run {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com}
    (hclosed : EngineClosed P) (hB : 3 * n + 3 < B)
    {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (hst : VirtualElimSt n G P E D R ID BH BV BN σ)
    (hcnt : σ.vars "cnt" < n) (hbh0 : BH (σ.vars "mind") ≠ 0)
    (hstale : ¬ (E (BV (BH (σ.vars "mind"))) = 0 ∧
      D (BV (BH (σ.vars "mind"))) = σ.vars "mind")) :
    ∃ σ' K, Run B (virtualCoreTurn provide) σ σ' K ∧ K ≤ 40 ∧
      VirtualElimInv n G P σ' ∧ 0 < σ.vars "ls" ∧
      σ'.vars "mind" = σ.vars "mind" ∧
      σ'.vars "ls" = σ.vars "ls" - 1 ∧
      σ'.vars "sp" = σ.vars "sp" ∧
      σ'.vars "cnt" = σ.vars "cnt" ∧
      σ'.arrs "elm" = σ.arrs "elm" := by
  obtain ⟨hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩ := hst
  obtain ⟨v₀, hv₀, hEv₀⟩ := helim.exists_alive hcnt
  have hmindn : σ.vars "mind" < n := helim.mind_lt hv₀ hEv₀
  have hbhlen : (σ.arrs "bh").length = n + 1 := by
    rw [heng.head_eq, length_arrOf]
  have hbvlen : (σ.arrs "bv").length = n + bucketExtra n + 1 := by
    rw [heng.val_eq, length_arrOf]
  have hbnlen : (σ.arrs "bn").length = n + bucketExtra n + 1 := by
    rw [heng.next_eq, length_arrOf]
  have hdeglen : (σ.arrs "deg").length = n := heng.deg_length
  have helmlen : (σ.arrs "elm").length = n := by
    rw [heng.elm_eq, length_arrOf]
  have hbhv : (σ.arrs "bh").getD (σ.vars "mind") 0 =
      BH (σ.vars "mind") := by
    rw [heng.head_eq, getD_arrOf BH (by omega)]
  have hbhpos : 0 < BH (σ.vars "mind") := Nat.pos_of_ne_zero hbh0
  have hbhlt : BH (σ.vars "mind") < σ.vars "sp" :=
    hbuck.head_lt _ (by omega)
  have hbhB : (σ.arrs "bh").getD (σ.vars "mind") 0 < B := by
    rw [hbhv]
    omega
  have hwn : BV (BH (σ.vars "mind")) < n :=
    hbuck.val_lt _ hbhpos hbhlt
  have hbnlt : BN (BH (σ.vars "mind")) < BH (σ.vars "mind") :=
    hbuck.alloc _ hbhpos hbhlt
  have hslot : BH (σ.vars "mind") < n + bucketExtra n + 1 := by
    simp [bucketExtra]
    omega
  have hbitw : E (BV (BH (σ.vars "mind"))) ≤ 1 := helim.bit _ hwn
  have hdnw : D (BV (BH (σ.vars "mind"))) < n := hD _ hwn
  have hbvv : (σ.arrs "bv").getD
      ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 =
      BV (BH (σ.vars "mind")) := by
    rw [hbhv, heng.val_eq, getD_arrOf BV hslot]
  have hbvB : (σ.arrs "bv").getD
      ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbvv]
    omega
  have hbnv : (σ.arrs "bn").getD
      ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 =
      BN (BH (σ.vars "mind")) := by
    rw [hbhv, heng.next_eq, getD_arrOf BN hslot]
  have hbnB : (σ.arrs "bn").getD
      ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbnv]
    omega
  have helmv : (σ.arrs "elm").getD
      ((σ.arrs "bv").getD
        ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 =
      E (BV (BH (σ.vars "mind"))) := by
    rw [hbvv, heng.elm_eq, getD_arrOf E hwn]
  have helmB : (σ.arrs "elm").getD
      ((σ.arrs "bv").getD
        ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [helmv]
    omega
  have hdegv : (σ.arrs "deg").getD
      ((σ.arrs "bv").getD
        ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 =
      D (BV (BH (σ.vars "mind"))) := by
    rw [hbvv, heng.deg_eq, getD_arrOf D hwn]
  have hdegB : (σ.arrs "deg").getD
      ((σ.arrs "bv").getD
        ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < B := by
    rw [hdegv]
    omega
  have hmachineStale : ¬ ((σ.arrs "elm").getD
      ((σ.arrs "bv").getD
        ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 < 1 ∧
      (σ.arrs "deg").getD
        ((σ.arrs "bv").getD
          ((σ.arrs "bh").getD (σ.vars "mind") 0) 0) 0 =
        σ.vars "mind") := by
    rintro ⟨he, hd⟩
    apply hstale
    rw [helmv] at he
    rw [hdegv] at hd
    exact ⟨by omega, hd⟩
  have hout : ∀ v < n, E v = 0 → D v = σ.vars "mind" →
      v ≠ BV (BH (σ.vars "mind")) := by
    rintro v hv hEv hDv rfl
    exact hstale ⟨hEv, hDv⟩
  obtain ⟨hlspos, hpop⟩ := hbuck.pop (by omega) hbh0 E
    (fun _ _ h => h) hout
  run_vcg [virtualAliveChoice_stale_spec B provide]
  · -- the bucket is known to be nonempty
    exfalso
    omega
  · -- the complete stale nested choice leaves the popped state unchanged
    have hEq := ‹(_ : Env) = _›
    subst hEq
    refine ⟨?_, hlspos, by simp, by simp, by simp, by simp, by simp⟩
    refine ⟨E, D, R, ID,
      upd BH (σ.vars "mind") (BN (BH (σ.vars "mind"))), BV, BN, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, hD, ?_, ?_, ?_, ?_⟩
    · apply hclosed.setVar (a := "ls") (by simp [engineVarNames])
      apply hclosed.setArr (a := "bh") (by simp [engineArrNames])
      apply hclosed.setVar (a := "w") (by simp [engineVarNames])
      apply hclosed.setVar (a := "p") (by simp [engineVarNames])
      exact hP
    · refine ⟨by simp [heng.n_eq], by simp [heng.elm_eq],
        by simp [heng.deg_eq], by simp [heng.rank_eq], by simp [heng.idg_eq],
        ?_, by simp [heng.val_eq], by simp [heng.next_eq]⟩
      simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
        ↓reduceIte, String.reduceEq]
      rw [hbnv, heng.head_eq, set_arrOf_eq_upd]
    · simpa using helim
    · simpa using hpop
    · simp
      omega
    · simp
      omega
    · simp [hmind]
    · simp [hkmax]
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq] at *
  all_goals omega

set_option maxHeartbeats 2000000 in
/-- A live head at the current degree is popped and eliminated through the
provider.  The slot and arena bounds are stated against the state before the
pop, which is the form consumed by the global potential. -/
theorem virtualTake_run {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n (bucketExtra n) G P provide κ)
    (hclosed : EngineClosed P) (hrunClosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B)
    {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (hst : VirtualElimSt n G P E D R ID BH BV BN σ)
    (hcnt : σ.vars "cnt" < n) (hroom : σ.vars "sp" < 2 * n + 3)
    (hbh0 : BH (σ.vars "mind") ≠ 0)
    (hEw : E (BV (BH (σ.vars "mind"))) = 0)
    (hDw : D (BV (BH (σ.vars "mind"))) = σ.vars "mind") :
    ∃ σ' K, Run B (virtualCoreTurn provide) σ σ' K ∧
      K ≤ κ (BV (BH (σ.vars "mind"))) +
        47 * virtualDegree G (BV (BH (σ.vars "mind"))) + 70 ∧
      VirtualElimInv n G P σ' ∧
      σ'.vars "sp" ≤ σ.vars "sp" +
        virtualDegree G (BV (BH (σ.vars "mind"))) ∧
      σ'.vars "ls" ≤ σ.vars "ls" - 1 +
        virtualDegree G (BV (BH (σ.vars "mind"))) ∧
      σ'.vars "cnt" = σ.vars "cnt" + 1 ∧
      σ'.vars "mind" = σ.vars "mind" - 1 ∧
      σ'.vars "kmax" = max (σ.vars "kmax") (σ.vars "mind") ∧
      σ'.arrs "elm" = arrOf n
        (upd E (BV (BH (σ.vars "mind"))) 1) := by
  obtain ⟨hP, heng, helim, hbuck, hD, hsp, hls, hmind, hkmax⟩ := hst
  obtain ⟨v₀, hv₀, hEv₀⟩ := helim.exists_alive hcnt
  have hmindn : σ.vars "mind" < n := helim.mind_lt hv₀ hEv₀
  have hbhlen : (σ.arrs "bh").length = n + 1 := by
    rw [heng.head_eq, length_arrOf]
  have hbvlen : (σ.arrs "bv").length = n + bucketExtra n + 1 := by
    rw [heng.val_eq, length_arrOf]
  have hbnlen : (σ.arrs "bn").length = n + bucketExtra n + 1 := by
    rw [heng.next_eq, length_arrOf]
  have hbhv : (σ.arrs "bh").getD (σ.vars "mind") 0 =
      BH (σ.vars "mind") := by
    rw [heng.head_eq, getD_arrOf BH (by omega)]
  have hbhpos : 0 < BH (σ.vars "mind") := Nat.pos_of_ne_zero hbh0
  have hbhlt : BH (σ.vars "mind") < σ.vars "sp" :=
    hbuck.head_lt _ (by omega)
  have hbhB : (σ.arrs "bh").getD (σ.vars "mind") 0 < B := by
    rw [hbhv]
    omega
  have hwn : BV (BH (σ.vars "mind")) < n :=
    hbuck.val_lt _ hbhpos hbhlt
  let w : Fin n := ⟨BV (BH (σ.vars "mind")), hwn⟩
  have hwval : (w : ℕ) = BV (BH (σ.vars "mind")) := rfl
  have hbnlt : BN (BH (σ.vars "mind")) < BH (σ.vars "mind") :=
    hbuck.alloc _ hbhpos hbhlt
  have hslot : BH (σ.vars "mind") < n + bucketExtra n + 1 := by
    simp [bucketExtra]
    omega
  have hbvv : (σ.arrs "bv").getD
      ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 = (w : ℕ) := by
    rw [hbhv, heng.val_eq, getD_arrOf BV hslot]
  have hbvB : (σ.arrs "bv").getD
      ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbvv]
    omega
  have hbnv : (σ.arrs "bn").getD
      ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 =
      BN (BH (σ.vars "mind")) := by
    rw [hbhv, heng.next_eq, getD_arrOf BN hslot]
  have hbnB : (σ.arrs "bn").getD
      ((σ.arrs "bh").getD (σ.vars "mind") 0) 0 < B := by
    rw [hbnv]
    omega
  have hout : ∀ v < n, upd E (w : ℕ) 1 v = 0 →
      D v = σ.vars "mind" → v ≠ (w : ℕ) := by
    rintro v hv hEv - rfl
    rw [upd_self] at hEv
    omega
  have hback : ∀ v < n, upd E (w : ℕ) 1 v = 0 → E v = 0 := by
    intro v hv hEv
    rw [upd_of_ne _ (fun hc => by rw [hc, upd_self] at hEv; omega)] at hEv
    exact hEv
  obtain ⟨hlspos, hpop⟩ := hbuck.pop (by omega) hbh0 (upd E (w : ℕ) 1)
    hback hout
  run_vcg [virtualAliveChoice_take_spec
    (E := E) (D := D) (R := R) (ID := ID)
    (BH := upd BH (σ.vars "mind") (BN (BH (σ.vars "mind"))))
    (BV := BV) (BN := BN)
    (w := ⟨BV (BH (σ.vars "mind")), hwn⟩) hp hclosed hrunClosed hB]
  · -- the bucket is known to be nonempty
    exfalso
    omega
  · -- the successful provider/extraction result
    obtain ⟨hInv, hsp', hls', hcnt', hmind', hkmax', helm'⟩ :=
      ‹VirtualElimInv n G P _ ∧ _›
    refine ⟨hInv, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hbvv] using hsp'
    · simpa [hbvv] using hls'
    · simpa using hcnt'
    · simpa using hmind'
    · simpa using hkmax'
    · simpa [hbvv] using helm'
  all_goals simp only [arrs_setVar, vars_setVar, arrs_setArr, vars_setArr,
    ↓reduceIte, String.reduceEq] at *
  all_goals try omega
  · -- state immediately after the pop satisfies `TakePre`
    refine ⟨?_, ?_, ?_, ?_, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply hclosed.setVar (a := "ls") (by simp [engineVarNames])
      apply hclosed.setArr (a := "bh") (by simp [engineArrNames])
      apply hclosed.setVar (a := "w") (by simp [engineVarNames])
      apply hclosed.setVar (a := "p") (by simp [engineVarNames])
      exact hP
    · refine ⟨by simp [heng.n_eq], by simp [heng.elm_eq],
        by simp [heng.deg_eq], by simp [heng.rank_eq], by simp [heng.idg_eq],
        ?_, by simp [heng.val_eq], by simp [heng.next_eq]⟩
      simp only [arrs_setVar, arrs_setArr]
      rw [heng.head_eq, set_arrOf_eq_upd]
      simp only [if_true]
      have hbnv' : (σ.arrs "bn").getD
          ((arrOf (n + 1) BH).getD (σ.vars "mind") 0) 0 =
          BN (BH (σ.vars "mind")) := by
        rw [← heng.head_eq]
        exact hbnv
      rw [hbnv']
    · simpa using helim
    · simpa using hpop
    · simpa [hbvv]
    · simpa using hcnt
    · simpa [hwval] using hEw
    · simpa [hwval] using hDw
    · simpa using hroom
    · have hslotLive : σ.vars "ls" - 1 + 1 ≤ σ.vars "sp" := by omega
      simpa using hslotLive
    · simpa using hmind
    · simpa using hkmax

/-- Complete case split for a guarded core turn. -/
theorem virtualCoreTurn_run {B n : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n (bucketExtra n) G P provide κ)
    (hclosed : EngineClosed P) (hrunClosed : EngineRunClosed P)
    (hB : 3 * n + 3 < B)
    {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (hst : VirtualElimSt n G P E D R ID BH BV BN σ)
    (hcnt : σ.vars "cnt" < n) (hroom : σ.vars "sp" < 2 * n + 3) :
    ∃ σ' K, Run B (virtualCoreTurn provide) σ σ' K ∧
      VirtualElimInv n G P σ' ∧ VirtualCoreEffect n G κ E σ σ' K := by
  have hbuck : Buck n n E D BH BV BN (σ.vars "sp") (σ.vars "ls") :=
    hst.2.2.2.1
  have hmindLe : σ.vars "mind" ≤ n := hst.2.2.2.2.2.2.2.1
  by_cases hbh0 : BH (σ.vars "mind") = 0
  · obtain ⟨σ', K, hr, hK, hI, hmind, hls, hsp, hcnt', helm⟩ :=
      virtualBump_run (provide := provide) hclosed hB hst hcnt hbh0
    exact ⟨σ', K, hr, hI, Or.inl ⟨hK, hmind, hls, hsp, hcnt', helm⟩⟩
  · by_cases htake : E (BV (BH (σ.vars "mind"))) = 0 ∧
        D (BV (BH (σ.vars "mind"))) = σ.vars "mind"
    · obtain ⟨σ', K, hr, hK, hI, hsp, hls, hcnt', hmind, hkmax, helm⟩ :=
        virtualTake_run hp hclosed hrunClosed hB hst hcnt hroom hbh0
          htake.1 htake.2
      exact ⟨σ', K, hr, hI, Or.inr (Or.inr
        ⟨BV (BH (σ.vars "mind")),
          hbuck.val_lt _ (Nat.pos_of_ne_zero hbh0)
            (hbuck.head_lt _ hmindLe),
          htake.1, hK, hsp, hls, hcnt', hmind, hkmax, helm⟩)⟩
    · obtain ⟨σ', K, hr, hK, hI, hlspos, hmind, hls, hsp, hcnt', helm⟩ :=
        virtualStale_run (provide := provide) hclosed hB hst hcnt hbh0 htake
      exact ⟨σ', K, hr, hI, Or.inr (Or.inl
        ⟨hK, hlspos, hmind, hls, hsp, hcnt', helm⟩)⟩

/-! ## Axiom audit -/

#print axioms virtualSkipMin_spec
#print axioms virtualAliveChoice_stale_spec
#print axioms virtualAliveChoice_take_spec
#print axioms virtualBump_run
#print axioms virtualStale_run
#print axioms virtualTake_run
#print axioms virtualCoreTurn_run

end Lax3Proofs.Refine.OrderVirtualTurn
