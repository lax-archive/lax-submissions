import Lax3Proofs.Refine.OrderActiveChain

/-!
# Initializing the compact active augmentation chain

The first compact elimination leaves the actual number of orientation arcs
as the last `ioff` offset, but the augmentation engine reads that number from
the scalar `kd`.  This file installs that exact value with one constant-time
read and packages the elimination output as stage zero of `ActiveFoldInv`.
-/

namespace Lax3Proofs.Refine.OrderActiveInit

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Augmentation (Orientation IsAugChain GreedyFratRound)
open Lax3Proofs.RamElim (CsrSimple InCsr)
open Lax3Proofs.Refine.ScatterBlock (MemList)
open Lax3Proofs.Refine.ElimCompact (ElimMemPost memGraph)
open Lax3Proofs.Refine.OrderActiveElim (elimWorkCom elimWorkCost elimWork_spec)
open Lax3Proofs.Refine.OrderActiveChain

/-- Read the live orientation slot count from the last compact offset. -/
def installLiveCountCom : Com :=
  .assign "kd" (.get "ioff" (.var "mm"))

/-- The last `InCsr` offset is the exact arc count, so one array read installs
the scalar expected by the compact augmentation engine. -/
theorem installLiveCount_run {B n mm W m : ℕ} {D : Orientation mm}
    {IO IT : ℕ → ℕ} { σ : Env }
    (hmn : mm ≤ n) (hmmB : mm < B) (hmB : m < B)
    (hmm : σ.vars "mm" = mm) (hsz : ActiveOrderSized n W σ)
    (hio : ∀ z, z ≤ mm → (σ.arrs "ioff").getD z 0 = IO z)
    (hin : InCsr D m IO IT) :
    Run B installLiveCountCom σ (σ.setVar "kd" m) 3 := by
  obtain ⟨IOg, hIOg⟩ :=
    hsz.get (p := ("ioff", n + 1)) (by simp [activeOrderLayout])
  have hIOgm : IOg mm = m := by
    have h := hio mm le_rfl
    rw [hIOg, getD_arrOf IOg (by omega), hin.last] at h
    exact h
  have hmmEval : (Expr.var "mm").evalB B σ = some mm := by
    have h := evalB_var (B := B) (x := "mm") ( σ := σ)
      (by rw [hmm]; exact hmmB)
    rw [hmm] at h
    exact h
  have hread : (Expr.get "ioff" (.var "mm")).evalB B σ = some m := by
    refine evalB_get hmmEval ?_ hmB
    rw [hIOg, getElem?_arrOf IOg (by omega), hIOgm]
  simpa only [installLiveCountCom, Expr.size] using
    (Run.assign (B := B) (x := "kd") ( σ := σ) hread)

/-- Package an oriented compact CSR as the zero-stage fold invariant after
installing its exact live slot count. -/
theorem activeFold_init {B n mm W w d₀ m : ℕ} {H : SimpleGraph (Fin mm)}
    {Mem IO IT : ℕ → ℕ} {D : Orientation mm} { σ : Env }
    (hmn : mm ≤ n) (hwW : w ≤ W) (hmmB : mm < B) (hmB : m < B)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hsz : ActiveOrderSized n W σ)
    (horients : D.Orients H) (hindeg : D.InDegLE d₀)
    (hin : InCsr D m IO IT) (hmw : m ≤ w)
    (hio : ∀ z, z ≤ mm → (σ.arrs "ioff").getD z 0 = IO z)
    (hitg : σ.arrs "itg" = arrOf W IT) :
    ∃ σ', Run B installLiveCountCom σ σ' 3 ∧
      ActiveFoldInv n mm W w d₀ H Mem 0 σ' := by
  let σ' := σ.setVar "kd" m
  have r : Run B installLiveCountCom σ σ' 3 :=
    installLiveCount_run hmn hmmB hmB hmm hsz hio hin
  let Ds : ℕ → Orientation mm := fun _ => D
  have hchain : IsAugChain H Ds 0 := by
    refine ⟨by simpa only [Ds] using horients, ?_⟩
    intro i hi
    omega
  have hgreedy : ∀ l < 0, GreedyFratRound (Ds l) (Ds (l + 1)) := by
    intro l hl
    omega
  refine ⟨σ', r, ?_⟩
  refine ⟨?_, ?_, ?_, hsz.run r, Ds, m, IO, IT, hchain, hgreedy, ?_, ?_, hmw,
    ?_, ?_, ?_⟩
  · simpa only [σ', vars_setVar, if_neg (by decide : ¬ ("n" = "kd"))] using hn
  · simpa only [σ', vars_setVar, if_neg (by decide : ¬ ("mm" = "kd"))] using hmm
  · simpa only [σ', arrs_setVar] using hmem
  · simpa only [Ds] using hindeg
  · simpa only [Ds] using hin
  · simp only [σ', vars_setVar, if_pos]
  · intro z hz
    simpa only [σ', arrs_setVar] using hio z hz
  · intro z hz
    simp only [σ', arrs_setVar, hitg]
    rw [getD_arrOf IT (lt_of_lt_of_le hz (hmw.trans hwW))]

/-- Every compact elimination postcondition initializes the fold.  Its
degeneracy witness becomes the initial in-degree bound. -/
theorem activeFold_init_of_elimPost {B n mm ns W w : ℕ}
    {G : SimpleGraph (Fin n)} {M Mem : ℕ → ℕ}
    {X : Set (Fin n)} {hml : MemList n mm Mem X} { σ : Env }
    (hmn : mm ≤ n) (hnsw : ns ≤ w) (hwW : w ≤ W)
    (hmmB : mm < B) (hwB : w < B)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hsz : ActiveOrderSized n W σ)
    (hpost : ElimMemPost G M Mem hml ns W σ) :
    ∃ σ' k, Run B installLiveCountCom σ σ' 3 ∧
      ActiveFoldInv n mm W w k (memGraph G M hml) Mem 0 σ' := by
  obtain ⟨R, IO, IT, k, m, E, -, -, hio, hitg, hmns, -, horients, hindeg,
    -, -, -, -, -, -, hin⟩ := hpost
  obtain ⟨σ', r, hI⟩ := activeFold_init hmn hwW hmmB
    (lt_of_le_of_lt (hmns.trans hnsw) hwB) hn hmm hmem hsz horients hindeg hin
    (hmns.trans hnsw) hio hitg
  exact ⟨σ', k, r, hI⟩

/-! ## The first resident elimination followed by fold initialization -/

def elimFoldInitCom : Com :=
  .seq elimWorkCom installLiveCountCom

def elimFoldInitCost (mm ns : ℕ) : ℕ :=
  elimWorkCost mm ns + 3

/-- Run the first compact elimination and expose exactly the invariant needed
by `activeFold_run`; all resident lengths are threaded automatically. -/
theorem elimFoldInit_spec {B n mm ns W w : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Mem : ℕ → ℕ} { σ : Env }
    (hml : MemList n mm Mem (Lax3Proofs.RamDriverCluster.markSet n M))
    (hcsr : CsrSimple (memGraph G M hml) ns O T)
    (hB : mm + ns + 1 < B) (hnB : n < B)
    (hnsw : ns ≤ w) (hwW : w ≤ W) (hwB : w < B)
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm)
    (hgof : σ.arrs "gof" = arrOf (n + 1) O)
    (hgtg : σ.arrs "gtg" = arrOf W T)
    (hmem : σ.arrs "mem" = arrOf n Mem) (hsz : ActiveOrderSized n W σ) :
    ∃ σ' k, Run B elimFoldInitCom σ σ' (elimFoldInitCost mm ns) ∧
      ActiveFoldInv n mm W w k (memGraph G M hml) Mem 0 σ' := by
  have get (a : String) (k : ℕ) (ha : (a, k) ∈ activeOrderLayout n W) :
      ∃ g, σ.arrs a = arrOf k g := hsz.get ha
  obtain ⟨σ₁, r₁, hpost, hn₁, hmm₁, -, -⟩ :=
    elimWork_spec hml hcsr hB hnB (hnsw.trans hwW) hn hmm hgof hgtg hmem
      (get "ork" n (by simp [activeOrderLayout]))
      (get "alv" n (by simp [activeOrderLayout]))
      (get "deg" n (by simp [activeOrderLayout]))
      (get "elm" n (by simp [activeOrderLayout]))
      (get "rnk" n (by simp [activeOrderLayout]))
      (get "idg" n (by simp [activeOrderLayout]))
      (get "bh" (n + 1) (by simp [activeOrderLayout]))
      (get "bv" (n + W + 1) (by simp [activeOrderLayout]))
      (get "bn" (n + W + 1) (by simp [activeOrderLayout]))
      (get "ioff" (n + 1) (by simp [activeOrderLayout]))
      (get "ifl" n (by simp [activeOrderLayout]))
      (get "itg" W (by simp [activeOrderLayout]))
  have hmn : mm ≤ n :=
    Lax3Proofs.Refine.ElimCompactWalks.card_le_of_smono
      (fun i j hij hj => hml.smono i j hij hj) (fun j hj => hml.lt j hj)
  have hmem₁ : σ₁.arrs "mem" = arrOf n Mem := by
    rw [r₁.frame_arr "mem" (by decide), hmem]
  obtain ⟨σ₂, k, r₂, hI⟩ := activeFold_init_of_elimPost hmn hnsw hwW
    (by omega) hwB hn₁ hmm₁ hmem₁ (hsz.run r₁) hpost
  refine ⟨σ₂, k, ?_, hI⟩
  simpa only [elimFoldInitCom, elimFoldInitCost] using r₁.seq r₂

/-! ## Axioms -/

#print axioms installLiveCount_run
#print axioms activeFold_init
#print axioms activeFold_init_of_elimPost
#print axioms elimFoldInit_spec

end Lax3Proofs.Refine.OrderActiveInit
