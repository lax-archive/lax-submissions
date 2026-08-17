import Lax3Proofs.Refine.CoverActiveStreamScratch

/-!
# The recursive call of a streamed active-cover turn

The streamed descent already holds every semantic component of the child
level, but distributed between the parent `LevelPre`, `ClusterData`, the
computed palette, and the kill rows.  This file assembles those components
into the exact `LevelPre`/`TableInvOn` interface of the recursive driver.

The assembly is representation-only: it performs no carrier walk and adds no
runtime cost.  Storage separation and scalar save/restore are supplied by
`CoverActiveStreamDepth` and are composed with this adapter below.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamInner

open Lax3.ColoredGraphs
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.Refine.CoverActiveStreamKill
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.CoverActiveStreamScratch
open Lax3Proofs.Refine.ScatterBlock (renEnv renEnv_arrs renEnv_vars)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {n : ℕ}

/-- The streamed batch and palette are exactly a child `LevelPre`.  All
depth-independent memory comes from the enclosing level; the child masks,
palette, and member enumeration come from the streamed descent. -/
theorem StreamKillOut.childLevelPre
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam Gm : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOut B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ)
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ) :
    LevelPre B n cap mb ns nt O T (j + 1) Alv Gam C' σ := by
  rcases hp with
    ⟨hn, hoff, htgt, -, -, -, -, -, -, hlevelMem, hdepthMem, hm, horderMem,
      htgtZero, htgtBound, -⟩
  rcases h.data.1 with
    ⟨-, -, -, halv, hAlvBound, -, -, hgam, hGamBound, hmem⟩
  exact ⟨hn, hoff, htgt, halv, hgam, h.colour_arr, hAlvBound, hGamBound,
    h.colour_bit, hlevelMem, hdepthMem, hm, horderMem, htgtZero, htgtBound, hmem⟩

/-- The rows written just before recursion are the child's initial table
invariant on the kill domain. -/
theorem StreamKillOut.childTableInvOn
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOut B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ) :
    TableInvOn q_top cap mb φ G (j + 1) Alv C'
      (killSet A₀ (markSet n Xa) (markSet n Wa)) σ :=
  h.kill_rows.tableInvOn h.tables

/-- The streamed output satisfies the complete precondition of the child
driver.  This is the semantic join point used by the fused turn. -/
theorem StreamKillOut.childCallPre
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam Gm : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOut B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ)
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ) :
    LevelPre B n cap mb ns nt O T (j + 1) Alv Gam C' σ ∧
      TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ell φ σ ∧
      PlayRec B cap G (j + 1) Alv Gam σ ∧
      TableInvOn q_top cap mb φ G (j + 1) Alv C'
        (killSet A₀ (markSet n Xa) (markSet n Wa)) σ :=
  ⟨StreamKillOut.childLevelPre h hp, h.tables, h.base_arrs, h.play,
    StreamKillOut.childTableInvOn h⟩

/-- The child mask kills every vertex whose row the parent pre-wrote. -/
theorem StreamKillOut.killSet_dead
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOut B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ) :
    ∀ v : Fin n, v ∈ killSet A₀ (markSet n Xa) (markSet n Wa) →
      Alv (v : ℕ) = 0 :=
  fun _ hv => Lax3Proofs.RamDriverCluster.killSet_dead h.data.1.2.2.2.2.2.2.1 hv

/-- Invoke any recursive implementation accepted by the landed cluster
interface.  The adapter itself is free; the bound is exactly the child's
arena-dependent bound. -/
theorem streamInnerSemanticStep
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam Gm : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n}
    {wA : (ℕ → ℕ) → ℕ} {inner : Com} {Kin : ℕ → ℕ}
    (hinner : InnerAvail B q_top cap mb ns nt ell j φ G O T wA inner Kin) :
    Spec B
      (fun σ =>
        StreamKillOut B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
          centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
      inner
      (fun σ σ' =>
        LevelPostD B q_top cap mb φ G ns nt O T (j + 1) Alv Gam C'
          (killSet A₀ (markSet n Xa) (markSet n Wa)) σ σ' ∧
        σ'.out = σ.out)
      (Kin (wA Alv)) := by
  intro σ hσ
  exact (hinner Alv Gam C' (killSet A₀ (markSet n Xa) (markSet n Wa))
    (StreamKillOut.killSet_dead hσ.1) hσ.1.colour_bit).run
      (StreamKillOut.childCallPre hσ.1 hσ.2)

/-! ## The physical depth-owned state -/

/-- The logical streamed state, interpreted through the five-pair physical
storage permutation of its parent depth. -/
def StreamKillOutAtDepth
    (B q_top cap mb ns nt na q j c tail bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ)
    (C C' : ℕ → ℕ → ℕ) (w : Fin mb → Fin n) (σ : Env) : Prop :=
  StreamKillOut B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
    centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w
      (renEnv (streamDepthSwap j) σ)

/-- At the physical seam, the parent `LevelPre` supplies common memory while
the renamed streamed output supplies the child masks, colours and member
enumeration. -/
theorem childLevelPreAtDepth
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam Gm : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ)
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ) :
    LevelPre B n cap mb ns nt O T (j + 1) Alv Gam C' σ := by
  rcases hp with
    ⟨hn, hoff, htgt, -, -, -, -, -, -, hlevelMem, hdepthMem, hm, horderMem,
      htgtZero, htgtBound, -⟩
  rcases h.data.1 with
    ⟨-, -, -, halv, hAlvBound, -, -, hgam, hGamBound, hmem⟩
  refine ⟨hn, hoff, htgt, ?_, ?_, ?_, hAlvBound, hGamBound, h.colour_bit,
    hlevelMem, hdepthMem, hm, horderMem, htgtZero, htgtBound, ?_⟩
  · simpa only [renEnv_arrs, streamDepthSwap_alvName] using halv
  · simpa only [renEnv_arrs, streamDepthSwap_gamName] using hgam
  · intro s hs
    simpa only [renEnv_arrs, streamDepthSwap_colName] using h.colour_arr s hs
  · rcases hmem with ⟨Mem, mm, hMem, hmm, henum, hbound⟩
    exact ⟨Mem, mm,
      by simpa only [renEnv_arrs, streamDepthSwap_memName] using hMem,
      by simpa only [renEnv_vars] using hmm, henum, hbound⟩

/-- The successor play record uses only connector scalars and the
`res`/`gam`/`par` depth families, all fixed by the storage permutation. -/
theorem childPlayAtDepth
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ) :
    PlayRec B cap G (j + 1) Alv Gam σ :=
  h.play.congr
    (fun _ _ => by simp only [renEnv_vars])
    (fun a _ => by simp only [renEnv_arrs, streamDepthSwap_resName])
    (fun a _ => by simp only [renEnv_arrs, streamDepthSwap_gamName])
    (fun a _ => by simp only [renEnv_arrs, streamDepthSwap_parName])

/-- The pre-written kill rows transport to physical storage because table
names are not among the five exchanges. -/
theorem childKillRowsAtDepth
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ) :
    KillRowsAt q_top cap mb j φ G A₀ Alv
      (markSet n Xa) (markSet n Wa) C' σ := by
  intro i hi Tb hTb v hAv hvX hvW
  apply h.kill_rows i hi Tb
    (by simpa only [renEnv_arrs, streamDepthSwap_tabName] using hTb)
    v hAv hvX hvW

/-- Exact physical recursive-call precondition.  The table and base-memory
clauses are carried in the physical environment by the enclosing run; the
semantic streamed state supplies everything data-dependent. -/
theorem childCallPreAtDepth
    {B q_top cap mb ns nt na q j c tail bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam Gm : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {σ : Env}
    (h : StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
      centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ)
    (hp : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (ht : TablesSized q_top cap mb φ n σ)
    (hb : BaseArrs B q_top cap mb ell φ σ) :
    LevelPre B n cap mb ns nt O T (j + 1) Alv Gam C' σ ∧
      TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ell φ σ ∧
      PlayRec B cap G (j + 1) Alv Gam σ ∧
      TableInvOn q_top cap mb φ G (j + 1) Alv C'
        (killSet A₀ (markSet n Xa) (markSet n Wa)) σ :=
  ⟨childLevelPreAtDepth h hp, ht, hb, childPlayAtDepth h,
    (childKillRowsAtDepth h).tableInvOn ht⟩

/-! ## Save--recurse--restore -/

/-- The exact five-clause precondition of the concrete recursive driver,
named so it can be transported across the parent's scalar save. -/
def StreamChildPre {n : ℕ}
    (B q_top cap mb ns nt ell j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T Alv Gam : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (D : Set (Fin n)) (σ : Env) : Prop :=
  LevelPre B n cap mb ns nt O T (j + 1) Alv Gam C σ ∧
    TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ell φ σ ∧
    PlayRec B cap G (j + 1) Alv Gam σ ∧
    TableInvOn q_top cap mb φ G (j + 1) Alv C D σ

/-- The one scalar invariant shared by every streamed level.  The radix
width is computed once at the root and then saved around recursive calls;
requiring it here keeps that one-time computation out of every centre. -/
def StreamRadixReady (B n : ℕ) (σ : Env) : Prop :=
  σ.vars "rsbits" = Nat.clog 2 n ∧
    Nat.clog 2 n < B ∧ n ≤ 2 ^ Nat.clog 2 n

/-- A recursive level contract with the program text left abstract.  This is
the semantic part of `LevelImplementsDA`, separated from the historical
choice of cover phase so the streamed driver can call itself. -/
def StreamLevelImplementsD {n : ℕ}
    (B q_top cap mb ns nt ell j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (D : Set (Fin n)) (cmd : Com) (K : ℕ) : Prop :=
  (∀ v : Fin n, v ∈ D → M (v : ℕ) = 0) →
  (∀ c < Lax3Proofs.FormulaTables.sigL cap mb (j + 1),
    ∀ v < n, C c v ≤ 1) →
  Spec B (fun σ =>
      StreamChildPre B q_top cap mb ns nt ell j φ G O T M Gm C D σ ∧
      StreamScratchFrom B n cap mb ell (j + 1) σ ∧
      StreamRadixReady B n σ)
    cmd
    (fun σ σ' =>
      LevelPostD B q_top cap mb φ G ns nt O T (j + 1) M Gm C D σ σ' ∧
      σ'.out = σ.out ∧
      StreamScratchFrom B n cap mb ell (j + 1) σ')
    K

/-- A scalar outside the child's level and play interfaces preserves the
whole recursive precondition. -/
theorem StreamChildPre.setVar
    {B q_top cap mb ns nt ell j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T Alv Gam : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {D : Set (Fin n)} {σ : Env}
    (h : StreamChildPre B q_top cap mb ns nt ell j φ G O T Alv Gam C D σ)
    (x : String) (hxn : x ≠ "n") (hxm : x ≠ "m") (hxlw : x ≠ "lw")
    (hxmm : x ≠ mnumName (j + 1)) (hxctr : ∀ a : ℕ, x ≠ ctrName a) (k : ℕ) :
    StreamChildPre B q_top cap mb ns nt ell j φ G O T Alv Gam C D
      (σ.setVar x k) := by
  refine ⟨levelPre_setVar h.1 x hxn hxm hxlw hxmm k,
    tablesSized_setVar_c h.2.1 x k, baseArrs_setVar_c h.2.2.1 x k,
    playRec_setVar h.2.2.2.1 x hxctr k, ?_⟩
  simpa only [TableInvOn, arrs_setVar] using h.2.2.2.2

/-- The four parent save slots are all below the child depth, hence saving
the loop scalars preserves the complete child-call precondition. -/
theorem StreamChildPre.saved
    {B q_top cap mb ns nt ell j q c tail bits : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {O T Alv Gam : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {D : Set (Fin n)} {σ : Env}
    (h : StreamChildPre B q_top cap mb ns nt ell j φ G O T Alv Gam C D σ) :
    StreamChildPre B q_top cap mb ns nt ell j φ G O T Alv Gam C D
      (streamSavedEnv j q c tail bits σ) := by
  unfold streamSavedEnv
  apply StreamChildPre.setVar
  · apply StreamChildPre.setVar
    · apply StreamChildPre.setVar
      · apply StreamChildPre.setVar h
        all_goals simp [cnumName, mnumName, ctrName, String.ext_iff]
      all_goals simp [curName, mnumName, ctrName, String.ext_iff]
    all_goals simp [xpName, mnumName, ctrName, String.ext_iff]
  all_goals simp [cixName, mnumName, ctrName, String.ext_iff]

/-- A scalar update away from the four variables mentioned by `LevelPre`
also preserves a completed child postcondition. -/
theorem levelPostD_setVar
    {B q_top cap mb ns nt jd : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {D : Set (Fin n)} {σ₀ σ : Env}
    (h : LevelPostD B q_top cap mb φ G ns nt O T jd M Gm C D σ₀ σ)
    (x : String) (hxn : x ≠ "n") (hxm : x ≠ "m") (hxlw : x ≠ "lw")
    (hxmm : x ≠ mnumName jd) (k : ℕ) :
    LevelPostD B q_top cap mb φ G ns nt O T jd M Gm C D σ₀
      (σ.setVar x k) := by
  refine ⟨levelPre_setVar h.1 x hxn hxm hxlw hxmm k,
    tablesSized_setVar_c h.2.1 x k, ?_⟩
  simpa only [TableInvOn, arrs_setVar] using h.2.2

/-- Restoring the parent's fixed scalar interface does not affect the
completed child level. -/
theorem levelPostD_restored
    {B q_top cap mb ns nt j q c tail bits : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {D : Set (Fin n)} {σ₀ σ : Env}
    (h : LevelPostD B q_top cap mb φ G ns nt O T (j + 1) M Gm C D σ₀ σ) :
    LevelPostD B q_top cap mb φ G ns nt O T (j + 1) M Gm C D σ₀
      (streamRestoredEnv q c tail bits σ) := by
  unfold streamRestoredEnv
  apply levelPostD_setVar
  · apply levelPostD_setVar
    · apply levelPostD_setVar
      · apply levelPostD_setVar
        · apply levelPostD_setVar h
          all_goals simp [mnumName, String.ext_iff]
        all_goals simp [mnumName, String.ext_iff]
      all_goals simp [mnumName, String.ext_iff]
    all_goals simp [mnumName, String.ext_iff]
  all_goals simp [mnumName, String.ext_iff]

/-- The part of the streamed parent state that must cross one concrete
recursive call. -/
structure StreamParentFrame (j q c tail bits : ℕ) (σ σ' : Env) : Prop where
  q_var : σ'.vars "qn" = q
  centre_var : σ'.vars "c" = c
  pointer_var : σ'.vars "xp" = tail
  tail_var : σ'.vars "tail" = tail
  bits_var : σ'.vars "rsbits" = bits
  saved : StreamScalarsSaved j q c tail bits σ'
  ord_arr : σ'.arrs (ordName j) = σ.arrs (ordName j)
  mask_arr : σ'.arrs (cpsName j) = σ.arrs (cpsName j)
  row_arr : σ'.arrs (xmmName j) = σ.arrs (xmmName j)
  asg_arr : σ'.arrs (asgName j) = σ.arrs (asgName j)
  dist_arr : σ'.arrs (pdsName j) = σ.arrs (pdsName j)
  depth_arr : ∀ a, Lax3Proofs.RamDriverWrites.BelowArr (j + 1) a →
    σ'.arrs a = σ.arrs a
  round_var : ∀ a < j, σ'.vars (ctrName a) = σ.vars (ctrName a)
  connector_var : σ'.vars (ctrName j) = σ.vars (ctrName j)
  member_count_var : σ'.vars (mnumName j) = σ.vars (mnumName j)
  kill_count_var : σ'.vars (kkName j) = σ.vars (kkName j)
  out_eq : σ'.out = σ.out

/-- The syntactic ownership facts required of a recursive child.  They are
independent of the child's semantics: a child may write its own and deeper
storage, but never its parent's depth-owned state. -/
structure StreamInnerFrames (j : ℕ) (inner : Com) : Prop where
  saved_var : ∀ y ∈ [curName j, cnumName j, xpName j, cixName j],
    y ∉ inner.wvars
  parent_arr : ∀ a ∈ [ordName j, cpsName j, xmmName j, asgName j, pdsName j],
    a ∉ inner.warrs
  below_arr : ∀ a, Lax3Proofs.RamDriverWrites.BelowArr (j + 1) a →
    a ∉ inner.warrs
  below_var : ∀ y, Lax3Proofs.RamDriverWrites.BelowVar (j + 1) y →
    y ∉ inner.wvars

/-- Save the parent scalars, run the actual active driver at depth `j+1`,
then restore the scalar interface. -/
def streamInnerCom (j : ℕ) (inner : Com) : Com :=
  .seq (streamSaveCom j)
    (.seq inner (streamRestoreCom j))

/-- If the recursive command respects the depth discipline, the concrete
save--call--restore wrapper respects it as well. -/
theorem belowArr_notMem_warrs_streamInnerCom
    {j : ℕ} {inner : Com} {a : String}
    (hinner : ∀ a, Lax3Proofs.RamDriverWrites.BelowArr (j + 1) a →
      a ∉ inner.warrs)
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamInnerCom j inner).warrs := by
  simpa [streamInnerCom, streamSaveCom, streamRestoreCom, Com.warrs] using
    hinner a (h.mono (Nat.le_succ j))

theorem belowVar_notMem_wvars_streamInnerCom
    {j : ℕ} {inner : Com} {y : String}
    (hinner : ∀ y, Lax3Proofs.RamDriverWrites.BelowVar (j + 1) y →
      y ∉ inner.wvars)
    (h : Lax3Proofs.RamDriverWrites.BelowVar j y) :
    y ∉ (streamInnerCom j inner).wvars := by
  have hd := Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h
  have hfixed : ∀ z ∈ (["qn", "c", "xp", "tail", "rsbits"] : List String),
      y ≠ z := by
    intro z hz he
    exact (Lax3Proofs.RamDriverWrites.notHasDigit_mem (by decide) hz) (he ▸ hd)
  have hcnum : y ≠ cnumName j :=
    Lax3Proofs.RamDriverWrites.belowVar_ne h le_rfl (by tauto)
  have hcur : y ≠ curName j :=
    Lax3Proofs.RamDriverWrites.belowVar_ne h le_rfl (by tauto)
  have hxp : y ≠ xpName j :=
    Lax3Proofs.RamDriverWrites.belowVar_ne h le_rfl (by tauto)
  have hcix : y ≠ cixName j :=
    Lax3Proofs.RamDriverWrites.belowVar_ne h le_rfl (by tauto)
  simpa [streamInnerCom, streamSaveCom, streamRestoreCom, Com.wvars,
    hcnum, hcur, hxp, hcix,
    hfixed "qn" (by simp), hfixed "c" (by simp),
    hfixed "xp" (by simp), hfixed "tail" (by simp),
    hfixed "rsbits" (by simp)] using
      hinner y (h.mono (Nat.le_succ j))

/-- **The physical recursive seam.**  Starting from a depth-owned streamed
row, this runs the actual active driver at the successor depth.  The bound is
the child's bound plus the exact eighteen scalar instructions; the five
parent arrays, all five loop scalars, the save slots, and output are retained.
-/
theorem streamInnerStep
    {B n q_top cap mb ns nt na q j c tail bits ell K : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Xmem asg M Xa Ra Wa Alv Gam Gm : ℕ → ℕ}
    {C C' : ℕ → ℕ → ℕ} {w : Fin mb → Fin n} {inner : Com}
    (hchild : StreamLevelImplementsD B q_top cap mb ns nt ell j φ G O T
      Alv Gam C' (killSet A₀ (markSet n Xa) (markSet n Wa)) inner K)
    (hframes : StreamInnerFrames j inner)
    (hqB : q < B) (hcB : c < B) (htailB : tail < B) (hbitsB : bits < B)
    (hpow : n ≤ 2 ^ bits) (hbitsEq : bits = Nat.clog 2 n) :
    Spec B
      (fun σ =>
        StreamKillOutAtDepth B q_top cap mb ns nt na q j c tail bits ell φ G A₀ π
          centre O T Xmem asg M Xa Ra Wa Alv Gam C C' w σ ∧
        LevelPre B n cap mb ns nt O T j A₀ Gm C σ ∧
        TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ell φ σ ∧
        StreamScratchFrom B n cap mb ell (j + 1) σ)
      (streamInnerCom j inner)
      (fun σ σ' =>
        LevelPostD B q_top cap mb φ G ns nt O T (j + 1) Alv Gam C'
          (killSet A₀ (markSet n Xa) (markSet n Wa)) σ σ' ∧
        StreamParentFrame j q c tail bits σ σ' ∧
        StreamScratchFrom B n cap mb ell (j + 1) σ')
      (8 + K + 10) := by
  intro σ hpre
  let σs := streamSavedEnv j q c tail bits σ
  have hstream := hpre.1
  have hvals : σ.vars "qn" = q ∧ σ.vars "c" = c ∧
      σ.vars "tail" = tail ∧ σ.vars "rsbits" = bits := by
    exact ⟨by simpa only [renEnv_vars] using hstream.sorted.q_var,
      by simpa only [renEnv_vars] using hstream.sorted.centre_var,
      by simpa only [renEnv_vars] using hstream.sorted.tail_var,
      by simpa only [renEnv_vars] using hstream.sorted.bits_var⟩
  have hrs : Run B (streamSaveCom j) σ σs 8 :=
    streamSaveCom_run hvals hqB hcB htailB hbitsB
  have hcall₀ : StreamChildPre B q_top cap mb ns nt ell j φ G O T Alv Gam C'
      (killSet A₀ (markSet n Xa) (markSet n Wa)) σ :=
    childCallPreAtDepth hstream hpre.2.1 hpre.2.2.1 hpre.2.2.2.1
  have hcall : StreamChildPre B q_top cap mb ns nt ell j φ G O T Alv Gam C'
      (killSet A₀ (markSet n Xa) (markSet n Wa)) σs := by
    exact StreamChildPre.saved (q := q) (c := c) (tail := tail) (bits := bits) hcall₀
  have hscratchs : StreamScratchFrom B n cap mb ell (j + 1) σs := by
    apply hpre.2.2.2.2.congr
    intro a
    simp [σs, streamSavedEnv]
  have hreadys : StreamRadixReady B n σs := by
    refine ⟨?_, ?_, ?_⟩
    · simp [σs, streamSavedEnv, cnumName, curName, xpName, cixName,
        String.ext_iff, hvals.2.2.2, hbitsEq]
    · simpa [hbitsEq] using hbitsB
    · simpa [hbitsEq] using hpow
  obtain ⟨σc, hrc, hpostc, houtc, hscratchc⟩ :=
    (hchild (StreamKillOut.killSet_dead hstream) hstream.colour_bit).run
      ⟨hcall, hscratchs, hreadys⟩
  have hsaveds : StreamScalarsSaved j q c tail bits σs := by
    simp [σs, StreamScalarsSaved, streamSavedEnv, cnumName, curName, xpName,
      cixName, String.ext_iff]
  have hvar (y : String)
      (hy : y ∈ [curName j, cnumName j, xpName j, cixName j]) :
      σc.vars y = σs.vars y :=
    hrc.frame_var y (hframes.saved_var y hy)
  have hsavedc : StreamScalarsSaved j q c tail bits σc :=
    ⟨(hvar _ (by simp)).trans hsaveds.1,
      (hvar _ (by simp)).trans hsaveds.2.1,
      (hvar _ (by simp)).trans hsaveds.2.2.1,
      (hvar _ (by simp)).trans hsaveds.2.2.2⟩
  let σr := streamRestoredEnv q c tail bits σc
  have hrr : Run B (streamRestoreCom j) σc σr 10 :=
    streamRestoreCom_run hsavedc hqB hcB htailB hbitsB
  have hpostr : LevelPostD B q_top cap mb φ G ns nt O T (j + 1) Alv Gam C'
      (killSet A₀ (markSet n Xa) (markSet n Wa)) σ σr := by
    exact levelPostD_restored (q := q) (c := c) (tail := tail) (bits := bits) hpostc
  have hscratchr : StreamScratchFrom B n cap mb ell (j + 1) σr := by
    apply hscratchc.congr
    intro a
    simp [σr, streamRestoredEnv]
  have harr (a : String)
      (ha : a ∈ [ordName j, cpsName j, xmmName j, asgName j, pdsName j]) :
      σc.arrs a = σs.arrs a :=
    hrc.frame_arr a (hframes.parent_arr a ha)
  have hdepth (a : String) (ha : Lax3Proofs.RamDriverWrites.BelowArr (j + 1) a) :
      σc.arrs a = σs.arrs a :=
    hrc.frame_arr a (hframes.below_arr a ha)
  have hbelowVar (y : String) (hy : Lax3Proofs.RamDriverWrites.BelowVar (j + 1) y) :
      σc.vars y = σs.vars y :=
    hrc.frame_var y (hframes.below_var y hy)
  refine ⟨σr, ?_, hpostr, ?_⟩
  · simpa only [streamInnerCom, σs, σr, Nat.add_assoc] using hrs.seq (hrc.seq hrr)
  · refine ⟨?_, hscratchr⟩
    refine
      { q_var := by simp [σr, streamRestoredEnv]
        centre_var := by simp [σr, streamRestoredEnv]
        pointer_var := by simp [σr, streamRestoredEnv]
        tail_var := by simp [σr, streamRestoredEnv]
        bits_var := by simp [σr, streamRestoredEnv]
        saved := by
          simpa [σr, StreamScalarsSaved, streamRestoredEnv, cnumName, curName,
            xpName, cixName, String.ext_iff] using hsavedc
        ord_arr := by
          simpa [σr, σs, streamRestoredEnv, streamSavedEnv] using
            (harr (ordName j) (by simp))
        mask_arr := by
          simpa [σr, σs, streamRestoredEnv, streamSavedEnv] using
            (harr (cpsName j) (by simp))
        row_arr := by
          simpa [σr, σs, streamRestoredEnv, streamSavedEnv] using
            (harr (xmmName j) (by simp))
        asg_arr := by
          simpa [σr, σs, streamRestoredEnv, streamSavedEnv] using
            (harr (asgName j) (by simp))
        dist_arr := by
          simpa [σr, σs, streamRestoredEnv, streamSavedEnv] using
            (harr (pdsName j) (by simp))
        depth_arr := fun a ha => by
          simpa [σr, σs, streamRestoredEnv, streamSavedEnv] using hdepth a ha
        round_var := fun a ha => by
          exact (hrr.frame_var _ (by
            simp [streamRestoreCom, Com.wvars, ctrName, cnumName, curName,
              xpName, cixName, String.ext_iff])).trans
            ((hbelowVar (ctrName a) ⟨a, by omega, by tauto⟩).trans
              (hrs.frame_var _ (by
                simp [streamSaveCom, Com.wvars, ctrName, cnumName, curName,
                  xpName, cixName, String.ext_iff])))
        connector_var := by
          exact (hrr.frame_var _ (by
            simp [streamRestoreCom, Com.wvars, ctrName, String.ext_iff])).trans
            ((hbelowVar (ctrName j) ⟨j, Nat.lt_succ_self j, by tauto⟩).trans
              (hrs.frame_var _ (by
                simp [streamSaveCom, Com.wvars, ctrName, cnumName, curName,
                  xpName, cixName, String.ext_iff])))
        member_count_var := by
          exact (hrr.frame_var _ (by
            simp [streamRestoreCom, Com.wvars, mnumName, String.ext_iff])).trans
            ((hbelowVar (mnumName j) ⟨j, Nat.lt_succ_self j, by tauto⟩).trans
              (hrs.frame_var _ (by
                simp [streamSaveCom, Com.wvars, mnumName, cnumName, curName,
                  xpName, cixName, String.ext_iff])))
        kill_count_var := by
          exact (hrr.frame_var _ (by
            simp [streamRestoreCom, Com.wvars, kkName, String.ext_iff])).trans
            ((hbelowVar (kkName j) ⟨j, Nat.lt_succ_self j, by tauto⟩).trans
              (hrs.frame_var _ (by
                simp [streamSaveCom, Com.wvars, kkName, cnumName, curName,
                  xpName, cixName, String.ext_iff])))
        out_eq := by
          simpa [σr, σs, streamRestoredEnv, streamSavedEnv] using houtc }

#print axioms StreamKillOut.childLevelPre
#print axioms StreamKillOut.childCallPre
#print axioms streamInnerSemanticStep
#print axioms childCallPreAtDepth

end Lax3Proofs.Refine.CoverActiveStreamInner
