import Lax3Proofs.Refine.CoverActiveCore
import Lax3Proofs.RamDriverMember

/-!
# Active-prefix cover compaction

Every active centre is alive and lies in its own cluster, so every block of
an active cover is nonempty.  Consequently the driver turn list is the
identity prefix `[0,q)`.  This file writes exactly that prefix, saves the
two scalar lengths, and produces `CoverHeldAtA` plus `Compacted` without a
carrier scan.
-/

namespace Lax3Proofs.Refine.CoverActiveCompact

open Lax3.ColoredGraphs
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover
open Lax3Proofs.RamCoverActive
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverMember
open Lax3Proofs.Refine.CoverActiveCore
open Lax3Proofs.Refine.CoverActiveRadixLoop
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## Mathematical identity compaction -/

variable {n q r xp : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre Xoff Xmem asg cps : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)}

/-- Every active block contains its centre. -/
theorem activeBlock_nonempty
    (hcentres : CentresBy n q A₀ π centre)
    (hcover : CoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    {c : ℕ} (hc : c < q) : Xoff c < Xoff (c + 1) := by
  have hin : InCluster (masked G A₀) π r (centre c) (centre c) :=
    ⟨hcentres.centre_lt c hc, hcentres.centre_lt c hc,
      self_mem_wreach _ _ _ _⟩
  obtain ⟨p, hp1, hp2, -⟩ := (hcover.block c hc (centre c)).mpr hin
  omega

/-- One nonempty block per active centre forces at least `q` arena cells. -/
theorem activeCount_le_arena
    (hcentres : CentresBy n q A₀ π centre)
    (hcover : CoverOutA G A₀ π centre r q xp Xoff Xmem asg) : q ≤ xp := by
  have hprefix : ∀ k, k ≤ q → k ≤ Xoff k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hi := ih (by omega)
        have hs := activeBlock_nonempty hcentres hcover (c := k) (by omega)
        omega
  have hq := hprefix q le_rfl
  rwa [hcover.last] at hq

/-- The identity active prefix satisfies the driver's compaction surface. -/
theorem compacted_identity
    (hcentres : CentresBy n q A₀ π centre)
    (hcover : CoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    (hcps : ∀ k < q, cps k = k) :
    Compacted q q xp A₀ centre Xoff cps := by
  refine
    { le_mass := activeCount_le_arena hcentres hcover
      le_carrier := le_rfl
      lt := ?_
      mono := ?_
      nonempty := ?_
      alive := ?_
      covers := ?_ }
  · intro k hk
    rw [hcps k hk]
    exact hk
  · intro k k' hkk' hk'
    rw [hcps k (lt_trans hkk' hk'), hcps k' hk']
    exact hkk'
  · intro k hk
    rw [hcps k hk]
    exact activeBlock_nonempty hcentres hcover hk
  · intro k hk
    rw [hcps k hk]
    exact hcentres.alive k hk
  · intro c hc _hne _halive
    exact ⟨c, hc, hcps c hc⟩

/-! ## Executable tail -/

/-- Fill the active turn list, save the cover pointer, and save its count. -/
def activeCompactCom (j : ℕ) : Com :=
  .seq (fillUpto (cpsName j) (.var "qn") (.var "i"))
    (.seq (.assign (xpName j) (.var "xp"))
      (.assign (cnumName j) (.var "qn")))

def activeCompactCost (q : ℕ) : ℕ := 11 * q + 10

variable {B ns nt j : ℕ} {O T : ℕ → ℕ}

/-- The active-prefix tail turns the direct core output into precisely the
retained-cover and compacted-list contracts consumed by the driver. -/
theorem activeCompact_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hqB : q < B) :
    Spec B
      (fun σ => ActiveCoreAtOut B q r j G A₀ π centre σ ∧
        ∃ cps₀, σ.arrs (cpsName j) = arrOf n cps₀)
      (activeCompactCom j)
      (fun _ σ' => σ'.vars "n" = n ∧ σ'.vars "qn" = q ∧
        σ'.arrs "elm" = arrOf n (fun _ => 0) ∧
        ∃ Xoff Xmem asg cps m,
          CoverHeldAtA B n q j G A₀ π centre r Xoff Xmem asg m σ' ∧
          σ'.arrs (cpsName j) = arrOf n cps ∧
          σ'.vars (cnumName j) = q ∧
          Compacted q q m A₀ centre Xoff cps)
      (activeCompactCost q) := by
  let Q : Env → Prop := ActiveCoreAtOut B q r j G A₀ π centre
  have hQfr : ∀ σ σ', Q σ →
      (∀ y, y ≠ "i" → σ'.vars y = σ.vars y) →
      (∀ b, b ≠ cpsName j → σ'.arrs b = σ.arrs b) → Q σ' := by
    intro σ σ' hQ hfv hfa
    obtain ⟨xp, Xoff, Xmem, asg, hxp, hxoff, hxmem, hasg, hcover, hxpB⟩ := hQ.cover
    refine
      { n_var := by rw [hfv "n" (by decide)]; exact hQ.n_var
        q_var := by rw [hfv "qn" (by decide)]; exact hQ.q_var
        centre_arr := by
          rw [hfa (ordName j) (by
            simp [ordName, cpsName, String.ext_iff])]
          exact hQ.centre_arr
        zero_mask := by
          rw [hfa "elm" (by simp [cpsName, String.ext_iff])]
          exact hQ.zero_mask
        cover := ⟨xp, Xoff, Xmem, asg, by
          rw [hfv "xp" (by decide)]; exact hxp, by
          rw [hfa (xofName j) (by simp [xofName, cpsName, String.ext_iff])]
          exact hxoff, by
          rw [hfa (xmmName j) (by simp [xmmName, cpsName, String.ext_iff])]
          exact hxmem, by
          rw [hfa (asgName j) (by simp [asgName, cpsName, String.ext_iff])]
          exact hasg, hcover, hxpB⟩ }
  have hbnd : ∀ σ, Q σ → (Expr.var "qn").evalB B σ = some q := by
    intro σ hQ
    simpa [hQ.q_var] using
      (evalB_var (B := B) (σ := σ) (x := "qn") (by rw [hQ.q_var]; exact hqB))
  have hcell : ∀ σ, Q σ → σ.vars "i" < q →
      (Expr.var "i").evalB B σ = some ((fun k => k) (σ.vars "i")) := by
    intro σ _ hi
    exact evalB_var (lt_trans hi hqB)
  intro σ hpre
  obtain ⟨hcore, cps₀, hcps₀⟩ := hpre
  obtain ⟨σ₁, rfill, ⟨cps', hcps₁, hcpsCells⟩, _hi, hcore₁⟩ :=
    (Lax3Proofs.RamDriverCompose.fillPrefix_spec q n (cpsName j)
      (.var "qn") (.var "i") (fun k => k) Q (by omega) hqB hcentres.count_le
      hQfr hbnd hcell).run (σ := σ) ⟨⟨cps₀, hcps₀⟩, hcore⟩
  obtain ⟨xp, Xoff, Xmem, asg, hxp₁, hxoff₁, hxmem₁, hasg₁, hcover, hxpB⟩ :=
    hcore₁.cover
  have halloc : xp ≤ n * n :=
    raw_arena_le (RawCoverOutA.of_sorted hcover)
  let σ₂ := σ₁.setVar (xpName j) xp
  have rxp : Run B (.assign (xpName j) (.var "xp")) σ₁ σ₂ 2 := by
    apply Run.assign
    simpa [hxp₁] using
      (evalB_var (B := B) (σ := σ₁) (x := "xp") (by rw [hxp₁]; exact hxpB))
  have hqn₂ : σ₂.vars "qn" = q := by
    simp [σ₂, xpName, String.ext_iff, hcore₁.q_var]
  let σ₃ := σ₂.setVar (cnumName j) q
  have rcnum : Run B (.assign (cnumName j) (.var "qn")) σ₂ σ₃ 2 := by
    apply Run.assign
    simpa [hqn₂] using
      (evalB_var (B := B) (σ := σ₂) (x := "qn") (by rw [hqn₂]; exact hqB))
  have hcore₃ : ActiveCoreAtOut B q r j G A₀ π centre σ₃ := by
    refine
      { n_var := by
          simp [σ₃, σ₂, xpName, cnumName, String.ext_iff, hcore₁.n_var]
        q_var := by
          simp [σ₃, σ₂, xpName, cnumName, String.ext_iff, hcore₁.q_var]
        centre_arr := by simp [σ₃, σ₂, hcore₁.centre_arr]
        zero_mask := by simp [σ₃, σ₂, hcore₁.zero_mask]
        cover := ⟨xp, Xoff, Xmem, asg, by
          simp [σ₃, σ₂, xpName, cnumName, String.ext_iff, hxp₁], by
          simp [σ₃, σ₂, hxoff₁], by simp [σ₃, σ₂, hxmem₁], by
          simp [σ₃, σ₂, hasg₁], hcover, hxpB⟩ }
  refine ⟨σ₃, ?_, hcore₃.n_var, hcore₃.q_var, hcore₃.zero_mask, ?_⟩
  · have hr := rfill.seq (rxp.seq rcnum)
    simpa [activeCompactCom, activeCompactCost] using hr
  · have hxpSaved : σ₃.vars (xpName j) = xp := by
      simp [σ₃, σ₂, xpName, cnumName, String.ext_iff]
    have hcnum : σ₃.vars (cnumName j) = q := by simp [σ₃]
    have hcps₃ : σ₃.arrs (cpsName j) = arrOf n cps' := by
      simp [σ₃, σ₂, hcps₁]
    refine ⟨Xoff, Xmem, asg, cps', xp, ?_, hcps₃, hcnum,
      compacted_identity hcentres hcover hcpsCells⟩
    exact
      { centre_arr := hcore₃.centre_arr
        off_arr := hxoff₁
        mem_arr := hxmem₁
        asg_arr := hasg₁
        pointer := hxpSaved
        alloc := halloc
        pointer_lt := hxpB
        centre_lt := hcentres.centre_lt
        cover := hcover }

/-! ## Axiom audit -/

#print axioms compacted_identity
#print axioms activeCompact_spec

end Lax3Proofs.Refine.CoverActiveCompact
