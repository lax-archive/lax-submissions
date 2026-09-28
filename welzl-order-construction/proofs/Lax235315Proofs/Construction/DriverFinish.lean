import Lax235315Proofs.Construction.StoredHistory
import Lax235315Proofs.Construction.GuardedDriverSource

/-! The literal final success test, verified on both its output branches. -/
namespace Lax235315Proofs.Construction.DriverFinish
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlStraight
open Lax235315Proofs.Construction.StoredHistory
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.GuardedDriverSource
open Lax195003.WelzlOrdersInGraphs

/-- The finish routine always terminates. If it reports success, its actual
output is the certified order; rejected attempts take the natural-order path. -/
lemma finish_run {B c n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ} {σ : Env}
    (h : DriverPost B c n x σ) (hc : 1 ≤ c) (hn : 1 < n) (hnB : n < B)
    (hhistory : σ.vars "good" = 1 →
      Nonempty (Stored G (6 * c ^ 2 * Nat.clog 2 n) σ)) :
    ∃ τ, Run B finish σ τ (104 * (n + 1)) ∧
      τ.vars "good" = σ.vars "good" ∧ τ.inp = σ.inp ∧
      (τ.vars "good" = 1 →
        EncodesGraphWelzlOrder G 1 (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) τ.out) := by
  have htest := evalB_condEq (evalB_var (h.workspace.bounded.vars "good"))
    (evalB_lit (by omega : 1 < B))
  by_cases hg : σ.vars "good" = 1
  · obtain ⟨history⟩ := hhistory hg
    have hf : Frontier B c n x σ := by
      rcases h.status with hf | hf
      · exact hf
      · exact False.elim (hf.1 hg)
    obtain ⟨τ, hr, hout, hin⟩ := history.reconstructAndWrite_correct hf hc hn hnB (h.small hn)
    refine ⟨τ, ?_, hr.frame_var "good" (by decide), hin, fun _ => hout⟩
    exact (Run.ite_true (b := .eq (.var "good") (.lit 1))
      (by simpa only [hg, beq_self_eq_true] using htest) hr).mono
      (by simp [Cond.size, Expr.size]; omega)
  · obtain ⟨τ, hr, hout⟩ := writeNaturalOrder_run h.workspace.vertices hnB
    have hgood := hr.frame_var "good" (by decide)
    refine ⟨τ, ?_, hgood, hr.frame_inp (by decide), ?_⟩
    · exact (Run.ite_false (b := .eq (.var "good") (.lit 1))
        (by simpa only [beq_eq_false_iff_ne.mpr hg] using htest) hr).mono
        (by simp [Cond.size, Expr.size]; omega)
    · intro he
      exact False.elim (hg (hgood.symm.trans he))

end Lax235315Proofs.Construction.DriverFinish
