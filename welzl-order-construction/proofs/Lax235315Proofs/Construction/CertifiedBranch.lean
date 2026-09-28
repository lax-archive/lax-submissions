import Lax235315Proofs.Construction.CertificateFrontier

/-! Both branches after the near certificate, including rejection. -/
namespace Lax235315Proofs.Construction.CertifiedBranch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.CertificateFrontier
open Lax235315Proofs.Construction.TracePartitions

/-- The literal collision-free branch of a round. -/
def certifiedBranch : Com := seqs [buildReductionCertificate,
  .ite (.eq (.var "good") (.lit 1)) commitReduction (.assign "acount" (.lit 0))]

/-- The source either commits a shrinking frontier or resets the loop count
on rejection. This includes the actual test and both execution paths. -/
lemma certifiedBranch_run {B c n bound : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} {σ : Env} {W : Finset ℕ}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ) (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c) (view σ "ord") W)
    (hWr : ∀ v ∈ W, v < n)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ', Run B certifiedBranch σ σ' (2300 * (x.length + 1)) ∧
      ((Frontier B c n x σ' ∧ σ'.vars "round" = σ.vars "round" + 1 ∧
          σ'.vars "acount" ≤ σ.vars "acount" / 2 + c ^ 2) ∨
        (σ'.vars "good" ≠ 1 ∧ σ'.vars "acount" = 0)) := by
  obtain ⟨τ, hr, hcand⟩ := certificate_candidate_run hx hG h hc (by omega)
    hcsq hbound henum hWr hnB htargetB hdenomB hboundB
  have htbound := SourceBounds.run_preserves hr h.workspace.bounded
  have htest := evalB_condEq (evalB_var (htbound.vars "good"))
    (evalB_lit (by omega : 1 < B))
  have hac := hr.frame_var "acount" (by decide)
  have hround := hr.frame_var "round" (by decide)
  have hlen := hx.length_eq
  by_cases hg : τ.vars "good" = 1
  · have hcandidate := hcand hg
    obtain ⟨τ', hcommit, hfront, hrnext, hacnext⟩ :=
      hcandidate.commit hc hn (by omega) (by rwa [hac])
    have hrun := hr.seq (Run.ite_true (d := .assign "acount" (.lit 0)) (b := .eq (.var "good") (.lit 1)) (by simpa only [hg, beq_self_eq_true] using htest) hcommit)
    refine ⟨τ', hrun.mono ?_, Or.inl ⟨hfront, ?_, ?_⟩⟩
    · simp only [Cond.size, Expr.size]; omega
    · rwa [hround] at hrnext
    · rw [hacnext, hcandidate.nextCount]
      simpa only [hac] using hcandidate.shrinks
  · let τ' := τ.setVar "acount" 0
    have hreset : Run B (.assign "acount" (.lit 0)) τ τ' 2 :=
      Run.assign (evalB_lit (by omega))
    have hrun := hr.seq (Run.ite_false (c := commitReduction) (b := .eq (.var "good") (.lit 1)) (by simpa only [beq_eq_false_iff_ne.mpr hg] using htest) hreset)
    refine ⟨τ', hrun.mono ?_, Or.inr ⟨?_, ?_⟩⟩
    · simp only [Cond.size, Expr.size]; omega
    · simpa [τ'] using hg
    · simp [τ']

end Lax235315Proofs.Construction.CertifiedBranch
