/-
# Undecidability of the Post Correspondence Problem

Sipser's Theorem 5.15 states that `PCP` is undecidable, and its proof is a reduction from
`A_TM`, the acceptance problem for Turing machines.  Sipser proves the undecidability of
`A_TM` earlier (Theorem 4.11, Section 4.2); Section 5.2 *uses* it.  Accordingly, the final
statement here is the reduction in its sharpest form:

  if the Post Correspondence Problem were decidable, then the acceptance problem for
  Turing machines would be decidable as well;

equivalently, PCP is undecidable as soon as `A_TM` is.  All the mathematical content of
Section 5.2 — the construction of the instance, the equivalence between matches and
accepting computation histories, and the effectiveness of the construction — is proved.
-/
import Lax251941Proofs.Source.PCP.Computable

namespace Lax251941Proofs.PCP

/-- A predicate is *computably decidable* if some computable Boolean-valued function
decides it. -/
def ComputablyDecidable {α : Type} [Primcodable α] (p : α → Prop) : Prop :=
  ∃ f : α → Bool, Computable f ∧ ∀ a, f a = true ↔ p a

/-- `A_TM`, the acceptance problem: given a machine and an input word, does the machine
accept the word? -/
def AcceptanceProblem (p : Arg) : Prop := p.1.Accepts p.2

/-- **Sipser's Theorem 5.15, as a many-one reduction.**  A decision procedure for the
Post Correspondence Problem would yield a decision procedure for the acceptance problem
for Turing machines: the map `(M, w) ↦ sipserPCP M w` is computable (indeed primitive
recursive) and `sipserPCP M w` has a match precisely when `M` accepts `w`. -/
theorem computablyDecidable_acceptance_of_pcp
    (h : ComputablyDecidable fun P : Inst Sym => HasMatch P) :
    ComputablyDecidable AcceptanceProblem := by
  obtain ⟨g, hg, hgspec⟩ := h
  refine ⟨fun p => g (sipserPCP p.1 p.2), hg.comp computable_sipserPCP, fun p => ?_⟩
  rw [hgspec]
  exact hasMatch_sipserPCP_iff p.1 p.2

/-- **The Post Correspondence Problem is undecidable**, given the undecidability of the
acceptance problem for Turing machines (Sipser's Theorem 4.11, which Section 5.2 takes as
its starting point). -/
theorem hasMatch_not_computablyDecidable
    (hATM : ¬ ComputablyDecidable AcceptanceProblem) :
    ¬ ComputablyDecidable fun P : Inst Sym => HasMatch P :=
  fun h => hATM (computablyDecidable_acceptance_of_pcp h)

end Lax251941Proofs.PCP
