/-
# From Section 4.2 to Section 5.2

Section 5.2 of the book reduces the acceptance problem to the Post Correspondence
Problem, and concludes that the latter is undecidable *because* the former is
(Section 4.2).  In this development the two sections use two different machine models:

* Section 4.2 (`RequestProject/Acceptance/Basic.lean`) works with the partial recursive
  programs `Nat.Partrec.Code`, for which the universal machine and the ability to program
  a new machine — the two ingredients of Sipser's diagonalization — are available;
* Section 5.2 (`RequestProject/PCP/`) works with tape machines whose configurations are
  strings, since the reduction to PCP manipulates computation histories.

What links the two is the Turing-completeness of the tape machines, proved in
`RequestProject/Sim/`: every partial recursive function is simulated by a tape machine
(`PCP.Sim.exists_tape_machine`).  Only one such simulation is needed here, since a
decision procedure for the acceptance problem is uniform in the machine: the machine
simulating a fixed universal function may be held fixed, and only its input word varies.

Consequently the results of this file are unconditional: the acceptance problem for the
tape machines of Section 5.2 is undecidable, and so is the Post Correspondence Problem.
-/
import Lax251941Proofs.Source.Acceptance.Basic
import Lax251941Proofs.Source.PCP.Undecidable
import Lax251941Proofs.Source.Sim.Universal

namespace Lax251941Proofs.Acceptance

/-- The partial function whose domain is `A_TM`: on input `⟨M, w⟩` it runs `M` on `w` and
converges precisely when the output is `1`. -/
noncomputable def atmFun : ℕ →. ℕ := fun n =>
  ((Denumerable.ofNat Machine n.unpair.1).eval n.unpair.2).bind
    fun y => cond (decide (y = 1)) (Part.some 0) Part.none

lemma partrec_atmFun : Partrec atmFun := by
  have hu : Partrec fun n : ℕ =>
      (Denumerable.ofNat Machine n.unpair.1).eval n.unpair.2 :=
    Nat.Partrec.Code.eval_part.comp
      ((Computable.ofNat _).comp (Primrec.fst.comp Primrec.unpair).to_comp)
      (Primrec.snd.comp Primrec.unpair).to_comp
  refine hu.bind ?_
  obtain ⟨_, h⟩ := (Primrec.eq.comp Primrec.snd (Primrec.const 1) :
    PrimrecPred fun p : ℕ × ℕ => p.2 = 1)
  have hc := Partrec.cond (c := fun p : ℕ × ℕ => decide (p.2 = 1))
    ((h.of_eq fun p => by simp).to_comp) (Computable.const 0).partrec Partrec.none
  refine hc.of_eq fun p => ?_
  by_cases hp : p.2 = 1 <;> simp [hp]

lemma dom_atmFun (n : ℕ) : (atmFun n).Dom ↔ n ∈ ATM := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp h
    rw [atmFun, Part.mem_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hy1 : y = 1 := by
      by_contra hne
      simp [hne] at hz
    subst hy1
    exact Part.eq_some_iff.mpr hy
  · intro h
    have hy : (1 : ℕ) ∈ (Denumerable.ofNat Machine n.unpair.1).eval n.unpair.2 :=
      Part.eq_some_iff.mp h
    refine Part.dom_iff_mem.mpr ⟨0, ?_⟩
    rw [atmFun, Part.mem_bind_iff]
    exact ⟨1, hy, by simp⟩

/-- **The acceptance problem for the tape machines of Section 5.2 is undecidable.**  A
decision procedure for it would decide `A_TM`, contradicting Sipser's Theorem 4.11. -/
theorem tm_acceptance_not_computablyDecidable :
    ¬ PCP.ComputablyDecidable PCP.AcceptanceProblem := by
  rintro ⟨g, hg, hgspec⟩
  obtain ⟨M, mk, c, hM⟩ := PCP.Sim.exists_tape_machine atmFun partrec_atmFun
  refine atm_not_turingDecidable ?_
  rw [turingDecidable_iff_computablePred]
  refine ⟨Classical.decPred _, ?_⟩
  have hcomp : Computable fun n : ℕ => g (M, mk :: List.replicate n c) :=
    hg.comp ((Computable.const M).pair (PCP.Sim.computable_unaryInput mk c))
  refine hcomp.of_eq fun n => ?_
  refine Bool.eq_iff_iff.2 ?_
  have key : g (M, mk :: List.replicate n c) = true ↔ n ∈ ATM := by
    rw [hgspec]
    exact (hM n).trans (dom_atmFun n)
  simpa using key

/-- **The Post Correspondence Problem is undecidable.**  This combines Sipser's
Theorem 4.11 (Section 4.2) with the reduction of Theorem 5.15 (Section 5.2). -/
theorem hasMatch_not_computablyDecidable :
    ¬ PCP.ComputablyDecidable fun P : PCP.Inst PCP.Sym => PCP.HasMatch P :=
  PCP.hasMatch_not_computablyDecidable tm_acceptance_not_computablyDecidable

end Lax251941Proofs.Acceptance
