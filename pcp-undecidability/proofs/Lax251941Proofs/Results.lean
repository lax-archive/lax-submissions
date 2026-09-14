import Lax251941.AcceptanceUndecidable
import Lax251941.TuringCompleteness
import Lax251941.TapeAcceptanceUndecidable
import Lax251941.PostCorrespondenceReduction
import Lax251941.PostCorrespondenceUndecidable
import Lax251941.PostCorrespondenceIndexUndecidable
import Lax251941Proofs.Bridge

/-!
The six statements of the submission, transported from the ported source
development through `Lax251941Proofs.Bridge`.
-/

namespace Lax251941Proofs.Results

open Lax251941.Acceptance Lax251941.TuringMachines Lax251941.PostCorrespondence
open Lax251941Proofs.Bridge

/--
---
conclusion: Lax251941.AcceptanceUndecidable.not_turingDecidable_ATM
---
The acceptance problem `A_TM` is undecidable (Sipser, Theorem 4.11).

# Proof strategy

Diagonalisation, as in the textbook: a decider `H` for `A_TM` yields, by
programming (`Nat.Partrec.Code.exists_code`), a machine `D` that accepts the
code of a machine `N` exactly when `N` does not accept its own code
(`Acceptance.exists_flip_machine` in the source); `D` on its own code is a
contradiction (`Acceptance.no_diagonal_machine`). The concept's definitions of
machines, acceptance and `A_TM` are the source's, so the source theorem is the
statement.

# Attribution

Sipser, *Introduction to the Theory of Computation*, Theorem 4.11; Lean proof
by Aristotle (`Acceptance.atm_not_turingDecidable`).
-/
theorem not_turingDecidable_ATM : ¬ TuringDecidable ATM :=
  Acceptance.atm_not_turingDecidable

/--
---
conclusion: Lax251941.TuringCompleteness.exists_tm_accepts_iff_dom
---
Every partial recursive function is computed, in the accept-iff-defined sense on
unary inputs, by a single-tape Turing machine.

# Proof strategy

The source compiles the function, presented through mathlib's `Nat.Partrec'`,
to a counter-machine program (`Sim/Compile.lean`), and the program to a tape
machine that walks over a tape of cells holding the counters
(`Sim/Simulate.lean`); `PCP.Sim.exists_tape_machine` assembles the two. The
concept's machine is the source's machine transported by `ofSrc`, and
acceptance is transported by `accepts_iff`.

# Attribution

Lean development by Aristotle (`RequestProject/Sim/`); the statement is the
Turing-completeness of Sipser's machines in the form the reduction needs.
-/
theorem exists_tm_accepts_iff_dom (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ (M : TM) (mk c : ℕ), ∀ n : ℕ, M.Accepts (mk :: List.replicate n c) ↔ (f n).Dom := by
  obtain ⟨M, mk, c, hM⟩ := PCP.Sim.exists_tape_machine f hf
  exact ⟨ofSrc M, mk, c, fun n => by rw [accepts_iff, toSrc_ofSrc]; exact hM n⟩

/--
---
conclusion: Lax251941.TapeAcceptanceUndecidable.not_computablePred_accepts
---
The acceptance problem for single-tape Turing machines is undecidable.

# Proof strategy

A decision procedure for the tape machines would decide `A_TM`: the partial
function whose domain is `A_TM` is partial recursive, so by Turing-completeness
one fixed tape machine accepts the unary encoding of `n` exactly when
`n ∈ A_TM`, and the decision procedure applied to that machine and the unary
inputs decides `A_TM` (`Acceptance.tm_acceptance_not_computablyDecidable`).
The bridge `computablePred_accepts_iff` moves between the concept's machines
and the source's.

# Attribution

Sipser, Theorem 4.11 for the tape machines of Section 5.2; Lean proof by
Aristotle (`RequestProject/Acceptance/Bridge.lean`).
-/
theorem not_computablePred_accepts :
    ¬ ComputablePred fun p : TM × List ℕ => p.1.Accepts p.2 := by
  rw [computablePred_accepts_iff]
  exact Acceptance.tm_acceptance_not_computablyDecidable

/--
---
conclusion: Lax251941.PostCorrespondenceReduction.computablePred_accepts_of_hasMatch
---
Sipser's Theorem 5.15 as a many-one reduction: a decision procedure for the
Post correspondence problem over `ℕ` decides the acceptance problem for Turing
machines.

# Proof strategy

The source builds Sipser's instance `sipserPCP M w` over the alphabet `Sym` of
configurations, proves that its matches are exactly the accepting computation
histories (`PCP.hasMatch_sipserPCP_iff`, through the modified problem and the
`⋆` trick, `PCP/SRtoMPCP.lean` and `PCP/StarTrick.lean`), and that the
construction is primitive recursive (`PCP/Computable.lean`);
`PCP.computablyDecidable_acceptance_of_pcp` is the reduction. The concept
states both problems over `ℕ`: the bridge moves the given decision procedure
from `ℕ` to `Sym` along the injective encoding of `Sym`, which preserves and
reflects matches (`computablyDecidable_hasMatch_sym`), and the resulting
procedure for the source's machines to the concept's
(`computablePred_accepts_iff`).

# Attribution

Sipser, Theorem 5.15 (Section 5.2); Lean proof by Aristotle
(`RequestProject/PCP/`).
-/
theorem computablePred_accepts_of_hasMatch
    (h : ComputablePred fun P : Inst ℕ => HasMatch P) :
    ComputablePred fun p : TM × List ℕ => p.1.Accepts p.2 := by
  rw [computablePred_accepts_iff]
  exact PCP.computablyDecidable_acceptance_of_pcp (computablyDecidable_hasMatch_sym h)

/--
---
conclusion: Lax251941.PostCorrespondenceUndecidable.not_computablePred_hasMatch
---
The Post correspondence problem over `ℕ` is undecidable: glued from the
reduction and the undecidability of acceptance for tape machines, taken as
assumptions.
-/
theorem not_computablePred_hasMatch : ¬ ComputablePred fun P : Inst ℕ => HasMatch P :=
  fun h => Lax251941.TapeAcceptanceUndecidable.not_computablePred_accepts
    (Lax251941.PostCorrespondenceReduction.computablePred_accepts_of_hasMatch h)

/--
---
conclusion: Lax251941.PostCorrespondenceIndexUndecidable.not_computablePred_solvable
---
The Post correspondence problem in index form is undecidable.

# Proof strategy

The source proves it from the domino form over `Sym`
(`Acceptance.hasMatch_not_computablyDecidable`), passing between dominos and
indices (`PCPIndex.solvable_iff_hasMatch`) and along the primitive recursive
injection of `Sym` into `ℕ` (`PCPIndex.solvable_mapInst_iff`,
`PCPIndex.primrec_mapInst`); the concept's `Solvable` is the source's.

# Attribution

Lean proof by Aristotle (`RequestProject/PCP/Index.lean`); the index form is
the one the book *Transducers* consumes.
-/
theorem not_computablePred_solvable : ¬ ComputablePred Solvable :=
  Transducers.PCP.solvable_not_computablePred

end Lax251941Proofs.Results
