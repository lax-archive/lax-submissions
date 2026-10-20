import Lax457868Proofs.RefinedProgramSource
import Lax808846Proofs.Compile

/-! Compute the fixed program's memory layout from its source syntax, then
check the existing compiler's exact compilability predicate in the kernel. -/
namespace Lax457868Proofs.RefinedProgramLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax457868Proofs.ClockedSource
open Lax457868Proofs.RefinedProgramSource

private def expressionOkDecidable (L : Layout) :
    (e : Expr) → (d : ℕ) → Decidable (Expr.Ok L e d)
  | .lit _, _ => isTrue trivial
  | .var x, _ => inferInstanceAs (Decidable (x ∈ L.scalars))
  | .get a i, d => by
      letI := expressionOkDecidable L i d
      exact inferInstanceAs (Decidable (a ∈ L.arrays ∧ Expr.Ok L i d ∧ d < L.temps))
  | .bin _ e f, d => by
      letI := expressionOkDecidable L f d
      letI := expressionOkDecidable L e (d + 1)
      exact inferInstanceAs
        (Decidable (Expr.Ok L f d ∧ Expr.Ok L e (d + 1) ∧ d < L.temps))

private def commandOkDecidable (L : Layout) : (c : Com) → Decidable (Com.Ok L c)
  | .skip => isTrue trivial
  | .assign x e => by
      letI := expressionOkDecidable L e 0
      exact inferInstanceAs (Decidable (x ∈ L.scalars ∧ Expr.Ok L e 0))
  | .store a i e => by
      letI := expressionOkDecidable L i 0
      letI := expressionOkDecidable L e 1
      exact inferInstanceAs
        (Decidable (a ∈ L.arrays ∧ Expr.Ok L i 0 ∧ Expr.Ok L e 1 ∧ 0 < L.temps))
  | .seq c d => by
      letI := commandOkDecidable L c
      letI := commandOkDecidable L d
      exact inferInstanceAs (Decidable (Com.Ok L c ∧ Com.Ok L d))
  | .ite b c d => by
      letI := expressionOkDecidable L (condExpr b) 0
      letI := commandOkDecidable L c
      letI := commandOkDecidable L d
      exact inferInstanceAs
        (Decidable (Expr.Ok L (condExpr b) 0 ∧ Com.Ok L c ∧ Com.Ok L d))
  | .while b c => by
      letI := expressionOkDecidable L (condExpr b) 0
      letI := commandOkDecidable L c
      exact inferInstanceAs (Decidable (Expr.Ok L (condExpr b) 0 ∧ Com.Ok L c))
  | .read x => inferInstanceAs (Decidable (x ∈ L.scalars))
  | .write e => by
      letI := expressionOkDecidable L e 0
      exact inferInstanceAs (Decidable (Expr.Ok L e 0 ∧ 0 < L.temps))

/-- The distinct names computed from the fixed source, with its computed
maximum expression depth of four. The compiler predicate below verifies
that this explicit layout covers every instruction. -/
def programLayout : Layout :=
  ⟨["c", "n", "m", "len", "i", "tmp", "L", "qpow", "v", "acount", "good", "round", "removedCount", "drawModulus", "drawSavedN", "drawSavedQ", "cutOne", "cutTwo", "cut64", "cut768", "cutA", "cutB", "cutResult", "cutC2", "cutC3", "cutC4", "cutC5", "cutS", "cutSPlusOne", "cutP", "cutQ", "cutR", "cutK", "cutoffResult", "refinedLogC", "activeBCount", "__clockBlockSize", "__clockBlocksLeft", "__clockSlotsLeft", "__clockTimedOut", "__clockContinue", "alen", "activePackCursor", "sampleCount", "vcount", "classCount", "ti", "token", "t", "markedLen", "touchedLen", "j", "jend", "cl", "nextBCount", "domainPackCursor", "samplerDenom", "repairSampleSize", "samplerCapDenom", "batchTarget", "exceptionCap", "nearBound", "repairFarBound", "initialRetryCap", "repairRetryCap", "drawCap", "initialDomainSize", "initialBatchTarget", "initialRetriesLeft", "initialRetryStatus", "attemptAccepted", "drawCount", "batchStop", "batchFailed", "drawUsed", "drawFound", "drawValue", "drawStop", "digit", "bit", "drawVertex", "drawCursor", "sampleCursor", "sum", "pos", "repIndex", "drawOffset", "repFailed", "repStop", "a", "neighborLen", "b", "r", "diff", "exceptionCount", "exceptionCursor", "phase2Cursor", "phase2OldCount", "repairClassTotal", "repairClassCursor", "repairClassTmp", "exceptionIndex", "exceptionStop", "repairRetryStatus", "repairB", "repairRep", "repairBLen", "repairRLen", "repairCursor", "repairClearCursor", "repairRetriesLeft", "repairClass", "repairStart", "repairStop", "trialDesiredLen", "repairScanSuccess", "repairScanCursor", "trialVertex", "trialRowLen", "trialDiffCount", "trialFilterCursor", "trialTraceEqual", "nextACount", "head", "last", "iend"],
    ["off", "tgt", "activeA", "activeB", "ord", "classSize", "markedCount", "stamp", "classB", "marked", "touched", "split",
  "nextB", "repClass", "repsB", "repB", "nextA", "drawDomain", "sampleFlags", "key0", "sampleDraws", "count",
  "scratchOrder", "degree", "inter", "neighbors", "exceptionFlags", "exceptionList", "repairClassStart", "repairBMarks",
  "repairBList", "repairRMarks", "repairRList", "trialActive", "trialDesiredMarks", "trialDesiredList", "trialRowMarks",
  "trialRowList", "trialDiffList", "classA", "repsA", "repA", "roundStart", "removed", "removedRep", "roundEnd",
  "nextVertex"], 4⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma programSource_ok (D : ℕ) : Com.Ok programLayout (programSource D) := by
  letI := commandOkDecidable programLayout (programSource D)
  exact of_decide_eq_true rfl

/-- The word-budget multiplier is derived from the layout's actual sizes. -/
def layoutFactor : ℕ :=
  programLayout.temps + 2 + programLayout.scalars.length +
    programLayout.arrays.length + 1

lemma layoutFactor_pos : 0 < layoutFactor := by
  unfold layoutFactor
  omega

lemma programLayout_fits {B w : ℕ} (hB : 1 < B)
    (hscale : layoutFactor * B ≤ 2 ^ w) :
    programLayout.FitsWords B w := by
  have hfactor := layoutFactor_pos
  refine ⟨hB, ?_, ?_⟩
  · have hh : B ≤ layoutFactor * B := by nlinarith
    exact hh.trans hscale
  · have hs : programLayout.span B ≤ layoutFactor * B := by
      dsimp [Layout.span, layoutFactor]
      nlinarith
    exact hs.trans hscale

/-- The theorem's scaled input-word premise supplies both memory addresses
and all source word bounds. No additional word-size assumption is needed. -/
lemma fitted_bound_of_input_scale (J c w : ℕ) (x : List ℕ) (hJ : 2 ≤ J)
    (hscale : ∀ v ∈ c :: x,
      layoutFactor * J * (x.length + v + 1) ≤ 2 ^ w) :
    let B := 2 ^ w / layoutFactor
    programLayout.FitsWords B w ∧ J * (x.length + 1) ≤ B ∧
      ∀ v ∈ c :: x, v < B := by
  let B := 2 ^ w / layoutFactor
  have hfit (v : ℕ) (hv : v ∈ c :: x) :
      J * (x.length + v + 1) ≤ B := by
    apply (Nat.le_div_iff_mul_le layoutFactor_pos).mpr
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscale v hv
  have hc := hfit c (by simp)
  have hbase : J * (x.length + 1) ≤ B := by nlinarith
  have hB : 1 < B := by nlinarith
  refine ⟨programLayout_fits hB ?_, hbase, ?_⟩
  · exact (Nat.mul_div_le (2 ^ w) layoutFactor)
  · intro v hv
    change v < B
    have hh := hfit v hv
    nlinarith

end Lax457868Proofs.RefinedProgramLayout
