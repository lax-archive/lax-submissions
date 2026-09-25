import Lax235315Proofs.Construction.RefineSplitMath
import Lax235315Proofs.Construction.MarkingSource
import Mathlib.Tactic

/-! Source-level verification of the touched-class allocation loop in
`refineOne`. -/

namespace Lax235315Proofs.Construction.RefineSplitSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RefineSplitMath
open Lax235315Proofs.Construction.WelzlProgram

/-- The concrete loop body which allocates a compact label for every partial
class on the touched stack. -/
def refineSplitBody : Com :=
  seqs [
    .assign "cl" (.get "touched" (.var "i")),
    .ite (.lt (.get "markedCount" (.var "cl"))
        (.get "classSize" (.var "cl")))
      (seqs [
        .store "split" (.var "cl") (.var "classCount"),
        .store "classSize" (.var "classCount")
          (.get "markedCount" (.var "cl")),
        .store "classSize" (.var "cl")
          (.sub (.get "classSize" (.var "cl"))
            (.get "markedCount" (.var "cl"))),
        inc "classCount"])
      (.store "split" (.var "cl") (.var "cl")),
    inc "i"]

/-- Machine invariant of the allocation loop.  Unprocessed old classes still
carry their original sizes, while `SplitPrefix` describes all split cells
already written. -/
def SplitInv (n base height : ℕ) (entry : ℕ → ℕ) (touched : Finset ℕ)
    (counts oldSize : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ (current : ℕ) (split workSize : ℕ → ℕ),
    τ.vars "i" ≤ height ∧ height ≤ n ∧
    τ.vars "n" = n ∧ τ.vars "touchedLen" = height ∧
    τ.vars "classCount" = current ∧
    τ.arrs "touched" = arrOf n entry ∧
    τ.arrs "markedCount" = arrOf n counts ∧
    τ.arrs "classSize" = arrOf n workSize ∧
    τ.arrs "split" = arrOf n split ∧
    PrefixEnumerates height entry touched ∧
    (∀ q ∈ touched, q < base) ∧
    SplitPrefix base current (processedClasses (τ.vars "i") entry)
      counts oldSize split ∧
    SplitSizes (processedClasses (τ.vars "i") entry)
      counts oldSize split workSize ∧
    ∀ q < base, q ∉ processedClasses (τ.vars "i") entry →
      workSize q = oldSize q

lemma splitInv_initial
    {n base height : ℕ} {entry counts oldSize split : ℕ → ℕ}
    {touched : Finset ℕ} {σ : Env}
    (hi : σ.vars "i" = 0) (hheight : height ≤ n)
    (hn : σ.vars "n" = n) (htouchedLen : σ.vars "touchedLen" = height)
    (hclassCount : σ.vars "classCount" = base)
    (htouched : σ.arrs "touched" = arrOf n entry)
    (hcounts : σ.arrs "markedCount" = arrOf n counts)
    (hsize : σ.arrs "classSize" = arrOf n oldSize)
    (hsplit : σ.arrs "split" = arrOf n split)
    (henum : PrefixEnumerates height entry touched)
    (hrange : ∀ q ∈ touched, q < base) :
    SplitInv n base height entry touched counts oldSize σ := by
  refine ⟨base, split, oldSize, by omega, hheight, hn, htouchedLen,
    hclassCount, htouched, hcounts, hsize, hsplit, henum, hrange, ?_, ?_, ?_⟩
  · simpa [hi, processedClasses] using splitPrefix_empty base counts oldSize split
  · simpa [hi, processedClasses] using
      splitSizes_empty counts oldSize split oldSize
  · intro q hq hnot
    rfl

private lemma splitBody_spec
    {B n base height : ℕ} {entry counts oldSize : ℕ → ℕ}
    {touched : Finset ℕ}
    (hnB : n < B) (honeB : 1 < B)
    (hcapacity : base +
      (touched.filter fun q => counts q < oldSize q).card ≤ n)
    (hcountsB : ∀ q < n, counts q < B)
    (hsizeB : ∀ q < base, oldSize q < B) :
    Spec B
      (fun τ => SplitInv n base height entry touched counts oldSize τ ∧
        τ.vars "i" < height)
      refineSplitBody
      (fun τ τ' => SplitInv n base height entry touched counts oldSize τ' ∧
        τ'.vars "i" = τ.vars "i" + 1)
      100 := by
  intro τ hτ
  rcases hτ with ⟨⟨current, split, workSize, hile, hheight, hn,
    htouchedLen, hcurrent, hentry, hcounts, hwork, hsplit, henum,
    hrange, hprefix, hsplitSizes, hunprocessed⟩, hilt⟩
  let processed := processedClasses (τ.vars "i") entry
  let q := entry (τ.vars "i")
  have hnext :=
    Lax235315Proofs.Construction.RefineSplitMath.PrefixEnumerates.next_mem_not_processed
      henum hilt
  have hqTouched : q ∈ touched := hnext.1
  have hqNot : q ∉ processed := hnext.2
  have hqBase : q < base := hrange q hqTouched
  have hbaseCurrent : base ≤ current := by
    rw [hprefix.1]
    omega
  have hqCurrent : q ≠ current := by omega
  have hqN : q < n := hqBase.trans_le
    (hbaseCurrent.trans
      ((Lax235315Proofs.Construction.RefineSplitMath.SplitPrefix.current_le hprefix
        (Lax235315Proofs.Construction.RefineSplitMath.PrefixEnumerates.processedClasses_subset
          henum hile)).trans hcapacity))
  have hiB : τ.vars "i" < B := (hilt.trans_le hheight).trans hnB
  have hqB : q < B := hqN.trans hnB
  have hcountB : counts q < B := hcountsB q hqN
  have hsizeEq : workSize q = oldSize q :=
    hunprocessed q hqBase hqNot
  have hsizeqB : workSize q < B := hsizeEq ▸ hsizeB q hqBase
  have hentryGet : (τ.arrs "touched")[τ.vars "i"]? = some q := by
    rw [hentry, getElem?_arrOf entry (hilt.trans_le hheight)]
  have hentryEval : (Expr.get "touched" (.var "i")).evalB B τ = some q :=
    evalB_get (evalB_var hiB) hentryGet hqB
  let τ₁ := τ.setVar "cl" q
  have rcl : Run B (.assign "cl" (.get "touched" (.var "i"))) τ τ₁ 6 :=
    (Run.assign hentryEval).mono (by norm_num [Expr.size])
  have hcountGet : (τ₁.arrs "markedCount")[τ₁.vars "cl"]? =
      some (counts q) := by
    simp [τ₁, hcounts, getElem?_arrOf counts hqN]
  have hcountEval : (Expr.get "markedCount" (.var "cl")).evalB B τ₁ =
      some (counts q) :=
    evalB_get (evalB_var hqB) hcountGet hcountB
  have hsizeGet : (τ₁.arrs "classSize")[τ₁.vars "cl"]? =
      some (workSize q) := by
    simp [τ₁, hwork, getElem?_arrOf workSize hqN]
  have hsizeEval : (Expr.get "classSize" (.var "cl")).evalB B τ₁ =
      some (workSize q) :=
    evalB_get (evalB_var hqB) hsizeGet hsizeqB
  let test := Cond.lt (.get "markedCount" (.var "cl"))
    (.get "classSize" (.var "cl"))
  by_cases hpartial : counts q < oldSize q
  · have htest : test.evalB B τ₁ = some true := by
      have := evalB_condLt hcountEval hsizeEval
      simpa [test, hsizeEq, hpartial] using this
    have hprocessedSub : processed ⊆ touched :=
      Lax235315Proofs.Construction.RefineSplitMath.PrefixEnumerates.processedClasses_subset
        henum hile
    have hcurrentLt : current < base +
        (touched.filter fun r => counts r < oldSize r).card :=
      Lax235315Proofs.Construction.RefineSplitMath.SplitPrefix.current_lt_of_unprocessed_partial
        hprefix hprocessedSub hqTouched hqNot hpartial
    have hcurrentN : current < n := hcurrentLt.trans_le hcapacity
    have hcurrentB : current < B := hcurrentN.trans hnB
    let τ₂ := τ₁.setArr "split" q current
    have rsplit : Run B (.store "split" (.var "cl") (.var "classCount"))
        τ₁ τ₂ 3 := by
      apply Run.store (evalB_var hqB)
      · rw [evalB_var_iff]
        simp [τ₁, hcurrent, hcurrentB]
      · simpa [τ₁, hsplit, length_arrOf] using hqN
    let τ₃ := τ₂.setArr "classSize" current (counts q)
    have rnewSize : Run B
        (.store "classSize" (.var "classCount")
          (.get "markedCount" (.var "cl"))) τ₂ τ₃ 7 := by
      have hccEval : (Expr.var "classCount").evalB B τ₂ = some current := by
        rw [evalB_var_iff]
        simp [τ₂, τ₁, hcurrent, hcurrentB]
      have hcountEval₂ :
          (Expr.get "markedCount" (.var "cl")).evalB B τ₂ =
            some (counts q) := by
        simpa [τ₂] using hcountEval
      have hlen : current < (τ₂.arrs "classSize").length := by
        simpa [τ₂, τ₁, hwork, length_arrOf] using hcurrentN
      exact (Run.store hccEval hcountEval₂ hlen).mono (by norm_num [Expr.size])
    let workSize' := upd (upd workSize current (counts q)) q
      (oldSize q - counts q)
    let τ₄ := τ₃.setArr "classSize" q (oldSize q - counts q)
    have hsizeAfter : (Expr.get "classSize" (.var "cl")).evalB B τ₃ =
        some (oldSize q) := by
      have hget : (τ₃.arrs "classSize")[τ₃.vars "cl"]? =
          some (oldSize q) := by
        simp [τ₃, τ₂, τ₁, hwork, List.getElem?_set,
          Ne.symm hqCurrent, hqN, hsizeEq]
      exact evalB_get (evalB_var (by simpa [τ₃, τ₂, τ₁] using hqB))
        hget (hsizeB q hqBase)
    have hcountAfter :
        (Expr.get "markedCount" (.var "cl")).evalB B τ₃ =
          some (counts q) := by
      simpa [τ₃, τ₂] using hcountEval
    have rshrink : Run B
        (.store "classSize" (.var "cl")
          (.sub (.get "classSize" (.var "cl"))
            (.get "markedCount" (.var "cl")))) τ₃ τ₄ 13 := by
      apply Run.mono (Run.store
        (evalB_var (by simpa [τ₃, τ₂, τ₁] using hqB))
        (evalB_bin hsizeAfter hcountAfter (by
          simp
          exact (Nat.sub_le _ _).trans_lt (hsizeB q hqBase))) (by
          simpa [τ₃, τ₂, τ₁, hwork, length_arrOf] using hqN))
      norm_num [Expr.size]
    let τ₅ := τ₄.setVar "classCount" (current + 1)
    have rclass : Run B (inc "classCount") τ₄ τ₅ 4 := by
      apply Run.assign
      apply evalB_bin
      · rw [evalB_var_iff]
        simp [τ₄, τ₃, τ₂, τ₁, hcurrent, hcurrentB]
      · exact evalB_lit honeB
      · simp
        exact (Nat.succ_le_of_lt (hcurrentLt.trans_le hcapacity)).trans_lt hnB
    have rbranch : Run B
        (seqs [
          .store "split" (.var "cl") (.var "classCount"),
          .store "classSize" (.var "classCount")
            (.get "markedCount" (.var "cl")),
          .store "classSize" (.var "cl")
            (.sub (.get "classSize" (.var "cl"))
              (.get "markedCount" (.var "cl"))),
          inc "classCount"])
        τ₁ τ₅ 27 := by
      simpa [seqs] using rsplit.seq (rnewSize.seq (rshrink.seq rclass))
    let τ₆ := τ₅.setVar "i" (τ.vars "i" + 1)
    have ri : Run B (inc "i") τ₅ τ₆ 4 := by
      apply Run.assign
      exact evalB_bin (evalB_var (by simpa [τ₅, τ₄, τ₃, τ₂, τ₁] using hiB))
        (evalB_lit honeB) (by
          simp
          exact ((Nat.succ_le_of_lt hilt).trans hheight).trans_lt hnB)
    refine ⟨τ₆, (rcl.seq ((Run.ite_true htest rbranch).seq ri)).mono (by
      norm_num [refineSplitBody, test, seqs, inc, Cond.size, Expr.size]), ?_,
      by simp [τ₆]⟩
    let split' := upd split q current
    have hprefix' : SplitPrefix base (current + 1)
        (processedClasses (τ.vars "i" + 1) entry) counts oldSize split' := by
      rw [processedClasses_succ]
      exact Lax235315Proofs.Construction.RefineSplitMath.SplitPrefix.insert_partial
        hprefix hqNot hpartial
    refine ⟨current + 1, split', workSize', by simp [τ₆]; omega,
      hheight, by simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hn],
      by simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, htouchedLen],
      by simp [τ₆, τ₅], by simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hentry],
      by simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hcounts], ?_, ?_, henum,
      hrange, by simpa [τ₆] using hprefix', ?_, ?_⟩
    · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hwork, workSize',
        set_arrOf_eq_upd]
    · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hsplit, split',
        set_arrOf_eq_upd]
    · rw [show processedClasses (τ₆.vars "i") entry =
          insert q processed by simp [τ₆, processedClasses_succ, q, processed]]
      exact Lax235315Proofs.Construction.RefineSplitMath.SplitSizes.insert_partial
        hprefix hsplitSizes (by
          intro r hr
          exact hrange r (by
            rcases Finset.mem_insert.mp hr with rfl | hrP
            · exact hqTouched
            · exact hprocessedSub hrP)) hqNot hpartial
    · intro r hrBase hrNot
      have hrNotInsert : r ∉ insert q processed := by
        simpa [τ₆, processedClasses_succ] using hrNot
      have hrq : r ≠ q := by
        intro heq
        subst r
        exact hrNotInsert (by simp)
      have hrProcessed : r ∉ processed := by
        intro hrP
        exact hrNotInsert (by simp [hrP])
      have hrCurrent : r ≠ current := by omega
      simp [workSize', upd, hrq, hrCurrent,
        hunprocessed r hrBase hrProcessed]
  · have hfull : oldSize q ≤ counts q := by omega
    have htest : test.evalB B τ₁ = some false := by
      have := evalB_condLt hcountEval hsizeEval
      simpa [test, hsizeEq, hpartial] using this
    let τ₂ := τ₁.setArr "split" q q
    have rsplit : Run B (.store "split" (.var "cl") (.var "cl"))
        τ₁ τ₂ 3 := by
      apply Run.store (evalB_var hqB) (evalB_var hqB)
      simpa [τ₁, hsplit, length_arrOf] using hqN
    let τ₃ := τ₂.setVar "i" (τ.vars "i" + 1)
    have ri : Run B (inc "i") τ₂ τ₃ 4 := by
      apply Run.assign
      exact evalB_bin (evalB_var (by simpa [τ₂, τ₁] using hiB))
        (evalB_lit honeB) (by
          simp
          exact ((Nat.succ_le_of_lt hilt).trans hheight).trans_lt hnB)
    refine ⟨τ₃, (rcl.seq ((Run.ite_false htest rsplit).seq ri)).mono (by
      norm_num [refineSplitBody, test, seqs, inc, Cond.size, Expr.size]), ?_,
      by simp [τ₃]⟩
    let split' := upd split q q
    have hprefix' : SplitPrefix base current
        (processedClasses (τ.vars "i" + 1) entry) counts oldSize split' := by
      rw [processedClasses_succ]
      exact Lax235315Proofs.Construction.RefineSplitMath.SplitPrefix.insert_full
        hprefix hqNot hfull
    refine ⟨current, split', workSize, by simp [τ₃]; omega, hheight,
      by simp [τ₃, τ₂, τ₁, hn], by simp [τ₃, τ₂, τ₁, htouchedLen],
      by simp [τ₃, τ₂, τ₁, hcurrent], by simp [τ₃, τ₂, τ₁, hentry],
      by simp [τ₃, τ₂, τ₁, hcounts], by simp [τ₃, τ₂, τ₁, hwork],
      ?_, henum, hrange, by simpa [τ₃] using hprefix', ?_, ?_⟩
    · simp [τ₃, τ₂, τ₁, split', hsplit, set_arrOf_eq_upd]
    · rw [show processedClasses (τ₃.vars "i") entry =
          insert q processed by simp [τ₃, processedClasses_succ, q, processed]]
      exact Lax235315Proofs.Construction.RefineSplitMath.SplitSizes.insert_full
        hsplitSizes hqNot hfull hsizeEq
    · intro r hrBase hrNot
      have hrNotInsert : r ∉ insert q processed := by
        simpa [τ₃, processedClasses_succ] using hrNot
      have hrProcessed : r ∉ processed := by
        intro hrP
        exact hrNotInsert (by simp [hrP])
      exact hunprocessed r hrBase hrProcessed

/-- The allocation loop terminates after the touched prefix and produces a
`ValidSplits` certificate for every touched class. -/
lemma refineSplitLoop_run
    {B n base height : ℕ} {entry counts oldSize : ℕ → ℕ}
    {touched : Finset ℕ} {σ : Env}
    (hI : SplitInv n base height entry touched counts oldSize σ)
    (hnB : n < B) (honeB : 1 < B)
    (hcapacity : base +
      (touched.filter fun q => counts q < oldSize q).card ≤ n)
    (hcountsB : ∀ q < n, counts q < B)
    (hsizeB : ∀ q < base, oldSize q < B) :
    ∃ σ' current split workSize,
      Run B (.while (.lt (.var "i") (.var "touchedLen"))
        refineSplitBody) σ σ' ((100 + 4) * height + 4) ∧
      SplitInv n base height entry touched counts oldSize σ' ∧
      σ'.vars "i" = height ∧ σ'.vars "classCount" = current ∧
      σ'.arrs "split" = arrOf n split ∧
      σ'.arrs "classSize" = arrOf n workSize ∧
      ValidSplits base touched counts oldSize split ∧ current ≤ n := by
  let I := SplitInv n base height entry touched counts oldSize
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < height)
      refineSplitBody
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 100 :=
    splitBody_spec hnB honeB hcapacity hcountsB hsizeB
  have hiB : ∀ τ, I τ → τ.vars "i" < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, hi, hh, -⟩
    exact (hi.trans hh).trans_lt hnB
  have hheightB : ∀ τ, I τ → τ.vars "touchedLen" < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, hh, _, htl, -⟩
    rw [htl]
    exact hh.trans_lt hnB
  have hheightEq : ∀ τ, I τ → τ.vars "touchedLen" = height := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, _, htl, -⟩
    exact htl
  have hiLe : ∀ τ, I τ → τ.vars "i" ≤ height := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, hi, -⟩
    exact hi
  obtain ⟨σ', rloop, hI', hi'⟩ :=
    (Spec.forRange "i" "touchedLen" I height 100
      ((100 + 4) * height + 4)
      hiB hheightB hheightEq hiLe hbody (fun _ h => h)
      (fun τ _ => Nat.add_le_add_right
        (Nat.mul_le_mul_left (100 + 4) (Nat.sub_le height (τ.vars "i"))) 4)).run hI
  rcases hI' with ⟨current, split, workSize, hile, hheight, hn,
    htouchedLen, hcurrent, hentry, hcounts, hwork, hsplit, henum,
    hrange, hprefix, hsplitSizes, hunprocessed⟩
  have hprocessed : processedClasses height entry = touched :=
    Lax235315Proofs.Construction.RefineSplitMath.PrefixEnumerates.processedClasses_eq henum
  have hvalid : ValidSplits base touched counts oldSize split := by
    apply Lax235315Proofs.Construction.RefineSplitMath.SplitPrefix.validSplits
    simpa [hi', hprocessed] using hprefix
  have hcurrentLe : current ≤ n := by
    apply (Lax235315Proofs.Construction.RefineSplitMath.SplitPrefix.current_le
      (by simpa [hi', hprocessed] using hprefix) (Finset.Subset.rfl)).trans
    exact hcapacity
  exact ⟨σ', current, split, workSize, rloop,
    ⟨current, split, workSize, hile, hheight, hn, htouchedLen,
      hcurrent, hentry, hcounts, hwork, hsplit, henum, hrange,
      hprefix, hsplitSizes, hunprocessed⟩,
    hi', hcurrent, hsplit, hwork, hvalid, hcurrentLe⟩

/-- The concrete loop body which copies the chosen split label to one marked
vertex. -/
def refineRelabelBody (clsName : String) : Com :=
  seqs [
    .assign "v" (.get "marked" (.var "i")),
    .assign "cl" (.get clsName (.var "v")),
    .store clsName (.var "v") (.get "split" (.var "cl")),
    inc "i"]

def RelabelInv (n height : ℕ) (entry : ℕ → ℕ) (marked : Finset ℕ)
    (clsName : String) (label split : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ height ∧ height ≤ n ∧ τ.vars "n" = n ∧
  τ.vars "markedLen" = height ∧
  τ.arrs "marked" = arrOf n entry ∧ τ.arrs "split" = arrOf n split ∧
  τ.arrs clsName = arrOf n
    (partiallyRefinedLabel (processedClasses (τ.vars "i") entry) label split) ∧
  PrefixEnumerates height entry marked

lemma relabelInv_initial
    {n height : ℕ} {entry label split : ℕ → ℕ} {marked : Finset ℕ}
    {clsName : String} {σ : Env}
    (hi : σ.vars "i" = 0) (hheight : height ≤ n) (hn : σ.vars "n" = n)
    (hmarkedLen : σ.vars "markedLen" = height)
    (hmarked : σ.arrs "marked" = arrOf n entry)
    (hsplit : σ.arrs "split" = arrOf n split)
    (hcls : σ.arrs clsName = arrOf n label)
    (henum : PrefixEnumerates height entry marked) :
    RelabelInv n height entry marked clsName label split σ := by
  refine ⟨by omega, hheight, hn, hmarkedLen, hmarked, hsplit, ?_, henum⟩
  simpa [hi, processedClasses, partiallyRefinedLabel] using hcls

private lemma relabelBody_spec
    {B n height : ℕ} {entry label split : ℕ → ℕ}
    {marked : Finset ℕ} {clsName : String}
    (hnB : n < B) (honeB : 1 < B)
    (hvertexN : ∀ v ∈ marked, v < n)
    (hlabelN : ∀ v ∈ marked, label v < n)
    (hsplitB : ∀ v ∈ marked, split (label v) < B)
    (hclsMarked : clsName ≠ "marked")
    (hclsSplit : clsName ≠ "split") :
    Spec B
      (fun τ => RelabelInv n height entry marked clsName label split τ ∧
        τ.vars "i" < height)
      (refineRelabelBody clsName)
      (fun τ τ' => RelabelInv n height entry marked clsName label split τ' ∧
        τ'.vars "i" = τ.vars "i" + 1)
      40 := by
  intro τ hτ
  rcases hτ with ⟨⟨hile, hheight, hn, hmarkedLen, hmarked, hsplit,
    hcls, henum⟩, hilt⟩
  let processed := processedClasses (τ.vars "i") entry
  let v := entry (τ.vars "i")
  have hnext :=
    Lax235315Proofs.Construction.RefineSplitMath.PrefixEnumerates.next_mem_not_processed
      henum hilt
  have hvMarked : v ∈ marked := hnext.1
  have hvNot : v ∉ processed := hnext.2
  have hvN : v < n := hvertexN v hvMarked
  have hvB : v < B := hvN.trans hnB
  have hiB : τ.vars "i" < B := (hilt.trans_le hheight).trans hnB
  have hentryGet : (τ.arrs "marked")[τ.vars "i"]? = some v := by
    rw [hmarked, getElem?_arrOf entry (hilt.trans_le hheight)]
  have hentryEval : (Expr.get "marked" (.var "i")).evalB B τ = some v :=
    evalB_get (evalB_var hiB) hentryGet hvB
  let τ₁ := τ.setVar "v" v
  have rv : Run B (.assign "v" (.get "marked" (.var "i"))) τ τ₁ 6 :=
    (Run.assign hentryEval).mono (by norm_num [Expr.size])
  have hlabelValue : partiallyRefinedLabel processed label split v = label v := by
    simp [partiallyRefinedLabel, hvNot]
  have hlabelN' : label v < n := hlabelN v hvMarked
  have hlabelB : label v < B := hlabelN'.trans hnB
  have hclsGet : (τ₁.arrs clsName)[τ₁.vars "v"]? = some (label v) := by
    simp [τ₁, hcls, getElem?_arrOf _ hvN, partiallyRefinedLabel,
      processed, hvNot]
  have hclsEval : (Expr.get clsName (.var "v")).evalB B τ₁ = some (label v) :=
    evalB_get (evalB_var hvB) hclsGet hlabelB
  let τ₂ := τ₁.setVar "cl" (label v)
  have rcl : Run B (.assign "cl" (.get clsName (.var "v"))) τ₁ τ₂ 6 :=
    (Run.assign hclsEval).mono (by norm_num [Expr.size])
  have hsplitGet : (τ₂.arrs "split")[τ₂.vars "cl"]? =
      some (split (label v)) := by
    simp [τ₂, τ₁, hsplit, getElem?_arrOf split hlabelN']
  have hsplitEval : (Expr.get "split" (.var "cl")).evalB B τ₂ =
      some (split (label v)) :=
    evalB_get (evalB_var hlabelB) hsplitGet (hsplitB v hvMarked)
  let τ₃ := τ₂.setArr clsName v (split (label v))
  have rstore : Run B
      (.store clsName (.var "v") (.get "split" (.var "cl"))) τ₂ τ₃ 7 := by
    have hvEval : (Expr.var "v").evalB B τ₂ = some v := by
      rw [evalB_var_iff]
      simp [τ₂, τ₁, hvB]
    have hlen : v < (τ₂.arrs clsName).length := by
      simpa [τ₂, τ₁, hcls, length_arrOf] using hvN
    exact (Run.store hvEval hsplitEval hlen).mono (by norm_num [Expr.size])
  let τ₄ := τ₃.setVar "i" (τ.vars "i" + 1)
  have ri : Run B (inc "i") τ₃ τ₄ 4 := by
    apply Run.assign
    exact evalB_bin (evalB_var (by simpa [τ₃, τ₂, τ₁] using hiB))
      (evalB_lit honeB) (by
        simp
        exact ((Nat.succ_le_of_lt hilt).trans hheight).trans_lt hnB)
  refine ⟨τ₄, (rv.seq (rcl.seq (rstore.seq ri))).mono (by
    norm_num [refineRelabelBody, seqs, inc, Expr.size]), ?_, by simp [τ₄]⟩
  have hupdate : upd (partiallyRefinedLabel processed label split) v
      (split (label v)) =
      partiallyRefinedLabel (insert v processed) label split :=
    update_partiallyRefinedLabel hvNot
  refine ⟨by simp [τ₄]; omega, hheight, by simp [τ₄, τ₃, τ₂, τ₁, hn],
    by simp [τ₄, τ₃, τ₂, τ₁, hmarkedLen],
    by simp [τ₄, τ₃, τ₂, τ₁, hmarked, Ne.symm hclsMarked],
    by simp [τ₄, τ₃, τ₂, τ₁, hsplit, Ne.symm hclsSplit], ?_, henum⟩
  simp only [τ₄, τ₃, τ₂, τ₁, arrs_setVar, vars_setVar, arrs_setArr,
    if_pos]
  rw [hcls, set_arrOf_eq_upd, processedClasses_succ]
  exact congrArg (arrOf n) hupdate

/-- Replaying the whole marked stack updates exactly the vertices in the
marked set. -/
lemma refineRelabelLoop_run
    {B n height : ℕ} {entry label split : ℕ → ℕ}
    {marked : Finset ℕ} {clsName : String} {σ : Env}
    (hI : RelabelInv n height entry marked clsName label split σ)
    (hnB : n < B) (honeB : 1 < B)
    (hvertexN : ∀ v ∈ marked, v < n)
    (hlabelN : ∀ v ∈ marked, label v < n)
    (hsplitB : ∀ v ∈ marked, split (label v) < B)
    (hclsMarked : clsName ≠ "marked")
    (hclsSplit : clsName ≠ "split") :
    ∃ σ', Run B
        (.while (.lt (.var "i") (.var "markedLen"))
          (refineRelabelBody clsName))
        σ σ' ((40 + 4) * height + 4) ∧
      RelabelInv n height entry marked clsName label split σ' ∧
      σ'.vars "i" = height ∧
      σ'.arrs clsName = arrOf n (refinedLabel marked label split) := by
  let I := RelabelInv n height entry marked clsName label split
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < height)
      (refineRelabelBody clsName)
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 40 :=
    relabelBody_spec hnB honeB hvertexN hlabelN hsplitB hclsMarked hclsSplit
  have hiB : ∀ τ, I τ → τ.vars "i" < B := by
    intro τ hτ
    exact lt_of_le_of_lt ((hτ.1.trans hτ.2.1)) hnB
  have hheightB : ∀ τ, I τ → τ.vars "markedLen" < B := by
    intro τ hτ
    rw [hτ.2.2.2.1]
    exact lt_of_le_of_lt hτ.2.1 hnB
  have hheightEq : ∀ τ, I τ → τ.vars "markedLen" = height :=
    fun _ h => h.2.2.2.1
  have hiLe : ∀ τ, I τ → τ.vars "i" ≤ height := fun _ h => h.1
  obtain ⟨σ', rloop, hI', hi'⟩ :=
    (Spec.forRange "i" "markedLen" I height 40
      ((40 + 4) * height + 4)
      hiB hheightB hheightEq hiLe hbody (fun _ h => h)
      (fun τ _ => Nat.add_le_add_right
        (Nat.mul_le_mul_left (40 + 4) (Nat.sub_le height (τ.vars "i"))) 4)).run hI
  have hprocessed : processedClasses height entry = marked :=
    Lax235315Proofs.Construction.RefineSplitMath.PrefixEnumerates.processedClasses_eq hI'.2.2.2.2.2.2.2
  refine ⟨σ', rloop, hI', hi', ?_⟩
  simpa [hi', hprocessed, partiallyRefinedLabel_eq_refinedLabel] using
    hI'.2.2.2.2.2.2.1

/-- The final loop body of `refineOne`, resetting one touched class counter. -/
def refineResetBody : Com :=
  seqs [
    .assign "cl" (.get "touched" (.var "i")),
    .store "markedCount" (.var "cl") (.lit 0),
    inc "i"]

def ResetInv (n height : ℕ) (entry : ℕ → ℕ) (touched : Finset ℕ)
    (counts : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ height ∧ height ≤ n ∧ τ.vars "n" = n ∧
  τ.vars "touchedLen" = height ∧
  τ.arrs "touched" = arrOf n entry ∧
  τ.arrs "markedCount" = arrOf n
    (partiallyCleared (processedClasses (τ.vars "i") entry) counts) ∧
  PrefixEnumerates height entry touched

lemma resetInv_initial
    {n height : ℕ} {entry counts : ℕ → ℕ} {touched : Finset ℕ}
    {σ : Env}
    (hi : σ.vars "i" = 0) (hheight : height ≤ n) (hn : σ.vars "n" = n)
    (htouchedLen : σ.vars "touchedLen" = height)
    (htouched : σ.arrs "touched" = arrOf n entry)
    (hcounts : σ.arrs "markedCount" = arrOf n counts)
    (henum : PrefixEnumerates height entry touched) :
    ResetInv n height entry touched counts σ := by
  refine ⟨by omega, hheight, hn, htouchedLen, htouched, ?_, henum⟩
  simpa [hi, processedClasses, partiallyCleared] using hcounts

private lemma resetBody_spec
    {B n height : ℕ} {entry counts : ℕ → ℕ} {touched : Finset ℕ}
    (hnB : n < B) (hclassN : ∀ q ∈ touched, q < n) :
    Spec B
      (fun τ => ResetInv n height entry touched counts τ ∧
        τ.vars "i" < height)
      refineResetBody
      (fun τ τ' => ResetInv n height entry touched counts τ' ∧
        τ'.vars "i" = τ.vars "i" + 1)
      20 := by
  intro τ hτ
  rcases hτ with ⟨⟨hile, hheight, hn, htouchedLen, htouched, hcounts,
    henum⟩, hilt⟩
  let processed := processedClasses (τ.vars "i") entry
  let q := entry (τ.vars "i")
  have hnext :=
    Lax235315Proofs.Construction.RefineSplitMath.PrefixEnumerates.next_mem_not_processed
      henum hilt
  have hqTouched : q ∈ touched := hnext.1
  have hqNot : q ∉ processed := hnext.2
  have hqN : q < n := hclassN q hqTouched
  have hqB : q < B := hqN.trans hnB
  have hiB : τ.vars "i" < B := (hilt.trans_le hheight).trans hnB
  have hget : (τ.arrs "touched")[τ.vars "i"]? = some q := by
    rw [htouched, getElem?_arrOf entry (hilt.trans_le hheight)]
  have heval : (Expr.get "touched" (.var "i")).evalB B τ = some q :=
    evalB_get (evalB_var hiB) hget hqB
  let τ₁ := τ.setVar "cl" q
  have rcl : Run B (.assign "cl" (.get "touched" (.var "i"))) τ τ₁ 6 :=
    (Run.assign heval).mono (by norm_num [Expr.size])
  let τ₂ := τ₁.setArr "markedCount" q 0
  have rstore : Run B (.store "markedCount" (.var "cl") (.lit 0))
      τ₁ τ₂ 3 := by
    apply Run.store (evalB_var hqB) (evalB_lit (by omega))
    simpa [τ₁, hcounts, length_arrOf] using hqN
  let τ₃ := τ₂.setVar "i" (τ.vars "i" + 1)
  have ri : Run B (inc "i") τ₂ τ₃ 4 := by
    apply Run.assign
    exact evalB_bin (evalB_var (by simpa [τ₂, τ₁] using hiB))
      (evalB_lit (by omega)) (by
        simp
        exact ((Nat.succ_le_of_lt hilt).trans hheight).trans_lt hnB)
  refine ⟨τ₃, (rcl.seq (rstore.seq ri)).mono (by
    norm_num [refineResetBody, seqs, inc, Expr.size]), ?_, by simp [τ₃]⟩
  have hupdate : upd (partiallyCleared processed counts) q 0 =
      partiallyCleared (insert q processed) counts :=
    update_partiallyCleared hqNot
  refine ⟨by simp [τ₃]; omega, hheight, by simp [τ₃, τ₂, τ₁, hn],
    by simp [τ₃, τ₂, τ₁, htouchedLen],
    by simp [τ₃, τ₂, τ₁, htouched], ?_, henum⟩
  simp only [τ₃, τ₂, τ₁, arrs_setVar, vars_setVar, arrs_setArr, if_pos]
  rw [hcounts, set_arrOf_eq_upd, processedClasses_succ]
  exact congrArg (arrOf n) hupdate

lemma refineResetLoop_run
    {B n height : ℕ} {entry counts : ℕ → ℕ} {touched : Finset ℕ}
    {σ : Env}
    (hI : ResetInv n height entry touched counts σ)
    (hnB : n < B) (hclassN : ∀ q ∈ touched, q < n) :
    ∃ σ', Run B
        (.while (.lt (.var "i") (.var "touchedLen")) refineResetBody)
        σ σ' ((20 + 4) * height + 4) ∧
      ResetInv n height entry touched counts σ' ∧
      σ'.vars "i" = height ∧
      σ'.arrs "markedCount" = arrOf n (partiallyCleared touched counts) := by
  let I := ResetInv n height entry touched counts
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < height)
      refineResetBody
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 20 :=
    resetBody_spec hnB hclassN
  have hiB : ∀ τ, I τ → τ.vars "i" < B := fun τ h =>
    lt_of_le_of_lt (h.1.trans h.2.1) hnB
  have hheightB : ∀ τ, I τ → τ.vars "touchedLen" < B := by
    intro τ h
    rw [h.2.2.2.1]
    exact lt_of_le_of_lt h.2.1 hnB
  have hheightEq : ∀ τ, I τ → τ.vars "touchedLen" = height :=
    fun _ h => h.2.2.2.1
  have hiLe : ∀ τ, I τ → τ.vars "i" ≤ height := fun _ h => h.1
  obtain ⟨σ', rloop, hI', hi'⟩ :=
    (Spec.forRange "i" "touchedLen" I height 20
      ((20 + 4) * height + 4)
      hiB hheightB hheightEq hiLe hbody (fun _ h => h)
      (fun τ _ => Nat.add_le_add_right
        (Nat.mul_le_mul_left (20 + 4) (Nat.sub_le height (τ.vars "i"))) 4)).run hI
  have hprocessed : processedClasses height entry = touched :=
    Lax235315Proofs.Construction.RefineSplitMath.PrefixEnumerates.processedClasses_eq hI'.2.2.2.2.2.2
  refine ⟨σ', rloop, hI', hi', ?_⟩
  simpa [hi', hprocessed] using hI'.2.2.2.2.2.1

end Lax235315Proofs.Construction.RefineSplitSource
