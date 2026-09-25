import Lax235315Proofs.Construction.RefineOneSource
import Mathlib.Tactic

/-! Source-level verification of the repeated test-vertex refinement loop. -/

namespace Lax235315Proofs.Construction.PartitionLoopSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax11Proofs.CC
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NeighborScan
open Lax235315Proofs.Construction.PartitionRefinement
open Lax235315Proofs.Construction.RadixEight
open Lax235315Proofs.Construction.RefineOneSource
open Lax235315Proofs.Construction.RefineSplitMath
open Lax235315Proofs.Construction.RefineSplitSource
open Lax235315Proofs.Construction.WelzlProgram

noncomputable section

/-- The set represented by the first `i` entries of a numeric test array. -/
def testPrefix {n : ℕ} (tests : ℕ → ℕ) (i : ℕ) : Set (Fin n) :=
  {v | ∃ j < i, tests j = v.val}

@[simp] theorem testPrefix_zero {n : ℕ} (tests : ℕ → ℕ) :
    testPrefix (n := n) tests 0 = ∅ := by
  ext v
  simp [testPrefix]

theorem testPrefix_succ {n i : ℕ} {tests : ℕ → ℕ}
    (hi : tests i < n) :
    testPrefix (n := n) tests (i + 1) =
      insert (⟨tests i, hi⟩ : Fin n) (testPrefix tests i) := by
  ext v
  constructor
  · rintro ⟨j, hj, heq⟩
    by_cases hji : j = i
    · left
      subst j
      exact Fin.ext heq.symm
    · right
      exact ⟨j, by omega, heq⟩
  · intro hv
    rcases hv with hv | hv
    · subst v
      exact ⟨i, by omega, rfl⟩
    · obtain ⟨j, hj, heq⟩ := hv
      exact ⟨j, by omega, heq⟩

/-- The exact source command used by `partition` for one test vertex. -/
def partitionRefineBody (activeName testsName clsName : String) : Com :=
  seqs [
    .assign "token" (.add (.var "ti") (.lit 1)),
    .assign "t" (.get testsName (.var "ti")),
    refineOne activeName clsName,
    inc "ti"]

/-- The concrete numeric partition after `i` passes classifies precisely the
neighborhood traces on the first `i` test vertices. -/
def RefineTestsInv {n : ℕ} (G : SimpleGraph (Fin n))
    (x : List ℕ) (targetCap testCount : ℕ)
    (activeName testsName testCountName clsName : String)
    (active tests : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ (current : ℕ) (label size stamp counts marked touched split : ℕ → ℕ),
    τ.vars "ti" ≤ testCount ∧ testCount ≤ n ∧
    τ.vars testCountName = testCount ∧ τ.vars "n" = n ∧
    τ.vars "classCount" = current ∧ current ≤ n ∧
    τ.arrs "off" = arrOf (n + 1) (offset x) ∧
    τ.arrs "tgt" = arrOf targetCap (target x) ∧
    τ.arrs activeName = arrOf n active ∧
    τ.arrs testsName = arrOf n tests ∧
    τ.arrs clsName = arrOf n label ∧
    τ.arrs "classSize" = arrOf n size ∧
    τ.arrs "stamp" = arrOf n stamp ∧
    τ.arrs "markedCount" = arrOf n counts ∧
    τ.arrs "marked" = arrOf n marked ∧
    τ.arrs "touched" = arrOf n touched ∧
    τ.arrs "split" = arrOf n split ∧
    (∀ v < n, stamp v ≤ τ.vars "ti") ∧
    (∀ q < n, counts q = 0) ∧
    ClassSizes n current active label size ∧
    LabelsOccupyPrefix current label (activeVertices n active) ∧
    Classifies G {v : Fin n | active v.val = 1}
      (testPrefix tests (τ.vars "ti")) (fun v => label v.val)

private theorem partitionRefineBody_run
    {B n targetCap testCount : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {active tests : ℕ → ℕ}
    {activeName testsName testCountName clsName : String}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (htestsRange : ∀ i < testCount, tests i < n)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hactiveCls : activeName ≠ clsName)
    (haStamp : activeName ≠ "stamp") (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (haSplit : activeName ≠ "split")
    (haSize : activeName ≠ "classSize")
    (hcStamp : clsName ≠ "stamp") (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount")
    (hcSplit : clsName ≠ "split")
    (hcSize : clsName ≠ "classSize")
    (hcOff : clsName ≠ "off") (hcTgt : clsName ≠ "tgt")
    (htestsFrame : testsName ∉
      (partitionRefineBody activeName testsName clsName).warrs)
    (hcountFrame : testCountName ∉
      (partitionRefineBody activeName testsName clsName).wvars)
    {τ : Env}
    (hI : RefineTestsInv G x targetCap testCount activeName testsName
      testCountName clsName active tests τ)
    (htiLt : τ.vars "ti" < testCount) :
    ∃ τ',
      Run B (partitionRefineBody activeName testsName clsName) τ τ'
        (320 * (offset x (tests (τ.vars "ti") + 1) -
          offset x (tests (τ.vars "ti")) + 1)) ∧
        RefineTestsInv G x targetCap testCount activeName testsName
          testCountName clsName active tests τ' ∧
        τ'.vars "ti" = τ.vars "ti" + 1 := by
  rcases hI with ⟨current, label, size, stamp, counts, marked, touched, split,
    htiLe, htestCountN, htestCount, hn, hcurrent, hcurrentN,
    hoff, htarget, hactive, htests, hlabel, hsize, hstamp, hcounts,
    hmarked, htouched, hsplit, hstampLe, hcountsZero, hsizes,
    hoccupied, hclassifies⟩
  let token := τ.vars "ti" + 1
  have htiB : τ.vars "ti" < B := by omega
  have htokenB : token < B := by
    dsimp [token]
    omega
  let τ₁ := τ.setVar "token" token
  have rtoken : Run B
      (.assign "token" (.add (.var "ti") (.lit 1))) τ τ₁ 4 := by
    apply Run.assign
    exact evalB_bin (evalB_var htiB) (evalB_lit honeB) htokenB
  let test := tests (τ.vars "ti")
  have htestN : test < n := htestsRange _ htiLt
  have htestB : test < B := htestN.trans hnB
  have htestGet : (τ₁.arrs testsName)[τ₁.vars "ti"]? = some test := by
    simp [τ₁, htests, test, getElem?_arrOf tests (htiLt.trans_le htestCountN)]
  have htestEval : (Expr.get testsName (.var "ti")).evalB B τ₁ = some test :=
    evalB_get (by simpa [τ₁] using evalB_var htiB) htestGet htestB
  let τ₂ := τ₁.setVar "t" test
  have rtest : Run B (.assign "t" (.get testsName (.var "ti"))) τ₁ τ₂ 6 :=
    (Run.assign htestEval).mono (by norm_num [Expr.size])
  have hsizeBound : ∀ q < current, size q < B := by
    intro q hq
    rw [hsizes.2 q hq]
    calc
      classMultiplicity label (activeVertices n active) q ≤
          (activeVertices n active).card := classMultiplicity_le_card _ _ _
      _ ≤ n := activeVertices_card_le n active
      _ < B := hnB
  have hstampNe : ∀ v < n, stamp v ≠ token := by
    intro v hv heq
    have := hstampLe v hv
    dsimp [token] at heq
    omega
  have hstampTokenLe : ∀ v < n, stamp v ≤ token := by
    intro v hv
    exact (hstampLe v hv).trans (by simp [token])
  have hstampBound : ∀ v < n, stamp v < B := by
    intro v hv
    exact lt_of_le_of_lt (hstampLe v hv) htiB
  obtain ⟨τ₃, current', split', size', counts', stamp', rrefine,
      hcurrent', hcurrentN', hactive', hlabel', hsize', hcounts', hstamp',
      hstampLe', hcountsZero', hsizes', hoccupied', hrefines'⟩ :=
    refineOne_run
      (B := B) (n := n) (targetCap := targetCap) (base := current)
      (token := token) (t := test) (activeName := activeName)
      (clsName := clsName) (active := active) (label := label) (size := size)
      (offset := offset x) (target := target x) (stamp := stamp)
      (counts := counts) (marked := marked) (touched := touched) (split₀ := split)
      (σ := τ₂)
      (by simp [τ₂, τ₁, hn]) (by simp [τ₂, τ₁, hcurrent])
      (by simp [τ₂, τ₁, token]) (by simp [τ₂, test])
      (by simp [τ₂, τ₁, hoff]) (by simp [τ₂, τ₁, htarget])
      (by simp [τ₂, τ₁, hactive]) (by simp [τ₂, τ₁, hlabel])
      (by simp [τ₂, τ₁, hsize]) (by simp [τ₂, τ₁, hstamp])
      (by simp [τ₂, τ₁, hcounts]) (by simp [τ₂, τ₁, hmarked])
      (by simp [τ₂, τ₁, htouched]) (by simp [τ₂, τ₁, hsplit])
      htestN hcurrentN (hx.offset_mono test htestN)
      (fun i hi => by
        rw [htargetCap]
        exact offset_le hx (by omega))
      (fun j hlo hhi => by
        exact target_lt' hx htestN hhi)
      hnB htargetCapB htokenB honeB hactiveB hsizeBound hstampNe
      hstampTokenLe hstampBound hcountsZero hsizes hoccupied hactiveCls
      haStamp haMarked haTouched haCount haSplit haSize
      hcStamp hcMarked hcTouched hcCount hcSplit hcSize
  have hmarkedLen : (τ₃.arrs "marked").length = n := by
    rw [run_array_length_eq rrefine "marked"]
    simp [τ₂, τ₁, hmarked, length_arrOf]
  obtain ⟨marked', hmarked'⟩ := exists_arrOf_of_length hmarkedLen
  have htouchedLen : (τ₃.arrs "touched").length = n := by
    rw [run_array_length_eq rrefine "touched"]
    simp [τ₂, τ₁, htouched, length_arrOf]
  obtain ⟨touched', htouched'⟩ := exists_arrOf_of_length htouchedLen
  have hsplitLen : (τ₃.arrs "split").length = n := by
    rw [run_array_length_eq rrefine "split"]
    simp [τ₂, τ₁, hsplit, length_arrOf]
  obtain ⟨splitNext, hsplitNext⟩ := exists_arrOf_of_length hsplitLen
  let τ₄ := τ₃.setVar "ti" (τ.vars "ti" + 1)
  have htiNextB : τ.vars "ti" + 1 < B := by
    simpa [token] using htokenB
  have rinc : Run B (inc "ti") τ₃ τ₄ 4 := by
    apply Run.assign
    have htiFrame : τ₃.vars "ti" = τ.vars "ti" := by
      rw [rrefine.frame_var "ti" (by
        simp [refineOne, finishRefinement, refineSplitBody,
          refineRelabelBody, refineResetBody, refineMarkBody, seqs, inc,
          Com.wvars])] <;>
        simp [τ₂, τ₁]
    exact evalB_bin (by rw [evalB_var_iff, htiFrame]; exact ⟨rfl, htiB⟩)
      (evalB_lit honeB) htiNextB
  have rbody : Run B (partitionRefineBody activeName testsName clsName)
      τ τ₄ (320 * (offset x (test + 1) - offset x test + 1)) := by
    have rr := rtoken.seq (rtest.seq (rrefine.seq rinc))
    simpa [partitionRefineBody, seqs] using rr.mono (by omega)
  have hclassifies' : Classifies G {v : Fin n | active v.val = 1}
      (testPrefix tests (τ.vars "ti" + 1))
      (fun v =>
        refinedLabel
          (activeTargets (target x) active (offset x test) (offset x (test + 1)))
          label split' v.val) := by
    rw [testPrefix_succ htestN]
    apply Classifies.of_refinesBy G hclassifies
    exact refinesBy_of_numeric_block hx ⟨test, htestN⟩ hrefines'
  refine ⟨τ₄, ?_, ?_, by simp [τ₄]⟩
  · simpa [test] using rbody
  refine ⟨current',
    refinedLabel
      (activeTargets (target x) active (offset x test) (offset x (test + 1)))
      label split', size', stamp', counts', marked', touched', splitNext,
    by simp [τ₄]; omega, htestCountN, ?_, ?_, ?_, hcurrentN', ?_, ?_,
    ?_, ?_, ?_, hsize', hstamp', hcounts', ?_, ?_, ?_, ?_,
    hcountsZero', hsizes', hoccupied', ?_⟩
  · rw [rbody.frame_var testCountName hcountFrame]
    exact htestCount
  · rw [rbody.frame_var "n" (by
      simp [partitionRefineBody, refineOne, finishRefinement, refineSplitBody,
        refineRelabelBody, refineResetBody, refineMarkBody, seqs, inc,
        Com.wvars])]
    exact hn
  · simpa [τ₄] using hcurrent'
  · rw [rbody.frame_arr "off" (by
      simp [partitionRefineBody, refineOne, finishRefinement, refineSplitBody,
        refineRelabelBody, refineResetBody, refineMarkBody, seqs, inc,
        Com.warrs, hcSplit, hcSize, Ne.symm hcOff])]
    exact hoff
  · rw [rbody.frame_arr "tgt" (by
      simp [partitionRefineBody, refineOne, finishRefinement, refineSplitBody,
        refineRelabelBody, refineResetBody, refineMarkBody, seqs, inc,
        Com.warrs, hcSplit, hcSize, Ne.symm hcTgt])]
    exact htarget
  · simpa [τ₄] using hactive'
  · rw [rbody.frame_arr testsName htestsFrame]
    exact htests
  · simpa [τ₄] using hlabel'
  · simpa [τ₄] using hmarked'
  · simpa [τ₄] using htouched'
  · simpa [τ₄] using hsplitNext
  · intro v hv
    simpa [τ₄] using hstampLe' v hv
  · simpa [τ₄] using hclassifies'

/-- Remaining CSR work of a consecutive prefix of the numeric test array.
Each entry contributes its adjacency-block length and one unit of per-test
overhead. -/
def refinementWork (x : List ℕ) (tests : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, k + 1 =>
      (offset x (tests i + 1) - offset x (tests i) + 1) +
        refinementWork x tests (i + 1) k

theorem refinementWork_eq_sum_range (x : List ℕ) (tests : ℕ → ℕ)
    (i k : ℕ) :
    refinementWork x tests i k =
      ∑ j ∈ Finset.range k,
        (deg x (tests (i + j)) + 1) := by
  induction k generalizing i with
  | zero => simp [refinementWork]
  | succ k ih =>
      rw [refinementWork, Finset.sum_range_succ']
      rw [ih (i + 1)]
      simp [deg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem refinementWork_le_edgeCount_add
    {n k : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ} {tests : ℕ → ℕ}
    (hx : EncodesGraph x n G)
    (hrange : ∀ i < k, tests i < n)
    (hinj : ∀ i < k, ∀ j < k, tests i = tests j → i = j) :
    refinementWork x tests 0 k ≤ 2 * edgeCount x + k := by
  rw [refinementWork_eq_sum_range]
  simp only [Nat.zero_add, Finset.sum_add_distrib]
  have hdeg := sum_deg_queue hx hrange hinj
  have hone : ∑ _ ∈ Finset.range k, 1 = k := by simp
  rw [hone]
  exact Nat.add_le_add_right hdeg k

/-- All refinement passes terminate with the exact graph-trace equivalence
relation induced by the supplied test prefix. -/
theorem partitionRefineLoop_run
    {B n targetCap testCount : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {active tests : ℕ → ℕ}
    {activeName testsName testCountName clsName : String} {σ : Env}
    (hI : RefineTestsInv G x targetCap testCount activeName testsName
      testCountName clsName active tests σ)
    (hti : σ.vars "ti" = 0)
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (htestsRange : ∀ i < testCount, tests i < n)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hactiveCls : activeName ≠ clsName)
    (haStamp : activeName ≠ "stamp") (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (haSplit : activeName ≠ "split")
    (haSize : activeName ≠ "classSize")
    (hcStamp : clsName ≠ "stamp") (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount")
    (hcSplit : clsName ≠ "split")
    (hcSize : clsName ≠ "classSize")
    (hcOff : clsName ≠ "off") (hcTgt : clsName ≠ "tgt")
    (htestsFrame : testsName ∉
      (partitionRefineBody activeName testsName clsName).warrs)
    (hcountFrame : testCountName ∉
      (partitionRefineBody activeName testsName clsName).wvars) :
    ∃ σ', Run B
        (.while (.lt (.var "ti") (.var testCountName))
          (partitionRefineBody activeName testsName clsName))
        σ σ' (324 * refinementWork x tests 0 testCount + 4) ∧
      RefineTestsInv G x targetCap testCount activeName testsName
        testCountName clsName active tests σ' ∧
      σ'.vars "ti" = testCount := by
  let I := RefineTestsInv G x targetCap testCount activeName testsName
    testCountName clsName active tests
  let Φ : Env → ℕ := fun τ =>
    324 * refinementWork x tests (τ.vars "ti")
      (testCount - τ.vars "ti")
  have htiB : ∀ τ, I τ → τ.vars "ti" < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, _, _, _, hle, hcountN, -⟩
    exact (hle.trans hcountN).trans_lt hnB
  have hcountB : ∀ τ, I τ → τ.vars testCountName < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, _, _, _, _, hcountN, hcount, -⟩
    rw [hcount]
    exact hcountN.trans_lt hnB
  have hcountEq : ∀ τ, I τ → τ.vars testCountName = testCount := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, _, _, _, _, _, hcount, -⟩
    exact hcount
  have htiLe : ∀ τ, I τ → τ.vars "ti" ≤ testCount := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, _, _, _, hle, -⟩
    exact hle
  have hdef : ∀ τ, I τ → ∃ v,
      (Cond.lt (.var "ti") (.var testCountName)).evalB B τ = some v := by
    intro τ hτ
    exact evalB_condLt_vars (htiB τ hτ) (hcountB τ hτ)
  have hstep : ∀ τ, I τ →
      (Cond.lt (.var "ti") (.var testCountName)).evalB B τ = some true →
      ∃ τ' K, Run B (partitionRefineBody activeName testsName clsName)
          τ τ' K ∧ I τ' ∧
        1 + (Cond.lt (.var "ti") (.var testCountName)).size + K + Φ τ' ≤
          Φ τ := by
    intro τ hτ hcond
    have hltVar := lt_of_condLt_true hcond
    have hlt : τ.vars "ti" < testCount := by
      rw [← hcountEq τ hτ]
      exact hltVar
    obtain ⟨τ', rbody, hτ', hti'⟩ :=
      partitionRefineBody_run hx htargetCap htestsRange hnB htargetCapB
        honeB hactiveB hactiveCls haStamp haMarked haTouched haCount haSplit
        haSize hcStamp hcMarked hcTouched hcCount hcSplit hcSize hcOff hcTgt
        htestsFrame hcountFrame hτ hlt
    let d := offset x (tests (τ.vars "ti") + 1) -
      offset x (tests (τ.vars "ti")) + 1
    have hsub : testCount - τ.vars "ti" =
        (testCount - (τ.vars "ti" + 1)) + 1 := by omega
    refine ⟨τ', 320 * d, ?_, hτ', ?_⟩
    · simpa [d] using rbody
    · dsimp [Φ]
      rw [hti', hsub]
      simp only [refinementWork, Cond.size, Expr.size]
      dsimp [d]
      omega
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ :=
    Run.while_potential I Φ hdef hstep hI
  have htiFinal : σ'.vars "ti" = testCount := by
    have hle := htiLe σ' hI'
    have hge := le_of_condLt_false hfalse
    have hcount := hcountEq σ' hI'
    omega
  have hPhiStart : Φ σ = 324 * refinementWork x tests 0 testCount := by
    simp [Φ, hti]
  have hPhiFinal : Φ σ' = 0 := by
    simp [Φ, htiFinal, refinementWork]
  refine ⟨σ', hrun.mono ?_, hI', htiFinal⟩
  rw [hPhiFinal, hPhiStart] at hpay
  norm_num [Cond.size, Expr.size] at hpay
  omega

end

end Lax235315Proofs.Construction.PartitionLoopSource
