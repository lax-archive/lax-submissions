import Lax235315Proofs.Construction.MarkingMath
import Lax235315Proofs.Construction.PartitionSource
import Lax808846Proofs.Lib.Stack
import Mathlib.Tactic

/-! Source-level verification of the duplicate-tolerant marking phase in
`refineOne`. -/

namespace Lax235315Proofs.Construction.MarkingSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NeighborScan
open Lax235315Proofs.Construction.WelzlProgram

/-- Invariant of the first loop in `refineOne`.  The two scratch stacks
enumerate the distinct active vertices and classes seen in the CSR prefix;
the stamp array recognizes those vertices, and `markedCount` stores exact
class multiplicities. -/
def MarkInv (B n targetCap lo hi classCount token : ℕ)
    (activeName clsName : String)
    (active label size target : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ stamp marked touched counts : ℕ → ℕ,
    lo ≤ τ.vars "j" ∧ τ.vars "j" ≤ hi ∧ τ.vars "jend" = hi ∧
    τ.vars "classCount" = classCount ∧ τ.vars "token" = token ∧
    τ.vars "n" = n ∧ classCount ≤ n ∧ hi ≤ targetCap ∧
    τ.arrs activeName = arrOf n active ∧
    τ.arrs clsName = arrOf n label ∧
    τ.arrs "classSize" = arrOf n size ∧
    τ.arrs "tgt" = arrOf targetCap target ∧
    τ.arrs "stamp" = arrOf n stamp ∧
    τ.arrs "markedCount" = arrOf n counts ∧
    Stack "marked" "markedLen" n n
      (activeTargets target active lo (τ.vars "j")).card marked τ ∧
    Stack "touched" "touchedLen" n n
      (touchedClasses label
        (activeTargets target active lo (τ.vars "j"))).card touched τ ∧
    PrefixEnumerates
      (activeTargets target active lo (τ.vars "j")).card marked
      (activeTargets target active lo (τ.vars "j")) ∧
    PrefixEnumerates
      (touchedClasses label
        (activeTargets target active lo (τ.vars "j"))).card touched
      (touchedClasses label
        (activeTargets target active lo (τ.vars "j")) ) ∧
    (∀ v < n, stamp v = token ↔
      v ∈ activeTargets target active lo (τ.vars "j")) ∧
    (∀ v < n, stamp v ≤ token) ∧
    (∀ v < n, stamp v < B) ∧
    (∀ q < n, counts q = classMultiplicity label
      (activeTargets target active lo (τ.vars "j")) q) ∧
    ClassSizes n classCount active label size

/-- Zero scratch heights and a stamp unequal to the current token establish
the scan invariant at the left endpoint of a block. -/
lemma markInv_initial {B n targetCap lo hi classCount token : ℕ}
    {activeName clsName : String} {active label size target : ℕ → ℕ}
    {σ : Env} {stamp marked touched counts : ℕ → ℕ}
    (hj : σ.vars "j" = lo) (hjend : σ.vars "jend" = hi)
    (hlohi : lo ≤ hi)
    (hclassCount : σ.vars "classCount" = classCount)
    (htoken : σ.vars "token" = token) (hn : σ.vars "n" = n)
    (hccn : classCount ≤ n) (hhi : hi ≤ targetCap)
    (hactive : σ.arrs activeName = arrOf n active)
    (hlabel : σ.arrs clsName = arrOf n label)
    (hsize : σ.arrs "classSize" = arrOf n size)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hcounts : σ.arrs "markedCount" = arrOf n counts)
    (hmarked : σ.arrs "marked" = arrOf n marked)
    (htouched : σ.arrs "touched" = arrOf n touched)
    (hmarkedLen : σ.vars "markedLen" = 0)
    (htouchedLen : σ.vars "touchedLen" = 0)
    (hstampNe : ∀ v < n, stamp v ≠ token)
    (hstampLe : ∀ v < n, stamp v ≤ token)
    (hstampB : ∀ v < n, stamp v < B)
    (hcounts0 : ∀ q < n, counts q = 0)
    (hsizes : ClassSizes n classCount active label size) :
    MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ := by
  refine ⟨stamp, marked, touched, counts, by omega, by omega, hjend,
    hclassCount, htoken, hn, hccn, hhi, hactive, hlabel, hsize, htarget,
    hstamp, hcounts, ?_, ?_, ?_, ?_, ?_, hstampLe, hstampB, ?_, hsizes⟩
  · simpa [hj] using
      (show Stack "marked" "markedLen" n n 0 marked σ from
        ⟨hmarked, hmarkedLen, by omega, by intro i hi; omega⟩)
  · simpa [hj] using
      (show Stack "touched" "touchedLen" n n 0 touched σ from
        ⟨htouched, htouchedLen, by omega, by intro i hi; omega⟩)
  · simpa [hj] using prefixEnumerates_zero marked
  · simpa [hj] using prefixEnumerates_zero touched
  · intro v hv
    simp [hj, hstampNe v hv]
  · intro q hq
    simp [hj, hcounts0 q hq, classMultiplicity]

/-- If the next CSR slot contributes no new active vertex, only the scan
counter changes. -/
private lemma MarkInv.advanceSame
    {B n targetCap lo hi classCount token : ℕ}
    {activeName clsName : String} {active label size target : ℕ → ℕ}
    {σ : Env} (h : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ)
    (hjlt : σ.vars "j" < hi)
    (hsame : activeTargets target active lo (σ.vars "j" + 1) =
      activeTargets target active lo (σ.vars "j"))
    (v : ℕ) :
    MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target
      ((σ.setVar "v" v).setVar "j" (σ.vars "j" + 1)) := by
  rcases h with ⟨stamp, marked, touched, counts, hlo, hjhi, hjend,
    hcc, htoken, hn, hccn, hhic, hactive, hlabel, hsize, htarget,
    hstamp, hcounts, hmarkedStack, htouchedStack, hmarkedEnum,
    htouchedEnum, hstampMem, hstampLe, hstampB, hcountEq, hsizes⟩
  let σ' := (σ.setVar "v" v).setVar "j" (σ.vars "j" + 1)
  refine ⟨stamp, marked, touched, counts, by simp [σ']; omega,
    by simp [σ']; omega, by simp [σ', hjend], by simp [σ', hcc],
    by simp [σ', htoken], by simp [σ', hn], hccn, hhic,
    by simp [σ', hactive], by simp [σ', hlabel], by simp [σ', hsize],
    by simp [σ', htarget], by simp [σ', hstamp], by simp [σ', hcounts],
    ?_, ?_, ?_, ?_, ?_, hstampLe, hstampB, ?_, hsizes⟩
  · simpa [σ', hsame] using hmarkedStack
  · simpa [σ', hsame] using htouchedStack
  · simpa [σ', hsame] using hmarkedEnum
  · simpa [σ', hsame] using htouchedEnum
  · intro u hu
    simpa [σ', hsame] using hstampMem u hu
  · intro q hq
    simpa [σ', hsame] using hcountEq q hq

/-- Mathematical state update performed on the first occurrence of an active
target.  The hypotheses are only the scalar and array equations supplied by
the source execution. -/
private lemma MarkInv.advanceFresh
    {B n targetCap lo hi classCount token : ℕ}
    {activeName clsName : String} {active label size target : ℕ → ℕ}
    {σ σ' : Env} (h : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ)
    (hjlt : σ.vars "j" < hi)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveAt : active (target (σ.vars "j")) = 1)
    (hfresh : (σ.arrs "stamp").getD (target (σ.vars "j")) 0 ≠ token)
    (htokenB : token < B)
    (hj' : σ'.vars "j" = σ.vars "j" + 1)
    (hjend' : σ'.vars "jend" = hi)
    (hclassCount' : σ'.vars "classCount" = classCount)
    (htoken' : σ'.vars "token" = token) (hn' : σ'.vars "n" = n)
    (hmarkedLen' : σ'.vars "markedLen" =
      (activeTargets target active lo (σ.vars "j")).card + 1)
    (htouchedLen' : σ'.vars "touchedLen" =
      (touchedClasses label
        (insert (target (σ.vars "j"))
          (activeTargets target active lo (σ.vars "j")))).card)
    (hactive' : σ'.arrs activeName = arrOf n active)
    (hlabel' : σ'.arrs clsName = arrOf n label)
    (hsize' : σ'.arrs "classSize" = arrOf n size)
    (htarget' : σ'.arrs "tgt" = arrOf targetCap target)
    (hstamp' : σ'.arrs "stamp" =
      (σ.arrs "stamp").set (target (σ.vars "j")) token)
    (hmarked' : σ'.arrs "marked" =
      (σ.arrs "marked").set
        (activeTargets target active lo (σ.vars "j")).card
        (target (σ.vars "j")))
    (htouched' : σ'.arrs "touched" =
      if label (target (σ.vars "j")) ∈
          touchedClasses label (activeTargets target active lo (σ.vars "j")) then
        σ.arrs "touched"
      else
        (σ.arrs "touched").set
          (touchedClasses label
            (activeTargets target active lo (σ.vars "j"))).card
          (label (target (σ.vars "j"))))
    (hcounts' : σ'.arrs "markedCount" =
      (σ.arrs "markedCount").set (label (target (σ.vars "j")))
        ((σ.arrs "markedCount").getD
          (label (target (σ.vars "j"))) 0 + 1)) :
    MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ' := by
  rcases h with ⟨stamp, marked, touched, counts, hlo, hjhi, hjend,
    hcc, htoken, hn, hccn, hhic, hactive, hlabel, hsize, htarget,
    hstamp, hcounts, hmarkedStack, htouchedStack, hmarkedEnum,
    htouchedEnum, hstampMem, hstampLe, hstampB, hcountEq, hsizes⟩
  let M := activeTargets target active lo (σ.vars "j")
  let v := target (σ.vars "j")
  have hvn : v < n := htargetRange _ hlo hjlt
  have hvA : v ∈ activeVertices n active := mem_activeVertices.mpr ⟨hvn, hactiveAt⟩
  have hvlabel : label v < n :=
    (hsizes.1 v hvn hactiveAt).trans_le hccn
  have hstampv : stamp v ≠ token := by
    intro heq
    apply hfresh
    rw [hstamp, getD_arrOf stamp hvn, heq]
  have hvM : v ∉ M := by
    intro hv
    exact hstampv ((hstampMem v hvn).mpr hv)
  have hMnext : activeTargets target active lo (σ.vars "j" + 1) = insert v M := by
    rw [activeTargets_succ hlo, if_pos hactiveAt]
  have hMsub : insert v M ⊆ activeVertices n active := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hvA
    · rw [mem_activeTargets] at hu
      obtain ⟨hua, k, hlk, hkj, rfl⟩ := hu
      exact mem_activeVertices.mpr ⟨htargetRange k hlk (hkj.trans hjlt), hua⟩
  let marked' := upd marked M.card v
  let touched' := updateTouched label M touched v
  let stamp' := upd stamp v token
  let counts' := upd counts (label v) (counts (label v) + 1)
  have hstampArr' : σ'.arrs "stamp" = arrOf n stamp' := by
    rw [hstamp', hstamp, set_arrOf_eq_upd]
  have hmarkedArr' : σ'.arrs "marked" = arrOf n marked' := by
    rw [hmarked', hmarkedStack.arr, set_arrOf_eq_upd]
  have htouchedArr' : σ'.arrs "touched" = arrOf n touched' := by
    rw [htouched']
    by_cases hclass : label v ∈ touchedClasses label M
    · simp [touched', updateTouched, M, v, hclass, htouchedStack.arr]
    · simp [touched', updateTouched, M, v, hclass, htouchedStack.arr,
        set_arrOf_eq_upd]
  have hcountsArr' : σ'.arrs "markedCount" = arrOf n counts' := by
    rw [hcounts', hcounts, getD_arrOf counts hvlabel, set_arrOf_eq_upd]
  have hmarkedEnum' : PrefixEnumerates (insert v M).card marked' (insert v M) := by
    have hcard : (insert v M).card = M.card + 1 := Finset.card_insert_of_notMem hvM
    rw [hcard]
    exact hmarkedEnum.push hvM
  have htouchedEnum' : PrefixEnumerates
      (touchedClasses label (insert v M)).card touched'
      (touchedClasses label (insert v M)) :=
    prefixEnumerates_updateTouched htouchedEnum
  have hmarkedStack' : Stack "marked" "markedLen" n n
      (insert v M).card marked' σ' := by
    refine ⟨hmarkedArr', ?_, ?_, ?_⟩
    · rw [hmarkedLen', Finset.card_insert_of_notMem hvM]
    · calc
        (insert v M).card ≤ (activeVertices n active).card :=
          Finset.card_le_card hMsub
        _ ≤ (Finset.range n).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = n := Finset.card_range n
    · intro i hiEntry
      have hmemList : marked' i ∈ Stack.toList (insert v M).card marked' := by
        simp [Stack.toList, arrOf]
        exact ⟨i, hiEntry, rfl⟩
      have hmemSet := (hmarkedEnum'.2 _).mp hmemList
      exact (mem_activeVertices.mp (hMsub hmemSet)).1
  have htouchedSub : touchedClasses label (insert v M) ⊆ Finset.range n := by
    intro q hq
    obtain ⟨u, huM, rfl⟩ := mem_touchedClasses.mp hq
    have huA := mem_activeVertices.mp (hMsub huM)
    exact Finset.mem_range.mpr ((hsizes.1 u huA.1 huA.2).trans_le hccn)
  have htouchedStack' : Stack "touched" "touchedLen" n n
      (touchedClasses label (insert v M)).card touched' σ' := by
    refine ⟨htouchedArr', htouchedLen',
      Finset.card_le_card htouchedSub |>.trans_eq (Finset.card_range n), ?_⟩
    intro i hiEntry
    have hmemList : touched' i ∈
        Stack.toList (touchedClasses label (insert v M)).card touched' := by
      simp [Stack.toList, arrOf]
      exact ⟨i, hiEntry, rfl⟩
    exact Finset.mem_range.mp (htouchedSub ((htouchedEnum'.2 _).mp hmemList))
  refine ⟨stamp', marked', touched', counts', by rw [hj']; omega,
    by rw [hj']; omega, hjend', hclassCount', htoken', hn', hccn, hhic,
    hactive', hlabel', hsize', htarget', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hsizes⟩
  · exact hstampArr'
  · exact hcountsArr'
  · simpa [hj', hMnext] using hmarkedStack'
  · simpa [hj', hMnext] using htouchedStack'
  · simpa [hj', hMnext] using hmarkedEnum'
  · simpa [hj', hMnext] using htouchedEnum'
  · intro u hu
    rw [hj', hMnext]
    exact upd_eq_token_iff_insert (hstampMem u hu)
  · intro u hu
    simp only [stamp', upd]
    split
    · omega
    · exact hstampLe u hu
  · intro u hu
    simp only [stamp', upd]
    split
    · exact htokenB
    · exact hstampB u hu
  · intro q hq
    rw [hj', hMnext]
    rw [classMultiplicity_insert hvM]
    by_cases hlabelq : label v = q
    · subst q
      have hc := hcountEq (label v) hvlabel
      change counts (label v) = classMultiplicity label M (label v) at hc
      simp [counts', hc]
    · have hqlabel : q ≠ label v := Ne.symm hlabelq
      have hc := hcountEq q hq
      change counts q = classMultiplicity label M q at hc
      simp [counts', hlabelq, hqlabel, hc]

/-- One inactive CSR entry changes no marking data. -/
private lemma refineMarkBody_run_inactive
    {B n targetCap lo hi classCount token : ℕ}
    {activeName clsName : String} {active label size target : ℕ → ℕ}
    {σ : Env}
    (hI : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ)
    (hjlt : σ.vars "j" < hi)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B) (honeB : 1 < B)
    (hinactive : active (target (σ.vars "j")) ≠ 1) :
    ∃ σ', Run B (refineMarkBody activeName clsName) σ σ' 100 ∧
      MarkInv B n targetCap lo hi classCount token
        activeName clsName active label size target σ' ∧
      σ'.vars "j" = σ.vars "j" + 1 := by
  rcases hI with ⟨stamp, marked, touched, counts, hlo, hjhi, hjend,
    hcc, htoken, hn, hccn, hhic, hactive, hlabel, hsize, htarget,
    hstamp, hcounts, hmarkedStack, htouchedStack, hmarkedEnum,
    htouchedEnum, hstampMem, hstampLe, hstampB, hcountEq, hsizes⟩
  have hvn : target (σ.vars "j") < n := htargetRange _ hlo hjlt
  have hjB : σ.vars "j" < B :=
    lt_of_lt_of_le hjlt (hhic.trans htargetCapB.le)
  have hget : (σ.arrs "tgt")[σ.vars "j"]? =
      some (target (σ.vars "j")) := by
    rw [htarget, getElem?_arrOf target (hjlt.trans_le hhic)]
  have heval : (Expr.get "tgt" (.var "j")).evalB B σ =
      some (target (σ.vars "j")) :=
    evalB_get (evalB_var hjB) hget (hvn.trans hnB)
  let σ₁ := σ.setVar "v" (target (σ.vars "j"))
  have rv : Run B (.assign "v" (.get "tgt" (.var "j"))) σ σ₁ 6 := by
    exact (Run.assign heval).mono (by norm_num [Expr.size])
  have hactiveGet : (σ₁.arrs activeName)[σ₁.vars "v"]? =
      some (active (target (σ.vars "j"))) := by
    simp [σ₁, hactive, getElem?_arrOf active hvn]
  have hactiveEval : (Expr.get activeName (.var "v")).evalB B σ₁ =
      some (active (target (σ.vars "j"))) := by
    apply evalB_get
    · exact evalB_var (by simp [σ₁]; exact hvn.trans hnB)
    · exact hactiveGet
    · exact hactiveB _ hvn
  have htest : (Cond.eq (.get activeName (.var "v")) (.lit 1)).evalB B σ₁ =
      some false := by
    simpa [hinactive] using evalB_condEq hactiveEval (evalB_lit honeB)
  let σ₂ := σ₁.setVar "j" (σ.vars "j" + 1)
  have hj1B : σ.vars "j" + 1 < B := by
    exact lt_of_le_of_lt ((Nat.succ_le_of_lt hjlt).trans hhic) htargetCapB
  have rj : Run B (inc "j") σ₁ σ₂ 4 := by
    apply Run.assign
    exact evalB_bin (by simpa [σ₁] using evalB_var hjB)
      (evalB_lit honeB) (by simpa using hj1B)
  have hsame : activeTargets target active lo (σ.vars "j" + 1) =
      activeTargets target active lo (σ.vars "j") := by
    rw [activeTargets_succ hlo, if_neg hinactive]
  have hpost : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ₂ := by
    exact (show MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ from
        ⟨stamp, marked, touched, counts, hlo, hjhi, hjend, hcc, htoken,
          hn, hccn, hhic, hactive, hlabel, hsize, htarget, hstamp, hcounts,
          hmarkedStack, htouchedStack, hmarkedEnum, htouchedEnum, hstampMem,
          hstampLe, hstampB, hcountEq, hsizes⟩).advanceSame hjlt hsame _
  refine ⟨σ₂, ?_, hpost, by simp [σ₂]⟩
  exact (rv.seq ((Run.ite_false htest Run.skip).seq rj)).mono (by
    norm_num [refineMarkBody, seqs, Cond.size, Expr.size])

/-- A repeated active target is recognized by its stamp and is not recorded
twice. -/
private lemma refineMarkBody_run_duplicate
    {B n targetCap lo hi classCount token : ℕ}
    {activeName clsName : String} {active label size target : ℕ → ℕ}
    {σ : Env}
    (hI : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ)
    (hjlt : σ.vars "j" < hi)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (htokenB : token < B) (honeB : 1 < B)
    (hactiveAt : active (target (σ.vars "j")) = 1)
    (hduplicate : (σ.arrs "stamp").getD (target (σ.vars "j")) 0 = token) :
    ∃ σ', Run B (refineMarkBody activeName clsName) σ σ' 100 ∧
      MarkInv B n targetCap lo hi classCount token
        activeName clsName active label size target σ' ∧
      σ'.vars "j" = σ.vars "j" + 1 := by
  rcases hI with ⟨stamp, marked, touched, counts, hlo, hjhi, hjend,
    hcc, htoken, hn, hccn, hhic, hactive, hlabel, hsize, htarget,
    hstamp, hcounts, hmarkedStack, htouchedStack, hmarkedEnum,
    htouchedEnum, hstampMem, hstampLe, hstampB, hcountEq, hsizes⟩
  have hvn : target (σ.vars "j") < n := htargetRange _ hlo hjlt
  have hduplicate' : stamp (target (σ.vars "j")) = token := by
    rw [← getD_arrOf stamp hvn, ← hstamp]
    exact hduplicate
  have hjB : σ.vars "j" < B :=
    lt_of_lt_of_le hjlt (hhic.trans htargetCapB.le)
  have hget : (σ.arrs "tgt")[σ.vars "j"]? =
      some (target (σ.vars "j")) := by
    rw [htarget, getElem?_arrOf target (hjlt.trans_le hhic)]
  have heval : (Expr.get "tgt" (.var "j")).evalB B σ =
      some (target (σ.vars "j")) :=
    evalB_get (evalB_var hjB) hget (hvn.trans hnB)
  let σ₁ := σ.setVar "v" (target (σ.vars "j"))
  have rv : Run B (.assign "v" (.get "tgt" (.var "j"))) σ σ₁ 6 := by
    exact (Run.assign heval).mono (by norm_num [Expr.size])
  have hactiveEval : (Expr.get activeName (.var "v")).evalB B σ₁ =
      some (active (target (σ.vars "j"))) := by
    apply evalB_get
    · exact evalB_var (by simp [σ₁]; exact hvn.trans hnB)
    · simp [σ₁, hactive, getElem?_arrOf active hvn]
    · exact hactiveB _ hvn
  have hactiveTest :
      (Cond.eq (.get activeName (.var "v")) (.lit 1)).evalB B σ₁ =
        some true := by
    simpa [hactiveAt] using evalB_condEq hactiveEval (evalB_lit honeB)
  have hstampEval : (Expr.get "stamp" (.var "v")).evalB B σ₁ =
      some (stamp (target (σ.vars "j"))) := by
    apply evalB_get
    · exact evalB_var (by simp [σ₁]; exact hvn.trans hnB)
    · simp [σ₁, hstamp, getElem?_arrOf stamp hvn]
    · exact hstampB _ hvn
  have htokenEval : (Expr.var "token").evalB B σ₁ = some token := by
    have htkn : σ₁.vars "token" = token := by simp [σ₁, htoken]
    have htknB : σ₁.vars "token" < B := by rw [htkn]; exact htokenB
    rw [show (Expr.var "token").evalB B σ₁ = some (σ₁.vars "token") from
      evalB_var htknB, htkn]
  have hstampTest :
      (Cond.eq (.get "stamp" (.var "v")) (.var "token")).evalB B σ₁ =
        some true := by
    simpa [hduplicate'] using evalB_condEq hstampEval htokenEval
  let σ₂ := σ₁.setVar "j" (σ.vars "j" + 1)
  have hj1B : σ.vars "j" + 1 < B := by
    exact lt_of_le_of_lt ((Nat.succ_le_of_lt hjlt).trans hhic) htargetCapB
  have rj : Run B (inc "j") σ₁ σ₂ 4 := by
    apply Run.assign
    exact evalB_bin (by simpa [σ₁] using evalB_var hjB)
      (evalB_lit honeB) (by simpa using hj1B)
  have hvM : target (σ.vars "j") ∈
      activeTargets target active lo (σ.vars "j") :=
    (hstampMem _ hvn).mp hduplicate'
  have hsame : activeTargets target active lo (σ.vars "j" + 1) =
      activeTargets target active lo (σ.vars "j") := by
    rw [activeTargets_succ hlo, if_pos hactiveAt,
      Finset.insert_eq_self.mpr hvM]
  have hpost : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ₂ := by
    exact (show MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ from
        ⟨stamp, marked, touched, counts, hlo, hjhi, hjend, hcc, htoken,
          hn, hccn, hhic, hactive, hlabel, hsize, htarget, hstamp, hcounts,
          hmarkedStack, htouchedStack, hmarkedEnum, htouchedEnum, hstampMem,
          hstampLe, hstampB, hcountEq, hsizes⟩).advanceSame hjlt hsame _
  refine ⟨σ₂, ?_, hpost, by simp [σ₂]⟩
  exact (rv.seq ((Run.ite_true hactiveTest
    (Run.ite_true hstampTest Run.skip)).seq rj)).mono (by
      norm_num [refineMarkBody, seqs, Cond.size, Expr.size])

/-- A first active occurrence executes both marking stores, records its class
on the touched stack exactly when that class was previously absent, and
increments the exact class multiplicity. -/
private lemma refineMarkBody_run_fresh
    {B n targetCap lo hi classCount token : ℕ}
    {activeName clsName : String} {active label size target : ℕ → ℕ}
    {σ : Env}
    (hI : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ)
    (hjlt : σ.vars "j" < hi)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (htokenB : token < B) (honeB : 1 < B)
    (hactiveAt : active (target (σ.vars "j")) = 1)
    (hfresh : (σ.arrs "stamp").getD (target (σ.vars "j")) 0 ≠ token)
    (haStamp : activeName ≠ "stamp") (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (hcStamp : clsName ≠ "stamp") (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount") :
    ∃ σ', Run B (refineMarkBody activeName clsName) σ σ' 100 ∧
      MarkInv B n targetCap lo hi classCount token
        activeName clsName active label size target σ' ∧
      σ'.vars "j" = σ.vars "j" + 1 := by
  rcases hI with ⟨stamp, marked, touched, counts, hlo, hjhi, hjend,
    hcc, htoken, hn, hccn, hhic, hactive, hlabel, hsize, htarget,
    hstamp, hcounts, hmarkedStack, htouchedStack, hmarkedEnum,
    htouchedEnum, hstampMem, hstampLe, hstampB, hcountEq, hsizes⟩
  have hI₀ : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ :=
    ⟨stamp, marked, touched, counts, hlo, hjhi, hjend, hcc, htoken,
      hn, hccn, hhic, hactive, hlabel, hsize, htarget, hstamp, hcounts,
      hmarkedStack, htouchedStack, hmarkedEnum, htouchedEnum, hstampMem,
      hstampLe, hstampB, hcountEq, hsizes⟩
  let M := activeTargets target active lo (σ.vars "j")
  let v := target (σ.vars "j")
  let q := label v
  let TC := touchedClasses label M
  have hvn : v < n := htargetRange _ hlo hjlt
  have hvA : v ∈ activeVertices n active :=
    mem_activeVertices.mpr ⟨hvn, hactiveAt⟩
  have hqcc : q < classCount := hsizes.1 v hvn hactiveAt
  have hqn : q < n := hqcc.trans_le hccn
  have hvB : v < B := hvn.trans hnB
  have hqB : q < B := hqn.trans hnB
  have hjB : σ.vars "j" < B :=
    lt_of_lt_of_le hjlt (hhic.trans htargetCapB.le)
  have hstampv : stamp v ≠ token := by
    intro heq
    apply hfresh
    rw [hstamp, getD_arrOf stamp hvn, heq]
  have hvM : v ∉ M := by
    intro hv
    exact hstampv ((hstampMem v hvn).mpr hv)
  have hMsub : M ⊆ activeVertices n active := by
    intro u hu
    rw [mem_activeTargets] at hu
    obtain ⟨hua, k, hlk, hkj, rfl⟩ := hu
    exact mem_activeVertices.mpr
      ⟨htargetRange k hlk (hkj.trans hjlt), hua⟩
  have hMcard : M.card < n := by
    have hins : (insert v M).card ≤ (Finset.range n).card := by
      apply Finset.card_le_card
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_range.mpr hvn
      · exact Finset.mem_range.mpr (mem_activeVertices.mp (hMsub hu)).1
    rw [Finset.card_insert_of_notMem hvM, Finset.card_range] at hins
    omega
  have hMcardB : M.card < B := hMcard.trans hnB
  have hMcard1B : M.card + 1 < B := by omega
  have hTCcard : TC.card ≤ M.card := by
    simpa [TC, touchedClasses] using Finset.card_image_le (s := M) (f := label)
  have hTCcardB : TC.card < B := hTCcard.trans_lt hMcardB
  have hTCcard1B : TC.card + 1 < B := by omega
  have hcountVal : counts q = classMultiplicity label M q := by
    simpa [q, M] using hcountEq q hqn
  have hcountLe : counts q ≤ M.card := by
    rw [hcountVal]
    exact classMultiplicity_le_card label M q
  have hcountB : counts q < B := hcountLe.trans_lt hMcardB
  have hcount1B : counts q + 1 < B := by omega
  have hget : (σ.arrs "tgt")[σ.vars "j"]? = some v := by
    rw [htarget, getElem?_arrOf target (hjlt.trans_le hhic)]
  have heval : (Expr.get "tgt" (.var "j")).evalB B σ = some v :=
    evalB_get (evalB_var hjB) hget hvB
  let σ₁ := σ.setVar "v" v
  have rv : Run B (.assign "v" (.get "tgt" (.var "j"))) σ σ₁ 6 := by
    exact (Run.assign heval).mono (by norm_num [Expr.size])
  have hactiveEval : (Expr.get activeName (.var "v")).evalB B σ₁ =
      some (active v) := by
    apply evalB_get
    · exact evalB_var (by simp [σ₁]; exact hvB)
    · simp [σ₁, hactive, getElem?_arrOf active hvn]
    · exact hactiveB _ hvn
  have hactiveTest :
      (Cond.eq (.get activeName (.var "v")) (.lit 1)).evalB B σ₁ =
        some true := by
    have hav : active v = 1 := by simpa [v] using hactiveAt
    simpa [hav] using evalB_condEq hactiveEval (evalB_lit honeB)
  have hstampEval : (Expr.get "stamp" (.var "v")).evalB B σ₁ =
      some (stamp v) := by
    apply evalB_get
    · exact evalB_var (by simp [σ₁]; exact hvB)
    · simp [σ₁, hstamp, getElem?_arrOf stamp hvn]
    · exact hstampB _ hvn
  have htokenEval : (Expr.var "token").evalB B σ₁ = some token := by
    have htkn : σ₁.vars "token" = token := by simp [σ₁, htoken]
    have htknB : σ₁.vars "token" < B := by rw [htkn]; exact htokenB
    rw [show (Expr.var "token").evalB B σ₁ = some (σ₁.vars "token") from
      evalB_var htknB, htkn]
  have hstampTest :
      (Cond.eq (.get "stamp" (.var "v")) (.var "token")).evalB B σ₁ =
        some false := by
    simpa [hstampv] using evalB_condEq hstampEval htokenEval
  let σ₂ := σ₁.setArr "stamp" v token
  have rstamp : Run B (.store "stamp" (.var "v") (.var "token"))
      σ₁ σ₂ 3 := by
    exact Run.store (evalB_var (by simp [σ₁]; exact hvB)) htokenEval (by
      rw [show σ₁.arrs "stamp" = σ.arrs "stamp" by simp [σ₁], hstamp,
        length_arrOf]
      exact hvn)
  let σ₃ := σ₂.setArr "marked" M.card v
  have rmarked : Run B (.store "marked" (.var "markedLen") (.var "v"))
      σ₂ σ₃ 3 := by
    have hml : σ₂.vars "markedLen" = M.card := by
      simp [σ₂, σ₁, hmarkedStack.height, M]
    apply Run.store
    · rw [show (Expr.var "markedLen").evalB B σ₂ =
          some (σ₂.vars "markedLen") from evalB_var (by rw [hml]; exact hMcardB),
        hml]
    · exact evalB_var (by simp [σ₂, σ₁]; exact hvB)
    · rw [show σ₂.arrs "marked" = σ.arrs "marked" by simp [σ₂, σ₁],
        hmarkedStack.arr, length_arrOf]
      exact hMcard
  let σ₄ := σ₃.setVar "markedLen" (M.card + 1)
  have rmarkedLen : Run B (inc "markedLen") σ₃ σ₄ 4 := by
    have hml : σ₃.vars "markedLen" = M.card := by
      simp [σ₃, σ₂, σ₁, hmarkedStack.height, M]
    apply Run.assign
    apply evalB_bin
    · rw [show (Expr.var "markedLen").evalB B σ₃ =
          some (σ₃.vars "markedLen") from evalB_var (by rw [hml]; exact hMcardB),
        hml]
    · exact evalB_lit honeB
    · exact hMcard1B
  let σ₅ := σ₄.setVar "cl" q
  have hclsEval : (Expr.get clsName (.var "v")).evalB B σ₄ = some q := by
    apply evalB_get
    · exact evalB_var (by simp [σ₄, σ₃, σ₂, σ₁]; exact hvB)
    · simp [σ₄, σ₃, σ₂, σ₁, hlabel, hcStamp, hcMarked,
        getElem?_arrOf label hvn, q]
    · exact hqB
  have rcl : Run B (.assign "cl" (.get clsName (.var "v"))) σ₄ σ₅ 6 := by
    exact (Run.assign hclsEval).mono (by norm_num [Expr.size])
  by_cases hclass : q ∈ TC
  · have hcountPos : 0 < counts q := by
      rw [hcountVal]
      exact classMultiplicity_pos_iff.mpr (by simpa [q, M, TC] using hclass)
    have hcountEval : (Expr.get "markedCount" (.var "cl")).evalB B σ₅ =
        some (counts q) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₅]; exact hqB)
      · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hcounts,
          getElem?_arrOf counts hqn]
      · exact hcountB
    have hcountTest :
        (Cond.eq (.get "markedCount" (.var "cl")) (.lit 0)).evalB B σ₅ =
          some false := by
      have hzeroB : 0 < B := by omega
      have heq := evalB_condEq hcountEval (evalB_lit hzeroB)
      simpa [Nat.ne_of_gt hcountPos] using heq
    have rtouched : Run B
        (.ite (.eq (.get "markedCount" (.var "cl")) (.lit 0))
          (seqs [.store "touched" (.var "touchedLen") (.var "cl"),
            inc "touchedLen"])
          .skip) σ₅ σ₅ 10 := by
      exact (Run.ite_false hcountTest Run.skip).mono (by
        norm_num [Cond.size, Expr.size])
    let σ₆ := σ₅.setArr "markedCount" q (counts q + 1)
    have haddEval :
        (Expr.add (.get "markedCount" (.var "cl")) (.lit 1)).evalB B σ₅ =
          some (counts q + 1) := by
      exact evalB_bin hcountEval (evalB_lit honeB) hcount1B
    have rcount : Run B (.store "markedCount" (.var "cl")
        (.add (.get "markedCount" (.var "cl")) (.lit 1))) σ₅ σ₆ 8 := by
      have hclEval : (Expr.var "cl").evalB B σ₅ = some q := by
        have hcl : σ₅.vars "cl" = q := by simp [σ₅]
        rw [show (Expr.var "cl").evalB B σ₅ = some (σ₅.vars "cl") from
          evalB_var (by rw [hcl]; exact hqB), hcl]
      have hr := Run.store hclEval haddEval (by
          rw [show σ₅.arrs "markedCount" = σ.arrs "markedCount" by
              simp [σ₅, σ₄, σ₃, σ₂, σ₁],
            hcounts, length_arrOf]
          exact hqn)
      simpa [σ₆] using hr.mono (by norm_num [Expr.size])
    let σ₇ := σ₆.setVar "j" (σ.vars "j" + 1)
    have hj1B : σ.vars "j" + 1 < B := by
      exact lt_of_le_of_lt ((Nat.succ_le_of_lt hjlt).trans hhic) htargetCapB
    have rj : Run B (inc "j") σ₆ σ₇ 4 := by
      apply Run.assign
      have hjeval : (Expr.var "j").evalB B σ₆ = some (σ.vars "j") := by
        simpa [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁] using
          (evalB_var hjB)
      exact evalB_bin hjeval (evalB_lit honeB) (by simpa using hj1B)
    have rfresh : Run B
        (seqs [
          .store "stamp" (.var "v") (.var "token"),
          .store "marked" (.var "markedLen") (.var "v"),
          inc "markedLen", .assign "cl" (.get clsName (.var "v")),
          .ite (.eq (.get "markedCount" (.var "cl")) (.lit 0))
            (seqs [.store "touched" (.var "touchedLen") (.var "cl"),
              inc "touchedLen"])
            .skip,
          .store "markedCount" (.var "cl")
            (.add (.get "markedCount" (.var "cl")) (.lit 1))])
        σ₁ σ₆ 40 := by
      simpa [seqs] using
        (rstamp.seq (rmarked.seq (rmarkedLen.seq (rcl.seq (rtouched.seq rcount))))).mono
          (by omega)
    have hrun : Run B (refineMarkBody activeName clsName) σ σ₇ 100 := by
      exact (rv.seq ((Run.ite_true hactiveTest
        (Run.ite_false hstampTest rfresh)).seq rj)).mono (by
          norm_num [refineMarkBody, seqs, Cond.size, Expr.size])
    have hTCinsert : touchedClasses label (insert v M) = TC := by
      rw [touchedClasses_insert]
      exact Finset.insert_eq_self.mpr (by simpa [q, TC] using hclass)
    have hpost : MarkInv B n targetCap lo hi classCount token
        activeName clsName active label size target σ₇ := by
      apply MarkInv.advanceFresh hI₀ hjlt htargetRange hactiveAt hfresh htokenB
      · simp [σ₇, σ₆]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hjend]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hcc]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htoken]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hn]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁,
          hmarkedStack.height, M]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁,
          htouchedStack.height, hTCinsert, M, v, TC]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hactive,
          haStamp, haMarked, haCount]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hlabel,
          hcStamp, hcMarked, hcCount]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hsize]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, htarget]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, v]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁,
          hmarkedStack.height, M, v]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁,
          hclass, q, TC, M, v]
      · simp [σ₇, σ₆, σ₅, σ₄, σ₃, σ₂, σ₁,
          hcounts, getElem?_arrOf counts hqn, v, q, M]
    exact ⟨σ₇, hrun, hpost, by simp [σ₇, σ₆]⟩
  · have hcountZero : counts q = 0 := by
      rw [hcountVal]
      exact Nat.eq_zero_of_not_pos (fun hp => hclass
        (by simpa [q, M, TC] using classMultiplicity_pos_iff.mp hp))
    have hcountEval : (Expr.get "markedCount" (.var "cl")).evalB B σ₅ =
        some 0 := by
      apply evalB_get
      · exact evalB_var (by simp [σ₅]; exact hqB)
      · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hcounts,
          getElem?_arrOf counts hqn, hcountZero]
      · omega
    have hcountTest :
        (Cond.eq (.get "markedCount" (.var "cl")) (.lit 0)).evalB B σ₅ =
          some true := by
      have hzeroB : 0 < B := by omega
      simpa using evalB_condEq hcountEval (evalB_lit hzeroB)
    let σ₅a := σ₅.setArr "touched" TC.card q
    have rtouchedStore : Run B (.store "touched" (.var "touchedLen") (.var "cl"))
        σ₅ σ₅a 3 := by
      have htl : σ₅.vars "touchedLen" = TC.card := by
        simp [σ₅, σ₄, σ₃, σ₂, σ₁,
          htouchedStack.height, TC, M]
      apply Run.store
      · rw [show (Expr.var "touchedLen").evalB B σ₅ =
            some (σ₅.vars "touchedLen") from
          evalB_var (by rw [htl]; exact hTCcardB), htl]
      · exact evalB_var (by simp [σ₅]; exact hqB)
      · rw [show σ₅.arrs "touched" = σ.arrs "touched" by
            simp [σ₅, σ₄, σ₃, σ₂, σ₁],
          htouchedStack.arr, length_arrOf]
        exact hTCcard.trans_lt hMcard
    let σ₅b := σ₅a.setVar "touchedLen" (TC.card + 1)
    have rtouchedLen : Run B (inc "touchedLen") σ₅a σ₅b 4 := by
      have htl : σ₅a.vars "touchedLen" = TC.card := by
        simp [σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁,
          htouchedStack.height, TC, M]
      apply Run.assign
      apply evalB_bin
      · rw [show (Expr.var "touchedLen").evalB B σ₅a =
            some (σ₅a.vars "touchedLen") from
          evalB_var (by rw [htl]; exact hTCcardB), htl]
      · exact evalB_lit honeB
      · exact hTCcard1B
    have rtouchedBranch : Run B
        (seqs [.store "touched" (.var "touchedLen") (.var "cl"),
          inc "touchedLen"]) σ₅ σ₅b 7 := by
      simpa [seqs] using rtouchedStore.seq rtouchedLen
    have rtouched : Run B
        (.ite (.eq (.get "markedCount" (.var "cl")) (.lit 0))
          (seqs [.store "touched" (.var "touchedLen") (.var "cl"),
            inc "touchedLen"])
          .skip) σ₅ σ₅b 16 := by
      exact (Run.ite_true hcountTest rtouchedBranch).mono (by
        norm_num [Cond.size, Expr.size])
    let σ₆ := σ₅b.setArr "markedCount" q 1
    have hcountEval' : (Expr.get "markedCount" (.var "cl")).evalB B σ₅b =
        some 0 := by
      simpa [σ₅b, σ₅a] using hcountEval
    have haddEval' :
        (Expr.add (.get "markedCount" (.var "cl")) (.lit 1)).evalB B σ₅b =
          some 1 := by
      exact evalB_bin hcountEval' (evalB_lit honeB) honeB
    have rcount : Run B (.store "markedCount" (.var "cl")
        (.add (.get "markedCount" (.var "cl")) (.lit 1))) σ₅b σ₆ 8 := by
      have hclEval : (Expr.var "cl").evalB B σ₅b = some q := by
        have hcl : σ₅b.vars "cl" = q := by simp [σ₅b, σ₅a, σ₅]
        rw [show (Expr.var "cl").evalB B σ₅b = some (σ₅b.vars "cl") from
          evalB_var (by rw [hcl]; exact hqB), hcl]
      have hr := Run.store hclEval haddEval' (by
          rw [show σ₅b.arrs "markedCount" = σ.arrs "markedCount" by
              simp [σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁],
            hcounts, length_arrOf]
          exact hqn)
      simpa [σ₆] using hr.mono (by norm_num [Expr.size])
    let σ₇ := σ₆.setVar "j" (σ.vars "j" + 1)
    have hj1B : σ.vars "j" + 1 < B := by
      exact lt_of_le_of_lt ((Nat.succ_le_of_lt hjlt).trans hhic) htargetCapB
    have rj : Run B (inc "j") σ₆ σ₇ 4 := by
      apply Run.assign
      have hjeval : (Expr.var "j").evalB B σ₆ = some (σ.vars "j") := by
        simpa [σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁]
          using (evalB_var hjB)
      exact evalB_bin hjeval (evalB_lit honeB) (by simpa using hj1B)
    have rfresh : Run B
        (seqs [
          .store "stamp" (.var "v") (.var "token"),
          .store "marked" (.var "markedLen") (.var "v"),
          inc "markedLen", .assign "cl" (.get clsName (.var "v")),
          .ite (.eq (.get "markedCount" (.var "cl")) (.lit 0))
            (seqs [.store "touched" (.var "touchedLen") (.var "cl"),
              inc "touchedLen"])
            .skip,
          .store "markedCount" (.var "cl")
            (.add (.get "markedCount" (.var "cl")) (.lit 1))])
        σ₁ σ₆ 50 := by
      simpa [seqs] using
        (rstamp.seq (rmarked.seq (rmarkedLen.seq (rcl.seq (rtouched.seq rcount))))).mono
          (by omega)
    have hrun : Run B (refineMarkBody activeName clsName) σ σ₇ 100 := by
      exact (rv.seq ((Run.ite_true hactiveTest
        (Run.ite_false hstampTest rfresh)).seq rj)).mono (by
          norm_num [refineMarkBody, seqs, Cond.size, Expr.size])
    have hTCinsert : (touchedClasses label (insert v M)).card = TC.card + 1 := by
      rw [touchedClasses_insert, Finset.card_insert_of_notMem]
      simpa [q, TC] using hclass
    have hpost : MarkInv B n targetCap lo hi classCount token
        activeName clsName active label size target σ₇ := by
      apply MarkInv.advanceFresh hI₀ hjlt htargetRange hactiveAt hfresh htokenB
      · simp [σ₇, σ₆]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, hjend]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, hcc]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, htoken]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, hn]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁,
          hmarkedStack.height, M]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁,
          hTCinsert, M, v, TC]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, hactive,
          haStamp, haMarked, haTouched, haCount]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, hlabel,
          hcStamp, hcMarked, hcTouched, hcCount]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, hsize]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, htarget]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁, v]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁,
          hmarkedStack.height, M, v]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁,
          hTCinsert, hclass, M, v, q, TC]
      · simp [σ₇, σ₆, σ₅b, σ₅a, σ₅, σ₄, σ₃, σ₂, σ₁,
          hcounts, getElem?_arrOf counts hqn, hcountZero, v, q, M]
    exact ⟨σ₇, hrun, hpost, by simp [σ₇, σ₆]⟩

/-- Uniform specification of one duplicate-tolerant CSR marking step. -/
lemma refineMarkBody_spec
    {B n targetCap lo hi classCount token : ℕ}
    {activeName clsName : String} {active label size target : ℕ → ℕ}
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (htokenB : token < B) (honeB : 1 < B)
    (haStamp : activeName ≠ "stamp") (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (hcStamp : clsName ≠ "stamp") (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount") :
    Spec B
      (fun τ => MarkInv B n targetCap lo hi classCount token
        activeName clsName active label size target τ ∧ τ.vars "j" < hi)
      (refineMarkBody activeName clsName)
      (fun τ τ' => MarkInv B n targetCap lo hi classCount token
          activeName clsName active label size target τ' ∧
        τ'.vars "j" = τ.vars "j" + 1)
      100 := by
  intro τ hτ
  rcases hτ with ⟨hI, hjlt⟩
  by_cases hactiveAt : active (target (τ.vars "j")) = 1
  · by_cases hduplicate :
        (τ.arrs "stamp").getD (target (τ.vars "j")) 0 = token
    · exact refineMarkBody_run_duplicate hI hjlt htargetRange hactiveB
        hnB htargetCapB htokenB honeB hactiveAt hduplicate
    · exact refineMarkBody_run_fresh hI hjlt htargetRange hactiveB
        hnB htargetCapB htokenB honeB hactiveAt hduplicate
        haStamp haMarked haTouched haCount hcStamp hcMarked hcTouched hcCount
  · exact refineMarkBody_run_inactive hI hjlt htargetRange hactiveB
      hnB htargetCapB honeB hactiveAt

/-- The whole CSR interval scan terminates at `hi` and represents exactly
the distinct active targets and their touched classes. -/
lemma refineMarkLoop_run
    {B n targetCap lo hi classCount token : ℕ}
    {activeName clsName : String} {active label size target : ℕ → ℕ}
    {σ : Env}
    (hI : MarkInv B n targetCap lo hi classCount token
      activeName clsName active label size target σ)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (htokenB : token < B) (honeB : 1 < B)
    (haStamp : activeName ≠ "stamp") (haMarked : activeName ≠ "marked")
    (haTouched : activeName ≠ "touched")
    (haCount : activeName ≠ "markedCount")
    (hcStamp : clsName ≠ "stamp") (hcMarked : clsName ≠ "marked")
    (hcTouched : clsName ≠ "touched")
    (hcCount : clsName ≠ "markedCount") :
    ∃ σ', Run B
        (.while (.lt (.var "j") (.var "jend"))
          (refineMarkBody activeName clsName))
        σ σ' ((100 + 4) * (hi - lo) + 4) ∧
      MarkInv B n targetCap lo hi classCount token
        activeName clsName active label size target σ' ∧
      σ'.vars "j" = hi := by
  let I := MarkInv B n targetCap lo hi classCount token
    activeName clsName active label size target
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "j" < hi)
      (refineMarkBody activeName clsName)
      (fun τ τ' => I τ' ∧ τ'.vars "j" = τ.vars "j" + 1) 100 :=
    refineMarkBody_spec htargetRange hactiveB hnB htargetCapB htokenB honeB
      haStamp haMarked haTouched haCount hcStamp hcMarked hcTouched hcCount
  have hjB : ∀ τ, I τ → τ.vars "j" < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, hjhi, _, _, _, _, _, hhic, -⟩
    exact lt_of_le_of_lt (hjhi.trans hhic) htargetCapB
  have hjendB : ∀ τ, I τ → τ.vars "jend" < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, _, hjend, _, _, _, _, hhic, -⟩
    rw [hjend]
    exact lt_of_le_of_lt hhic htargetCapB
  have hjend : ∀ τ, I τ → τ.vars "jend" = hi := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, _, hjend, -⟩
    exact hjend
  have hjhi : ∀ τ, I τ → τ.vars "j" ≤ hi := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, hjhi, -⟩
    exact hjhi
  exact (Spec.forRange "j" "jend" I hi 100
    ((100 + 4) * (hi - lo) + 4)
    hjB hjendB hjend hjhi hbody (fun _ h => h)
    (fun τ h => by
      rcases h with ⟨_, _, _, _, hlo, -⟩
      omega)).run hI

end Lax235315Proofs.Construction.MarkingSource
