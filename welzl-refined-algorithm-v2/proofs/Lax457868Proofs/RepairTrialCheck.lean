import Mathlib.Tactic
import Lax457868Proofs.RepairDomainSource
import Lax457868Proofs.RepairFilterSource
import Lax457868Proofs.EnumeratedDraws
import Lax457868Proofs.SamplePacking
import Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
import Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-! A single row of the local-repair class scan is compared against the
fixed desired trace using the existing degree-local filtered append. -/

namespace Lax457868Proofs.RepairTrialCheck

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding Lax11Proofs.CC
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.NeighborScan
open Lax457868Proofs.RepairFilterSource
open Lax457868Proofs.EnumeratedDraws
open Lax457868Proofs.RepairDomainSource
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.SourceRenaming

/-- Simultaneously move the filter's scratch buffer, count, and cursor away
from the sampler's fixed draw state. -/
def trialFilterNames : Names where
  scalar := Equiv.swap "repairCursor" "trialFilterCursor" *
    Equiv.swap "drawModulus" "trialDiffCount"
  array := Equiv.swap "drawDomain" "trialDiffList"

def filterTraceRow : Com :=
  renameCom trialFilterNames
    (appendFiltered "trialRowList" "trialDesiredMarks" "trialRowLen")

/-- Append precisely the row trace elements absent from the fixed desired
trace. The resulting count is zero exactly when the row trace is contained
in the desired trace. -/
lemma filterTraceRow_run
    {B n h : ℕ} {σ : Env} {src marks domain : ℕ → ℕ} {S T : Finset ℕ}
    (hn : σ.vars "n" = n)
    (hlen : σ.vars "trialRowLen" = h)
    (hcount : σ.vars "trialDiffCount" = 0)
    (hsrc : σ.arrs "trialRowList" = arrOf n src)
    (hmarks : σ.arrs "trialDesiredMarks" = arrOf n marks)
    (hdomain : σ.arrs "trialDiffList" = arrOf n domain)
    (hrow : PrefixEnumerates h src S)
    (hSrange : S ⊆ Finset.range n)
    (hmarks01 : ∀ v < n, marks v ≤ 1)
    (hmarksMem : ∀ v < n, marks v = 1 ↔ v ∈ T)
    (hB : n < B) (honeB : 1 < B) :
    ∃ σ' diffList,
      Run B filterTraceRow σ σ' (24 * h + 6) ∧
      σ'.arrs "trialDiffList" = arrOf n diffList ∧
      PrefixEnumerates (σ'.vars "trialDiffCount") diffList (S \ T) ∧
      σ'.vars "trialDiffCount" = (S \ T).card ∧
      σ'.vars "trialFilterCursor" = h ∧
      σ'.arrs "trialRowList" = arrOf n src ∧
      σ'.arrs "trialDesiredMarks" = arrOf n marks ∧
      σ'.vars "trialRowLen" = h ∧ σ'.vars "n" = n ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let ρ := trialFilterNames
  let τ := renameEnv ρ.inverse σ
  have hnτ : τ.vars "n" = n := by
    change σ.vars (ρ.scalar "n") = n
    simp [ρ, trialFilterNames]
    exact hn
  have hlenτ : τ.vars "trialRowLen" = h := by
    change σ.vars (ρ.scalar "trialRowLen") = h
    simp [ρ, trialFilterNames]
    exact hlen
  have hcountτ : τ.vars "drawModulus" = 0 := by
    change σ.vars (ρ.scalar "drawModulus") = 0
    simp [ρ, trialFilterNames]
    exact hcount
  have hsrcτ : τ.arrs "trialRowList" = arrOf n src := by
    change σ.arrs (ρ.array "trialRowList") = arrOf n src
    simp [ρ, trialFilterNames]
    exact hsrc
  have hmarksτ : τ.arrs "trialDesiredMarks" = arrOf n marks := by
    change σ.arrs (ρ.array "trialDesiredMarks") = arrOf n marks
    simp [ρ, trialFilterNames]
    exact hmarks
  have hdomainτ : τ.arrs "drawDomain" = arrOf n domain := by
    change σ.arrs (ρ.array "drawDomain") = arrOf n domain
    simp [ρ, trialFilterNames]
    exact hdomain
  have hset : (Stack.toList h src).toFinset = S := by
    ext v
    simpa using hrow.2 v
  have hrowCardEq : (Stack.toList h src).length = S.card := by
    rw [← hset, List.toFinset_card_of_nodup hrow.1]
  have hrowCard : h ≤ n := by
    have hc : (Stack.toList h src).length = h := by simp [Stack.toList]
    rw [hc] at hrowCardEq
    rw [hrowCardEq]
    simpa using Finset.card_le_card hSrange
  have hdiff : selectedPrefix (Stack.toList h src) marks h = S \ T :=
    selectedPrefix_eq_sdiff hrow hSrange hmarks01 hmarksMem
  have hcap : (∅ ∪ selectedPrefix (Stack.toList h src) marks h).card ≤ n := by
    have hsub : S \ T ⊆ Finset.range n := (Finset.sdiff_subset).trans hSrange
    rw [hdiff]
    simpa using Finset.card_le_card hsub
  obtain ⟨τ', out, rfilter, hout, hpref, hcount', hcursor,
    hsrc', hmarks', hlen', hn', _hframeArrs, _hframeVars, hinp, houtp⟩ :=
    appendFiltered_run (srcName := "trialRowList")
      (marksName := "trialDesiredMarks") (lenName := "trialRowLen")
      (by decide) hnτ hlenτ hsrcτ hmarksτ hdomainτ
      (by simpa [hcountτ] using prefixEnumerates_zero domain)
      hrow hSrange hrowCard hmarks01 (by simp) hcap hB honeB
  let σ' := renameEnv ρ τ'
  have hrun : Run B filterTraceRow σ σ' (24 * h + 6) := by
    simpa [filterTraceRow, ρ, τ, σ', appendFilteredBodyCost,
      appendFilteredBody, appendFilteredTest, Expr.size, Cond.size] using
      run_rename ρ rfilter
  refine ⟨σ', out, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change σ'.arrs (ρ.array "drawDomain") = arrOf n out
    have hmap : ρ.array "drawDomain" = "trialDiffList" := by
      simp [ρ, trialFilterNames]
    rw [hmap]
    exact hout
  · change PrefixEnumerates (σ'.vars (ρ.scalar "drawModulus")) out (S \ T)
    simp [trialFilterNames, ρ, hdiff] at *
    exact hpref
  · change σ'.vars (ρ.scalar "drawModulus") = (S \ T).card
    simp [trialFilterNames, ρ, hdiff] at *
    exact hcount'
  · change σ'.vars (ρ.scalar "repairCursor") = h
    simp [trialFilterNames, ρ]
    exact hcursor
  · change σ'.arrs (ρ.array "trialRowList") = arrOf n src
    simp [trialFilterNames, ρ]
    exact hsrc'
  · change σ'.arrs (ρ.array "trialDesiredMarks") = arrOf n marks
    simp [trialFilterNames, ρ]
    exact hmarks'
  · change σ'.vars (ρ.scalar "trialRowLen") = h
    simp [trialFilterNames, ρ]
    exact hlen'
  · change σ'.vars (ρ.scalar "n") = n
    simp [trialFilterNames, ρ]
    exact hn'
  · exact hrun.frame_arr "drawDomain" (by
      simp [filterTraceRow, trialFilterNames, appendFiltered,
        appendFilteredBody, seqs, inc, Com.warrs] <;> decide)
  · exact hrun.frame_var "drawModulus" (by
      simp [filterTraceRow, trialFilterNames, appendFiltered,
        appendFilteredBody, seqs, inc, Com.wvars] <;> decide)
  · exact hinp
  · exact houtp

/-- With equal cardinalities, an empty filtered difference certifies equal
traces. -/
lemma traceDiff_empty_iff_eq {h : ℕ} {S T : Finset ℕ}
    (hcardS : h = S.card) (hcardT : h = T.card) :
    (S \ T).card = 0 ↔ S = T := by
  constructor
  · intro hempty
    have hdiff : S \ T = ∅ := Finset.card_eq_zero.mp hempty
    have hsub : S ⊆ T := by
      intro v hv
      by_contra hnot
      have : v ∈ S \ T := Finset.mem_sdiff.mpr ⟨hv, hnot⟩
      simpa [hdiff] using this
    apply Finset.eq_of_subset_of_card_le hsub
    rw [← hcardS, ← hcardT]
  · intro heq
    simp [heq]

/-- Convert the filtered-difference count and the two trace lengths to a
zero-one equality flag. -/
def setTraceEqualityFlag : Com :=
  seqs [
  .assign "trialTraceEqual" (.lit 0),
  .ite (.eq (.var "trialDiffCount") (.lit 0))
    (.ite (.eq (.var "trialRowLen") (.var "trialDesiredLen"))
      (.assign "trialTraceEqual" (.lit 1))
      (seqs [.skip, .skip]))
    (seqs [.skip, .skip, .skip, .skip, .skip, .skip])]

lemma setTraceEqualityFlag_run
    {B h d diff : ℕ} {σ : Env}
    (hrow : σ.vars "trialRowLen" = h)
    (hdesired : σ.vars "trialDesiredLen" = d)
    (hdiff : σ.vars "trialDiffCount" = diff)
    (hrowB : h < B) (hdesiredB : d < B) (hdiffB : diff < B)
    (honeB : 1 < B) :
    ∃ σ', Run B setTraceEqualityFlag σ σ' 12 ∧
      (σ'.vars "trialTraceEqual" = 1 ↔ diff = 0 ∧ h = d) ∧
      σ'.vars "trialTraceEqual" ≤ 1 ∧
      (∀ a, σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ≠ "trialTraceEqual" → σ'.vars x = σ.vars x) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let σ₀ := σ.setVar "trialTraceEqual" 0
  have rinit : Run B (.assign "trialTraceEqual" (.lit 0)) σ σ₀ 2 := by
    simpa [σ₀] using Run.assign (evalB_lit (by omega : 0 < B))
  have hdiffBound : σ.vars "trialDiffCount" < B := by rw [hdiff]; exact hdiffB
  have hrowBound : σ.vars "trialRowLen" < B := by rw [hrow]; exact hrowB
  have hdesiredBound : σ.vars "trialDesiredLen" < B := by rw [hdesired]; exact hdesiredB
  have hdiffEval : (Expr.var "trialDiffCount").evalB B σ₀ = some diff := by
    simpa [σ₀, hdiff] using evalB_var hdiffBound
  have hrowEval : (Expr.var "trialRowLen").evalB B σ₀ = some h := by
    simpa [σ₀, hrow] using evalB_var hrowBound
  have hdesiredEval : (Expr.var "trialDesiredLen").evalB B σ₀ = some d := by
    simpa [σ₀, hdesired] using evalB_var hdesiredBound
  have hdiffTest : (Cond.eq (.var "trialDiffCount") (.lit 0)).evalB B σ₀ =
      some (diff == 0) := by simp [Cond.evalB, hdiffEval, evalB_lit (by omega : 0 < B)]
  have hlenTest : (Cond.eq (.var "trialRowLen") (.var "trialDesiredLen")).evalB B σ₀ =
      some (h == d) := by simp [Cond.evalB, hrowEval, hdesiredEval]
  by_cases hd : diff = 0
  · by_cases hh : h = d
    · have ha : Run B (.assign "trialTraceEqual" (.lit 1)) σ₀
          (σ₀.setVar "trialTraceEqual" 1) 2 := by
        simpa using Run.assign (evalB_lit (by omega : 1 < B))
      have hi : (Cond.eq (.var "trialRowLen") (.var "trialDesiredLen")).evalB B σ₀ =
          some true := by rw [hlenTest]; simp [hh]
      have ri : Run B
        (.ite (.eq (.var "trialRowLen") (.var "trialDesiredLen"))
          (.assign "trialTraceEqual" (.lit 1)) (seqs [.skip, .skip]))
          σ₀ (σ₀.setVar "trialTraceEqual" 1) 6 := by
        simpa [Cond.size, Expr.size] using Run.ite_true hi ha
      have ho : (Cond.eq (.var "trialDiffCount") (.lit 0)).evalB B σ₀ =
          some true := by rw [hdiffTest]; simp [hd]
      have hr : Run B
          (.ite (.eq (.var "trialDiffCount") (.lit 0))
            (.ite (.eq (.var "trialRowLen") (.var "trialDesiredLen"))
              (.assign "trialTraceEqual" (.lit 1)) (seqs [.skip, .skip]))
            (seqs [.skip, .skip, .skip, .skip, .skip, .skip]))
          σ₀ (σ₀.setVar "trialTraceEqual" 1) 10 := by
        simpa [setTraceEqualityFlag, Cond.size, Expr.size] using Run.ite_true ho ri
      have hrun : Run B setTraceEqualityFlag σ (σ₀.setVar "trialTraceEqual" 1) 12 := by
        simpa [setTraceEqualityFlag, seqs] using rinit.seq hr
      refine ⟨σ₀.setVar "trialTraceEqual" 1, hrun, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · simp [σ₀, Env.setVar, hd, hh]
      · simp [σ₀, Env.setVar]
      · intro a; simp [σ₀, Env.setVar]
      · intro x hx; simp [σ₀, Env.setVar, hx]
    · have ha : Run B (seqs [.skip, .skip]) σ₀ σ₀ 2 := by
        simpa [seqs] using (Run.skip.seq Run.skip)
      have hi : (Cond.eq (.var "trialRowLen") (.var "trialDesiredLen")).evalB B σ₀ =
          some false := by rw [hlenTest]; simp [hh]
      have ri : Run B
          (.ite (.eq (.var "trialRowLen") (.var "trialDesiredLen"))
            (.assign "trialTraceEqual" (.lit 1)) (seqs [.skip, .skip]))
          σ₀ σ₀ 6 := by
        simpa [Cond.size, Expr.size] using Run.ite_false hi ha
      have ho : (Cond.eq (.var "trialDiffCount") (.lit 0)).evalB B σ₀ =
          some true := by rw [hdiffTest]; simp [hd]
      have hr : Run B
          (.ite (.eq (.var "trialDiffCount") (.lit 0))
            (.ite (.eq (.var "trialRowLen") (.var "trialDesiredLen"))
              (.assign "trialTraceEqual" (.lit 1)) (seqs [.skip, .skip]))
            (seqs [.skip, .skip, .skip, .skip, .skip, .skip]))
          σ₀ σ₀ 10 := by
        simpa [Cond.size, Expr.size] using Run.ite_true ho ri
      have hrun : Run B setTraceEqualityFlag σ σ₀ 12 := by
        simpa [setTraceEqualityFlag, seqs] using rinit.seq hr
      refine ⟨σ₀, hrun, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · simp [σ₀, Env.setVar, hd, hh]
      · simp [σ₀, Env.setVar]
      · intro a; simp [σ₀, Env.setVar]
      · intro x hx; simp [σ₀, Env.setVar, hx]
  · have hfalse : (Cond.eq (.var "trialDiffCount") (.lit 0)).evalB B σ₀ =
        some false := by rw [hdiffTest]; simp [hd]
    have rfalse : Run B
        (seqs [.skip, .skip, .skip, .skip, .skip, .skip]) σ₀ σ₀ 6 := by
      simp only [seqs]
      exact Run.skip.seq (Run.skip.seq (Run.skip.seq (Run.skip.seq (Run.skip.seq Run.skip))))
    have hr : Run B
        (.ite (.eq (.var "trialDiffCount") (.lit 0))
          (.ite (.eq (.var "trialRowLen") (.var "trialDesiredLen"))
          (.assign "trialTraceEqual" (.lit 1)) (seqs [.skip, .skip]))
          (seqs [.skip, .skip, .skip, .skip, .skip, .skip]))
        σ₀ σ₀ 10 := by
      simpa [Cond.size, Expr.size] using Run.ite_false hfalse rfalse
    have hrun : Run B setTraceEqualityFlag σ σ₀ 12 := by
      simpa [setTraceEqualityFlag, seqs] using rinit.seq hr
    refine ⟨σ₀, hrun, ?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp [σ₀, Env.setVar, hd]
    · simp [σ₀, Env.setVar]
    · intro a; simp [σ₀, Env.setVar]
    · intro x hx; simp [σ₀, Env.setVar, hx]

/-- Clear only the row's touched marks after its trace has been checked. -/
def trialRowClearNames : Names :=
  repairClearNames "trialRowMarks" "trialRowList" "trialRowLen"

def clearTrialRowMarks : Com :=
  renameCom trialRowClearNames (markDrawArrayWith 0)

def checkTraceRow : Com :=
  seqs [filterTraceRow, setTraceEqualityFlag]

def checkTraceRowAndClear : Com :=
  seqs [.assign "trialDiffCount" (.lit 0), filterTraceRow,
    setTraceEqualityFlag, clearTrialRowMarks]

/-- Check a collected CSR row against the fixed desired trace, set the
equality flag, and clear only that row's touched marks. -/
lemma checkTraceRow_then_clear_run
    {B n h d : ℕ} {σ : Env} {src rowMarks desiredMarks diffBuffer : ℕ → ℕ}
    {S T : Finset ℕ}
    (hn : σ.vars "n" = n)
    (hrowLen : σ.vars "trialRowLen" = h)
    (hdesiredLen : σ.vars "trialDesiredLen" = d)
    (hrowList : σ.arrs "trialRowList" = arrOf n src)
    (hrowMarks : σ.arrs "trialRowMarks" = arrOf n rowMarks)
    (hdesiredMarks : σ.arrs "trialDesiredMarks" = arrOf n desiredMarks)
    (hdiffList : σ.arrs "trialDiffList" = arrOf n diffBuffer)
    (hrow : PrefixEnumerates h src S)
    (hSrange : S ⊆ Finset.range n)
    (hrowMarks01 : ∀ v < n, rowMarks v ≤ 1)
    (hrowMarksMem : ∀ v < n, rowMarks v = 1 ↔ v ∈ S)
    (hdesiredMarks01 : ∀ v < n, desiredMarks v ≤ 1)
    (hdesiredMarksMem : ∀ v < n, desiredMarks v = 1 ↔ v ∈ T)
    (hTrange : T ⊆ Finset.range n)
    (hd : d = T.card) (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B checkTraceRowAndClear σ σ' (36 * h + 26) ∧
      (σ'.vars "trialTraceEqual" = 1 ↔ S = T) ∧
      σ'.vars "trialTraceEqual" ≤ 1 ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.vars "repairClearCursor" = h ∧
      σ'.arrs "trialRowList" = σ.arrs "trialRowList" ∧
      σ'.arrs "trialDesiredMarks" = σ.arrs "trialDesiredMarks" ∧
      σ'.arrs "sampleFlags" = σ.arrs "sampleFlags" ∧
      σ'.arrs "ord" = σ.arrs "ord" ∧
      σ'.arrs "classB" = σ.arrs "classB" ∧
      σ'.arrs "classSize" = σ.arrs "classSize" := by
  have hrowCard : h = S.card := prefixEnumerates_card h src S hrow
  have hdesiredB : d < B := by
    rw [hd]
    exact lt_of_le_of_lt (by simpa using Finset.card_le_card hTrange) hnB
  have hrowB : h < B := by
    rw [hrowCard]
    exact lt_of_le_of_lt (by simpa using Finset.card_le_card hSrange) hnB
  let σ₀ := σ.setVar "trialDiffCount" 0
  have rinit : Run B (.assign "trialDiffCount" (.lit 0)) σ σ₀ 2 := by
    simpa [σ₀] using Run.assign (evalB_lit (by omega : 0 < B))
  have hn₀ : σ₀.vars "n" = n := by simpa [σ₀, Env.setVar] using hn
  have hrowLen₀ : σ₀.vars "trialRowLen" = h := by
    simpa [σ₀, Env.setVar] using hrowLen
  have hrowList₀ : σ₀.arrs "trialRowList" = arrOf n src := by
    simpa [σ₀, Env.setVar] using hrowList
  have hdesiredMarks₀ : σ₀.arrs "trialDesiredMarks" = arrOf n desiredMarks := by
    simpa [σ₀, Env.setVar] using hdesiredMarks
  have hdiffList₀ : σ₀.arrs "trialDiffList" = arrOf n diffBuffer := by
    simpa [σ₀, Env.setVar] using hdiffList
  have hdiffCount₀ : σ₀.vars "trialDiffCount" = 0 := by
    simp [σ₀, Env.setVar]
  obtain ⟨σ₁, diffList, rfilter, _hdiffList₁, _hdiffPrefix,
    hdiffCount₁, _hcursor₁, hrowList₁, hdesiredMarks₁, hrowLen₁,
    hn₁, hdrawDomain₁, hdrawModulus₁, _hinp₁, _hout₁⟩ :=
    filterTraceRow_run hn₀ hrowLen₀ hdiffCount₀ hrowList₀ hdesiredMarks₀
      hdiffList₀ hrow hSrange hdesiredMarks01 hdesiredMarksMem hnB honeB
  have hdiffB : (S \ T).card < B := by
    exact lt_of_le_of_lt
      (by simpa using Finset.card_le_card (Finset.sdiff_subset.trans hSrange)) hnB
  have hdesiredLen₁ : σ₁.vars "trialDesiredLen" = d := by
    rw [rfilter.frame_var "trialDesiredLen" (by
      simp [filterTraceRow, trialFilterNames, appendFiltered,
        appendFilteredBody, seqs, inc, Com.wvars] <;> decide)]
    simpa [σ₀, Env.setVar] using hdesiredLen
  obtain ⟨σ₂, rflag, hflag, hflagLE, harr₂, hvars₂, _hinp₂, _hout₂⟩ :=
    setTraceEqualityFlag_run hrowLen₁ hdesiredLen₁ hdiffCount₁
      hrowB hdesiredB hdiffB honeB
  have hflagEq : σ₂.vars "trialTraceEqual" = 1 ↔ S = T := by
    rw [hflag]
    constructor
    · rintro ⟨hzero, heqLen⟩
      have hdiffSet : S \ T = ∅ := Finset.card_eq_zero.mp hzero
      have hsub : S ⊆ T := by
        intro v hv
        by_contra hnot
        have hvdiff : v ∈ S \ T := Finset.mem_sdiff.mpr ⟨hv, hnot⟩
        simpa [hdiffSet] using hvdiff
      have hcards : S.card = T.card := by
        calc S.card = h := hrowCard.symm
          _ = d := heqLen
          _ = T.card := hd
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcards])
    · intro hST
      constructor
      · simp [hST]
      · calc h = S.card := hrowCard
          _ = T.card := congrArg Finset.card hST
          _ = d := hd.symm
  have hdrawDomain₂ : σ₂.arrs "drawDomain" = σ.arrs "drawDomain" :=
    (harr₂ "drawDomain").trans hdrawDomain₁ |>.trans (by simp [σ₀])
  have hdrawModulus₂ : σ₂.vars "drawModulus" = σ.vars "drawModulus" :=
    (hvars₂ "drawModulus" (by decide)).trans hdrawModulus₁ |>.trans (by simp [σ₀, Env.setVar])
  have hn₂ : σ₂.vars "n" = n :=
    (hvars₂ "n" (by decide)).trans hn₁
  have hlen₂ : σ₂.vars "trialRowLen" = h :=
    (hvars₂ "trialRowLen" (by decide)).trans hrowLen₁
  have hmarks₂ : σ₂.arrs "trialRowMarks" = arrOf n rowMarks := by
    have hmarks₁ : σ₁.arrs "trialRowMarks" = arrOf n rowMarks := by
      rw [rfilter.frame_arr "trialRowMarks" (by
        simp [filterTraceRow, trialFilterNames, appendFiltered,
          appendFilteredBody, seqs, inc, Com.warrs] <;> decide)]
      simpa [σ₀] using hrowMarks
    exact (harr₂ "trialRowMarks").trans hmarks₁
  have hlist₂ : σ₂.arrs "trialRowList" = arrOf n src :=
    (harr₂ "trialRowList").trans hrowList₁
  obtain ⟨σ₃, rclear, hzero, hcursor, _hinp₃, _hout₃⟩ :=
    clearNeighborhoodSupport_run trialRowClearNames "trialRowMarks" "trialRowList" "trialRowLen"
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      hn₂ hlen₂ hmarks₂ hlist₂ hrow hSrange hrowMarks01 hrowMarksMem hnB
  have hrun : Run B checkTraceRowAndClear σ σ₃ (36 * h + 26) := by
    have hseq : Run B checkTraceRowAndClear σ σ₃
        (2 + (24 * h + 6 + (12 + (12 * h + 6)))) := by
      simpa [checkTraceRowAndClear, clearTrialRowMarks, trialRowClearNames,
        repairClearNames, seqs, σ₀] using rinit.seq (rfilter.seq (rflag.seq rclear))
    exact hseq.mono (by omega)
  have hflagClear : σ₃.vars "trialTraceEqual" = σ₂.vars "trialTraceEqual" :=
    rclear.frame_var "trialTraceEqual" (by decide)
  have hflagLEClear : σ₃.vars "trialTraceEqual" ≤ 1 := by
    rw [hflagClear]
    exact hflagLE
  have hdrawDomain₃ : σ₃.arrs "drawDomain" = σ.arrs "drawDomain" :=
    (rclear.frame_arr "drawDomain" (by decide)).trans hdrawDomain₂
  have hdrawModulus₃ : σ₃.vars "drawModulus" = σ.vars "drawModulus" :=
    (rclear.frame_var "drawModulus" (by decide)).trans hdrawModulus₂
  exact ⟨σ₃, hrun, hflagClear ▸ hflagEq, hflagLEClear, hdrawDomain₃, hdrawModulus₃,
    hzero, hcursor,
    hrun.frame_arr "trialRowList" (by decide),
    hrun.frame_arr "trialDesiredMarks" (by decide),
    hrun.frame_arr "sampleFlags" (by decide),
    hrun.frame_arr "ord" (by decide),
    hrun.frame_arr "classB" (by decide),
    hrun.frame_arr "classSize" (by decide)⟩

/-- Fixed names for obtaining a row directly from CSR with the fixed trial
active mask and private row scratch arrays. -/
def trialCollectNames : Names :=
  neighborhoodNames "trialActive" "trialRowMarks" "trialRowList" "trialRowLen"

def collectTrialRow : Com :=
  collectNeighborhoodAt trialCollectNames "trialVertex" "trialRowLen"

def collectCheckAndClearTrialRow : Com :=
  seqs [collectTrialRow, checkTraceRowAndClear]

/-- Actual CSR row collection followed by filtered trace comparison and
touched-entry cleanup. The local cost depends on the selected CSR row and
the collected row length, with no full-vertex clear between rows. -/
lemma collectCheckAndClearTrialRow_run
    {B n d targetCap b : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {σ : Env} {active rowMarks rowList desiredMarks diffBuffer : ℕ → ℕ}
    {T : Finset ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hvertex : σ.vars "trialVertex" = b)
    (hn : σ.vars "n" = n)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs "trialActive" = arrOf n active)
    (hrowMarks : σ.arrs "trialRowMarks" = arrOf n (fun _ => 0))
    (hrowList : σ.arrs "trialRowList" = arrOf n rowList)
    (hdesiredLen : σ.vars "trialDesiredLen" = d)
    (hdesiredMarks : σ.arrs "trialDesiredMarks" = arrOf n desiredMarks)
    (hdiffList : σ.arrs "trialDiffList" = arrOf n diffBuffer)
    (hdesiredMarks01 : ∀ v < n, desiredMarks v ≤ 1)
    (hdesiredMarksMem : ∀ v < n, desiredMarks v = 1 ↔ v ∈ T)
    (hTrange : T ⊆ Finset.range n)
    (hd : d = T.card)
    (hb : b < n)
    (hactiveB : ∀ v < n, active v < B)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' rowList', Run B collectCheckAndClearTrialRow σ σ'
        (54 * (offset x (b + 1) - offset x b) + 22 +
          36 * (activeTargets (target x) active (offset x b) (offset x (b + 1))).card + 26) ∧
      (σ'.vars "trialTraceEqual" = 1 ↔
        activeTargets (target x) active (offset x b) (offset x (b + 1)) = T) ∧
      σ'.vars "trialTraceEqual" ≤ 1 ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "drawDomain" = σ.arrs "drawDomain" ∧
      σ'.vars "drawModulus" = σ.vars "drawModulus" ∧
      σ'.arrs "trialRowList" = arrOf n rowList' ∧
      PrefixEnumerates
        (activeTargets (target x) active (offset x b) (offset x (b + 1))).card
        rowList' (activeTargets (target x) active (offset x b) (offset x (b + 1))) ∧
      (activeTargets (target x) active (offset x b) (offset x (b + 1))).card ≤
        offset x (b + 1) - offset x b ∧
      σ'.arrs "trialDesiredMarks" = σ.arrs "trialDesiredMarks" ∧
      σ'.arrs "sampleFlags" = σ.arrs "sampleFlags" ∧
      σ'.arrs "trialActive" = σ.arrs "trialActive" ∧
      σ'.arrs "ord" = σ.arrs "ord" ∧
      σ'.arrs "repB" = σ.arrs "repB" ∧
      σ'.arrs "classB" = σ.arrs "classB" ∧
      σ'.arrs "classSize" = σ.arrs "classSize" := by
  let lo := offset x b
  let hi := offset x (b + 1)
  let R := activeTargets (target x) active lo hi
  have hlohi : lo ≤ hi := hx.offset_mono b hb
  have hhiCap : hi ≤ targetCap := by
    change offset x (b + 1) ≤ targetCap
    rw [htargetCap, ← hx.offset_last]
    exact offset_mono' hx (by omega) le_rfl
  have htargetRange : ∀ j, lo ≤ j → j < hi → target x j < n := by
    intro j _ hjhi
    apply hx.target_lt j
    rw [← htargetCap]
    exact hjhi.trans_le hhiCap
  obtain ⟨σ₁, rowMarks', rowList', rcollect, hrowMarks₁, hrowList₁,
    hrowLen₁, hrow₁, hrowMem₁, hrowBound₁, _hactive₁, _htarget₁,
    _hj₁, _htoken₁, _hinp₁, _hout₁⟩ :=
    collectNeighborhoodAt_run trialCollectNames "trialVertex" "trialActive"
      "trialRowMarks" "trialRowList" "trialRowLen"
      (by decide) (by decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      (by simp [trialCollectNames, neighborhoodNames] <;> decide)
      hx htargetCap hvertex hn hoff htarget hactive hrowMarks hrowList
      hb hactiveB hn1B htargetCapB
  have hrowRange : R ⊆ Finset.range n := by
    dsimp [R, lo, hi]
    exact activeTargets_subset_range htargetRange
  have hrowMarksVals : ∀ v < n, rowMarks' v ≤ 1 := hrowBound₁
  have hrowMarksMem' : ∀ v < n, rowMarks' v = 1 ↔ v ∈ R := by
    simpa [R, lo, hi] using hrowMem₁
  have hdesiredLen₁ : σ₁.vars "trialDesiredLen" = d := by
    rw [rcollect.frame_var "trialDesiredLen" (by decide)]
    exact hdesiredLen
  have hdesiredMarks₁ : σ₁.arrs "trialDesiredMarks" = arrOf n desiredMarks := by
    rw [rcollect.frame_arr "trialDesiredMarks" (by decide)]
    exact hdesiredMarks
  have hdiffList₁ : σ₁.arrs "trialDiffList" = arrOf n diffBuffer := by
    rw [rcollect.frame_arr "trialDiffList" (by decide)]
    exact hdiffList
  have hcheckInput : σ₁.vars "n" = n := by
    rw [rcollect.frame_var "n" (by decide)]
    exact hn
  obtain ⟨σ₂, rcheck, hflag₂, hflagLE₂, _hdrawDomain₂, _hdrawModulus₂,
    hzero₂, hcursor₂, hrowList₂, _hdesired₂, _hsampleFlags₂,
    _hord₂, _hclassB₂, _hclassSize₂⟩ :=
    checkTraceRow_then_clear_run hcheckInput hrowLen₁ hdesiredLen₁
      hrowList₁ hrowMarks₁ hdesiredMarks₁ hdiffList₁
      (by simpa [R, lo, hi] using hrow₁) hrowRange hrowMarksVals
      hrowMarksMem' hdesiredMarks01 hdesiredMarksMem hTrange hd hnB honeB
  have hrun : Run B collectCheckAndClearTrialRow σ σ₂
      (54 * (offset x (b + 1) - offset x b) + 22 + 36 * R.card + 26) := by
    have hseq : Run B collectCheckAndClearTrialRow σ σ₂
        ((54 * (offset x (b + 1) - offset x b) + 22) + (36 * R.card + 26)) := by
      simpa [collectCheckAndClearTrialRow, collectTrialRow, seqs, R, lo, hi] using
        rcollect.seq rcheck
    simpa [R, lo, hi, Nat.add_assoc] using hseq
  have hdrawDomain : σ₂.arrs "drawDomain" = σ.arrs "drawDomain" :=
    (rcheck.frame_arr "drawDomain" (by decide)).trans
      (rcollect.frame_arr "drawDomain" (by decide))
  have hdrawModulus : σ₂.vars "drawModulus" = σ.vars "drawModulus" :=
    (rcheck.frame_var "drawModulus" (by decide)).trans
      (rcollect.frame_var "drawModulus" (by decide))
  have hrowListOut : σ₂.arrs "trialRowList" = arrOf n rowList' :=
    hrowList₂.trans hrowList₁
  exact ⟨σ₂, rowList', hrun, by simpa [R, lo, hi] using hflag₂,
    hflagLE₂, hzero₂, hdrawDomain, hdrawModulus, hrowListOut,
    by simpa [R, lo, hi] using hrow₁,
    by simpa [R, lo, hi] using card_activeTargets_le_interval,
    hrun.frame_arr "trialDesiredMarks" (by decide),
    hrun.frame_arr "sampleFlags" (by decide),
    hrun.frame_arr "trialActive" (by decide),
    hrun.frame_arr "ord" (by decide),
    hrun.frame_arr "repB" (by decide),
    hrun.frame_arr "classB" (by decide),
    hrun.frame_arr "classSize" (by decide)⟩

lemma clearTrialRowMarks_run
    {B n h : ℕ} {σ : Env} {src rowMarks : ℕ → ℕ} {S : Finset ℕ}
    (hn : σ.vars "n" = n)
    (hlen : σ.vars "trialRowLen" = h)
    (hlist : σ.arrs "trialRowList" = arrOf n src)
    (hmarks : σ.arrs "trialRowMarks" = arrOf n rowMarks)
    (hrow : PrefixEnumerates h src S)
    (hSrange : S ⊆ Finset.range n)
    (hmarks01 : ∀ v < n, rowMarks v ≤ 1)
    (hmarksMem : ∀ v < n, rowMarks v = 1 ↔ v ∈ S)
    (hnB : n < B) :
    ∃ σ', Run B clearTrialRowMarks σ σ' (12 * h + 6) ∧
      σ'.arrs "trialRowMarks" = arrOf n (fun _ => 0) ∧
      σ'.vars "repairClearCursor" = h ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨σ', hr, hzero, hcursor, hinp, hout⟩ :=
    clearNeighborhoodSupport_run trialRowClearNames "trialRowMarks" "trialRowList" "trialRowLen"
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      (by simp [trialRowClearNames, repairClearNames] <;> decide)
      hn hlen hmarks hlist hrow hSrange hmarks01 hmarksMem hnB
  exact ⟨σ', by simpa [clearTrialRowMarks, trialRowClearNames,
      repairClearNames] using hr, hzero, hcursor, hinp, hout⟩

end Lax457868Proofs.RepairTrialCheck
