import Mathlib.Tactic
import Lax457868Proofs.RepairDomainSource
import Lax457868Proofs.RepairFilterSource
import Lax457868Proofs.SamplePacking
import Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
import Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-! A single row of the local-repair class scan is compared against the
fixed desired trace using the existing degree-local filtered append. -/

namespace Lax457868Proofs.RepairTrialCheck

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.RepairFilterSource
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
    {B n h : ℕ} {σ : Env} {src marks : ℕ → ℕ} {S T : Finset ℕ}
    (hn : σ.vars "n" = n)
    (hlen : σ.vars "trialRowLen" = h)
    (hcount : σ.vars "trialDiffCount" = 0)
    (hsrc : σ.arrs "trialRowList" = arrOf n src)
    (hmarks : σ.arrs "trialDesiredMarks" = arrOf n marks)
    (hdomain : σ.arrs "trialDiffList" = arrOf n (fun _ => 0))
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
  have hdomainτ : τ.arrs "drawDomain" = arrOf n (fun _ => 0) := by
    change σ.arrs (ρ.array "drawDomain") = arrOf n (fun _ => 0)
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
      (by simpa [hcountτ] using (prefixEnumerates_zero (fun _ => 0)))
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

/-- A duplicate-free row prefix has cardinality equal to its runtime length.
-/
lemma prefixCard_eq {n h : ℕ} {src : ℕ → ℕ} {S : Finset ℕ}
    (hrow : PrefixEnumerates h src S) : h = S.card := by
  have hset : (Stack.toList h src).toFinset = S := by
    ext v
    simp [List.mem_toFinset, hrow.2 v]
  have hcard : (Stack.toList h src).length = S.card := by
    rw [← hset, List.toFinset_card_of_nodup hrow.1]
  simpa [Stack.toList] using hcard

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
      refine ⟨σ₀.setVar "trialTraceEqual" 1, hrun, ?_, ?_, ?_, rfl, rfl⟩
      · simp [σ₀, Env.setVar, hd, hh]
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
      refine ⟨σ₀, hrun, ?_, ?_, ?_, rfl, rfl⟩
      · simp [σ₀, Env.setVar, hd, hh]
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
    refine ⟨σ₀, hrun, ?_, ?_, ?_, rfl, rfl⟩
    · simp [σ₀, Env.setVar, hd]
    · intro a; simp [σ₀, Env.setVar]
    · intro x hx; simp [σ₀, Env.setVar, hx]

/-- Clear only the row's touched marks after its trace has been checked. -/
def trialRowClearNames : Names :=
  repairClearNames "trialRowMarks" "trialRowList" "trialRowLen"

def clearTrialRowMarks : Com :=
  renameCom trialRowClearNames (markDrawArrayWith 0)

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
