import Lax235315Proofs.Construction.RepresentativeMath
import Lax235315Proofs.Construction.PartitionLoopSource
import Mathlib.Tactic

/-! Source-level verification of the representative-selection scan. -/

namespace Lax235315Proofs.Construction.RepresentativeSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RepresentativeMath
open Lax235315Proofs.Construction.WelzlProgram

/-- The first representative scan appearing literally in `partition`. -/
def representativeSelectBody (activeName clsName repsName activeOutName
    outCountName : String) : Com :=
  seqs [
    .ite (.eq (.get activeName (.var "v")) (.lit 1))
      (seqs [
        .assign "cl" (.get clsName (.var "v")),
        .ite (.eq (.get "repClass" (.var "cl")) (.var "n"))
          (seqs [
            .store "repClass" (.var "cl") (.var "v"),
            .store repsName (.var outCountName) (.var "v"),
            .store activeOutName (.var "v") (.lit 1),
            inc outCountName])
          .skip])
      .skip,
    inc "v"]

def RepSelectInv (n current : ℕ)
    (activeName clsName repsName activeOutName outCountName : String)
    (active label : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ repClass reps outActive : ℕ → ℕ, ∃ R : Finset ℕ,
    τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧
    τ.vars "classCount" = current ∧ current ≤ n ∧
    τ.vars outCountName = R.card ∧
    τ.arrs activeName = arrOf n active ∧
    τ.arrs clsName = arrOf n label ∧
    τ.arrs "repClass" = arrOf n repClass ∧
    τ.arrs repsName = arrOf n reps ∧
    τ.arrs activeOutName = arrOf n outActive ∧
    RepData n current (τ.vars "v") active label
      repClass reps outActive R

private lemma representativeSelectBody_spec
    {B n current : ℕ} {active label : ℕ → ℕ}
    {activeName clsName repsName activeOutName outCountName : String}
    (hnB : n < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hlabels : ∀ v < n, active v = 1 → label v < current)
    (hactiveCls : activeName ≠ clsName)
    (haRepClass : activeName ≠ "repClass")
    (haReps : activeName ≠ repsName) (haOut : activeName ≠ activeOutName)
    (hcRepClass : clsName ≠ "repClass")
    (hcReps : clsName ≠ repsName) (hcOut : clsName ≠ activeOutName)
    (hrepClassReps : "repClass" ≠ repsName)
    (hrepClassOut : "repClass" ≠ activeOutName)
    (hrepOut : repsName ≠ activeOutName)
    (hcountV : outCountName ≠ "v") (hcountCl : outCountName ≠ "cl")
    (hcountN : outCountName ≠ "n")
    (hcountClass : outCountName ≠ "classCount") :
    Spec B
      (fun τ => RepSelectInv n current activeName clsName repsName
          activeOutName outCountName active label τ ∧ τ.vars "v" < n)
      (representativeSelectBody activeName clsName repsName activeOutName
        outCountName)
      (fun τ τ' => RepSelectInv n current activeName clsName repsName
          activeOutName outCountName active label τ' ∧
        τ'.vars "v" = τ.vars "v" + 1)
      300 := by
  intro τ hτ
  rcases hτ with ⟨hI, hvn⟩
  rcases hI with ⟨repClass, reps, outActive, R, hvle, hn, hcurrent,
    hcurrentN, houtCount, hactive, hlabel, hrepClass, hreps, hout, hdata⟩
  have hvB : τ.vars "v" < B := hvn.trans hnB
  have hactiveEval : (Expr.get activeName (.var "v")).evalB B τ =
      some (active (τ.vars "v")) := by
    apply evalB_get (evalB_var hvB)
    · rw [hactive, getElem?_arrOf active hvn]
    · exact hactiveB _ hvn
  let activeTest := Cond.eq (.get activeName (.var "v")) (.lit 1)
  by_cases hav : active (τ.vars "v") = 1
  · have hactiveTest : activeTest.evalB B τ = some true := by
      simpa [activeTest, hav] using evalB_condEq hactiveEval (evalB_lit honeB)
    let q := label (τ.vars "v")
    have hqCurrent : q < current := hlabels _ hvn hav
    have hqN : q < n := hqCurrent.trans_le hcurrentN
    have hqB : q < B := hqN.trans hnB
    have hlabelEval : (Expr.get clsName (.var "v")).evalB B τ = some q := by
      apply evalB_get (evalB_var hvB)
      · rw [hlabel, getElem?_arrOf label hvn]
      · exact hqB
    let τ₁ := τ.setVar "cl" q
    have rcl : Run B (.assign "cl" (.get clsName (.var "v"))) τ τ₁ 6 :=
      (Run.assign hlabelEval).mono (by norm_num [Expr.size])
    have hrepLe : repClass q ≤ n := hdata.table_le q hqCurrent
    have hrepB : repClass q < B := hrepLe.trans_lt hnB
    have hrepEval : (Expr.get "repClass" (.var "cl")).evalB B τ₁ =
        some (repClass q) := by
      apply evalB_get
      · exact evalB_var (by simp [τ₁]; exact hqB)
      · simp [τ₁, hrepClass, getElem?_arrOf repClass hqN]
      · exact hrepB
    have hnEval : (Expr.var "n").evalB B τ₁ = some n := by
      rw [evalB_var_iff]
      simp [τ₁, hn, hnB]
    let repTest := Cond.eq (.get "repClass" (.var "cl")) (.var "n")
    by_cases hfresh : repClass q = n
    · have hrepTest : repTest.evalB B τ₁ = some true := by
        simpa [repTest, hfresh] using evalB_condEq hrepEval hnEval
      have hcardLe : R.card ≤ τ.vars "v" := by
        calc
          R.card ≤ (activeVertices (τ.vars "v") active).card :=
            Finset.card_le_card hdata.reps_processed
          _ ≤ τ.vars "v" := activeVertices_card_le _ _
      have hcardN : R.card < n := hcardLe.trans_lt hvn
      have hcardB : R.card < B := hcardN.trans hnB
      let τ₂ := τ₁.setArr "repClass" q (τ.vars "v")
      have rrepClass : Run B
          (.store "repClass" (.var "cl") (.var "v")) τ₁ τ₂ 3 := by
        exact Run.store (evalB_var (by simp [τ₁]; exact hqB))
          (evalB_var (by simp [τ₁]; exact hvB)) (by
            simp [τ₁, hrepClass, length_arrOf, hqN])
      let τ₃ := τ₂.setArr repsName R.card (τ.vars "v")
      have rreps : Run B
          (.store repsName (.var outCountName) (.var "v")) τ₂ τ₃ 3 := by
        apply Run.store
        · rw [evalB_var_iff]
          simp [τ₂, τ₁, hcountCl, Ne.symm hcountCl, hcountV,
            Ne.symm hcountV, houtCount, hcardB]
        · exact evalB_var (by simp [τ₂, τ₁]; exact hvB)
        · simp [τ₂, τ₁, hreps, hrepClassReps, Ne.symm hrepClassReps,
            length_arrOf, hcardN]
      let τ₄ := τ₃.setArr activeOutName (τ.vars "v") 1
      have rout : Run B
          (.store activeOutName (.var "v") (.lit 1)) τ₃ τ₄ 3 := by
        exact Run.store (evalB_var (by simp [τ₃, τ₂, τ₁]; exact hvB))
          (evalB_lit honeB) (by
            simp [τ₃, τ₂, τ₁, hout, hrepClassOut, Ne.symm hrepClassOut,
              hrepOut, Ne.symm hrepOut, length_arrOf, hvn])
      let τ₅ := τ₄.setVar outCountName (R.card + 1)
      have rcount : Run B (inc outCountName) τ₄ τ₅ 4 := by
        apply Run.assign
        have hcountEval : (Expr.var outCountName).evalB B τ₄ = some R.card := by
          rw [evalB_var_iff]
          simp [τ₄, τ₃, τ₂, τ₁, hcountCl, Ne.symm hcountCl,
            hcountV, Ne.symm hcountV, houtCount, hcardB]
        exact evalB_bin hcountEval (evalB_lit honeB)
          (lt_of_le_of_lt ((Nat.succ_le_iff).mpr hcardN) hnB)
      let τ₆ := τ₅.setVar "v" (τ.vars "v" + 1)
      have rv : Run B (inc "v") τ₅ τ₆ 4 := by
        apply Run.assign
        exact evalB_bin (by rw [evalB_var_iff]; simp [τ₅, τ₄, τ₃, τ₂, τ₁,
          hcountV, Ne.symm hcountV, hvB]) (evalB_lit honeB)
          (lt_of_le_of_lt ((Nat.succ_le_iff).mpr hvn) hnB)
      have rbranch : Run B
          (seqs [
            .store "repClass" (.var "cl") (.var "v"),
            .store repsName (.var outCountName) (.var "v"),
            .store activeOutName (.var "v") (.lit 1),
            inc outCountName]) τ₁ τ₅ 13 := by
        simpa [seqs] using rrepClass.seq (rreps.seq (rout.seq rcount))
      have hrun : Run B
          (representativeSelectBody activeName clsName repsName activeOutName
            outCountName) τ τ₆ 300 := by
        exact ((Run.ite_true hactiveTest
          (rcl.seq (Run.ite_true hrepTest rbranch))).seq rv).mono (by
            norm_num [representativeSelectBody, activeTest, repTest, seqs,
              Cond.size, Expr.size])
      let repClass' := upd repClass q (τ.vars "v")
      let reps' := upd reps R.card (τ.vars "v")
      let outActive' := upd outActive (τ.vars "v") 1
      have hdata' : RepData n current (τ.vars "v" + 1) active label
          repClass' reps' outActive' (insert (τ.vars "v") R) := by
        exact hdata.fresh hvn hav rfl hqCurrent hfresh
      refine ⟨τ₆, hrun, ?_, by simp [τ₆, τ₅, hcountV, Ne.symm hcountV]⟩
      refine ⟨repClass', reps', outActive', insert (τ.vars "v") R,
        by simp [τ₆]; omega, ?_, ?_, hcurrentN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hn, hcountN, Ne.symm hcountN]
      · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hcurrent, hcountClass,
          Ne.symm hcountClass]
      · simp [τ₆, τ₅, hcountV, Ne.symm hcountV,
          Finset.card_insert_of_notMem (by
          intro hvR
          exact ((hdata.table_empty q hqCurrent).mp hfresh _ hvR rfl))]
      · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hactive, hcountV,
          Ne.symm hcountV, haRepClass, Ne.symm haRepClass,
          haReps, Ne.symm haReps, haOut, Ne.symm haOut]
      · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hlabel, hcountV,
          Ne.symm hcountV, hcRepClass, Ne.symm hcRepClass,
          hcReps, Ne.symm hcReps, hcOut, Ne.symm hcOut]
      · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hrepClass, repClass',
          set_arrOf_eq_upd, hcountV, Ne.symm hcountV,
          hrepClassReps, Ne.symm hrepClassReps,
          hrepClassOut, Ne.symm hrepClassOut]
      · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hreps, reps',
          set_arrOf_eq_upd, hrepClassReps, Ne.symm hrepClassReps,
          hrepOut, Ne.symm hrepOut, hcountV, Ne.symm hcountV]
      · simp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hout, outActive',
          set_arrOf_eq_upd, hrepClassOut, Ne.symm hrepClassOut,
          hrepOut, Ne.symm hrepOut, hcountV, Ne.symm hcountV]
      · simpa [τ₆] using hdata'
    · have hrepTest : repTest.evalB B τ₁ = some false := by
        simpa [repTest, hfresh] using evalB_condEq hrepEval hnEval
      let τ₂ := τ₁.setVar "v" (τ.vars "v" + 1)
      have rv : Run B (inc "v") τ₁ τ₂ 4 := by
        apply Run.assign
        exact evalB_bin (by simpa [τ₁] using evalB_var hvB)
          (evalB_lit honeB)
          (lt_of_le_of_lt ((Nat.succ_le_iff).mpr hvn) hnB)
      have hrun : Run B
          (representativeSelectBody activeName clsName repsName activeOutName
            outCountName) τ τ₂ 300 := by
        exact ((Run.ite_true hactiveTest
          (rcl.seq (Run.ite_false hrepTest Run.skip))).seq rv).mono (by
            norm_num [representativeSelectBody, activeTest, repTest, seqs,
              Cond.size, Expr.size])
      have hdata' := hdata.existing hvn hav rfl hqCurrent hfresh
      refine ⟨τ₂, hrun, ?_, by simp [τ₂, τ₁]⟩
      refine ⟨repClass, reps, outActive, R, by simp [τ₂, τ₁]; omega,
        by simp [τ₂, τ₁, hn], by simp [τ₂, τ₁, hcurrent], hcurrentN,
        by simp [τ₂, τ₁, houtCount, hcountV, hcountCl],
        by simp [τ₂, τ₁, hactive], by simp [τ₂, τ₁, hlabel],
        by simp [τ₂, τ₁, hrepClass], by simp [τ₂, τ₁, hreps],
        by simp [τ₂, τ₁, hout], by simpa [τ₂] using hdata'⟩
  · have hactiveTest : activeTest.evalB B τ = some false := by
      simpa [activeTest, hav] using evalB_condEq hactiveEval (evalB_lit honeB)
    let τ₁ := τ.setVar "v" (τ.vars "v" + 1)
    have rv : Run B (inc "v") τ τ₁ 4 := by
      apply Run.assign
      exact evalB_bin (evalB_var hvB) (evalB_lit honeB)
        (lt_of_le_of_lt ((Nat.succ_le_iff).mpr hvn) hnB)
    have hrun : Run B
        (representativeSelectBody activeName clsName repsName activeOutName
          outCountName) τ τ₁ 300 := by
      exact ((Run.ite_false hactiveTest Run.skip).seq rv).mono (by
        norm_num [representativeSelectBody, activeTest, seqs, Cond.size, Expr.size])
    have hdata' := hdata.inactive hav
    refine ⟨τ₁, hrun, ?_, by simp [τ₁]⟩
    exact ⟨repClass, reps, outActive, R, by simp [τ₁]; omega,
      by simp [τ₁, hn], by simp [τ₁, hcurrent], hcurrentN,
      by simp [τ₁, houtCount, hcountV], by simp [τ₁, hactive],
      by simp [τ₁, hlabel], by simp [τ₁, hrepClass], by simp [τ₁, hreps],
      by simp [τ₁, hout], by simpa [τ₁] using hdata'⟩

/-- The complete increasing scan selects exactly one active representative of
each occupied class. -/
lemma representativeSelectLoop_run
    {B n current : ℕ} {active label : ℕ → ℕ}
    {activeName clsName repsName activeOutName outCountName : String}
    {σ : Env}
    (hI : RepSelectInv n current activeName clsName repsName activeOutName
      outCountName active label σ)
    (hnB : n < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hlabels : ∀ v < n, active v = 1 → label v < current)
    (hactiveCls : activeName ≠ clsName)
    (haRepClass : activeName ≠ "repClass")
    (haReps : activeName ≠ repsName) (haOut : activeName ≠ activeOutName)
    (hcRepClass : clsName ≠ "repClass")
    (hcReps : clsName ≠ repsName) (hcOut : clsName ≠ activeOutName)
    (hrepClassReps : "repClass" ≠ repsName)
    (hrepClassOut : "repClass" ≠ activeOutName)
    (hrepOut : repsName ≠ activeOutName)
    (hcountV : outCountName ≠ "v") (hcountCl : outCountName ≠ "cl")
    (hcountN : outCountName ≠ "n")
    (hcountClass : outCountName ≠ "classCount") :
    ∃ σ' repClass reps outActive R,
      Run B (.while (.lt (.var "v") (.var "n"))
        (representativeSelectBody activeName clsName repsName activeOutName
          outCountName)) σ σ' (304 * n + 4) ∧
      σ'.vars "v" = n ∧ σ'.vars outCountName = R.card ∧
      σ'.arrs "repClass" = arrOf n repClass ∧
      σ'.arrs repsName = arrOf n reps ∧
      σ'.arrs activeOutName = arrOf n outActive ∧
      RepData n current n active label repClass reps outActive R := by
  let I := RepSelectInv n current activeName clsName repsName activeOutName
    outCountName active label
  have hbody := representativeSelectBody_spec hnB honeB hactiveB hlabels
    hactiveCls haRepClass haReps haOut hcRepClass hcReps hcOut
    hrepClassReps hrepClassOut hrepOut hcountV hcountCl hcountN hcountClass
  have hvB : ∀ τ, I τ → τ.vars "v" < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, hv, -⟩
    exact hv.trans_lt hnB
  have hnBound : ∀ τ, I τ → τ.vars "n" < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, hn, -⟩
    rw [hn]
    exact hnB
  have hnEq : ∀ τ, I τ → τ.vars "n" = n := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, _, hn, -⟩
    exact hn
  have hvLe : ∀ τ, I τ → τ.vars "v" ≤ n := by
    intro τ hτ
    rcases hτ with ⟨_, _, _, _, hv, -⟩
    exact hv
  obtain ⟨σ', r, hI', hv⟩ :=
    (Spec.forRange "v" "n" I n 300 (304 * n + 4)
      hvB hnBound hnEq hvLe hbody (fun _ h => h)
      (fun τ _ => Nat.add_le_add_right
        (Nat.mul_le_mul_left 304 (Nat.sub_le n (τ.vars "v"))) 4)).run hI
  rcases hI' with ⟨repClass, reps, outActive, R, -, hn, -, -, houtCount,
    -, -, hrepClass, hreps, hout, hdata⟩
  exact ⟨σ', repClass, reps, outActive, R, r, hv, houtCount,
    hrepClass, hreps, hout, by simpa [hv] using hdata⟩

/-- The second representative scan appearing literally in `partition`. -/
def representativeMapBody (activeName clsName repOfName : String) : Com :=
  seqs [
    .ite (.eq (.get activeName (.var "v")) (.lit 1))
      (seqs [
        .assign "cl" (.get clsName (.var "v")),
        .store repOfName (.var "v") (.get "repClass" (.var "cl"))])
      .skip,
    inc "v"]

def RepMapInv (n current : ℕ)
    (activeName clsName repOfName : String)
    (active label repClass : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ repOf : ℕ → ℕ,
    τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧
    current ≤ n ∧
    τ.arrs activeName = arrOf n active ∧
    τ.arrs clsName = arrOf n label ∧
    τ.arrs "repClass" = arrOf n repClass ∧
    τ.arrs repOfName = arrOf n repOf ∧
    (∀ v < n, active v = 1 → label v < current) ∧
    ∀ v < τ.vars "v", active v = 1 →
      repOf v = repClass (label v)

private lemma representativeMapBody_spec
    {B n current : ℕ} {active label repClass : ℕ → ℕ}
    {activeName clsName repOfName : String}
    (hnB : n < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hrepRange : ∀ v < n, active v = 1 → repClass (label v) < n)
    (hactiveCls : activeName ≠ clsName)
    (haRepClass : activeName ≠ "repClass")
    (haRepOf : activeName ≠ repOfName)
    (hcRepClass : clsName ≠ "repClass")
    (hcRepOf : clsName ≠ repOfName)
    (hrepClassRepOf : "repClass" ≠ repOfName) :
    Spec B
      (fun τ => RepMapInv n current activeName clsName repOfName
          active label repClass τ ∧ τ.vars "v" < n)
      (representativeMapBody activeName clsName repOfName)
      (fun τ τ' => RepMapInv n current activeName clsName repOfName
          active label repClass τ' ∧ τ'.vars "v" = τ.vars "v" + 1)
      100 := by
  intro τ hτ
  rcases hτ with ⟨⟨repOf, hvle, hn, hcurrentN, hactive, hlabel, hrepClass, hrepOf,
    hlabels, hfilled⟩, hvn⟩
  have hvB : τ.vars "v" < B := hvn.trans hnB
  have hactiveEval : (Expr.get activeName (.var "v")).evalB B τ =
      some (active (τ.vars "v")) := by
    apply evalB_get (evalB_var hvB)
    · rw [hactive, getElem?_arrOf active hvn]
    · exact hactiveB _ hvn
  let activeTest := Cond.eq (.get activeName (.var "v")) (.lit 1)
  by_cases hav : active (τ.vars "v") = 1
  · have htest : activeTest.evalB B τ = some true := by
      simpa [activeTest, hav] using evalB_condEq hactiveEval (evalB_lit honeB)
    let q := label (τ.vars "v")
    have hqCurrent : q < current := hlabels _ hvn hav
    have hqN : q < n := hqCurrent.trans_le hcurrentN
    have hqB : q < B := hqN.trans hnB
    have hlabelEval : (Expr.get clsName (.var "v")).evalB B τ = some q := by
      apply evalB_get (evalB_var hvB)
      · rw [hlabel, getElem?_arrOf label hvn]
      · exact hqB
    let τ₁ := τ.setVar "cl" q
    have rcl : Run B (.assign "cl" (.get clsName (.var "v"))) τ τ₁ 6 :=
      (Run.assign hlabelEval).mono (by norm_num [Expr.size])
    have hrepN : repClass q < n := hrepRange _ hvn hav
    have hrepB : repClass q < B := hrepN.trans hnB
    have hrepEval : (Expr.get "repClass" (.var "cl")).evalB B τ₁ =
        some (repClass q) := by
      apply evalB_get
      · exact evalB_var (by simp [τ₁]; exact hqB)
      · simp [τ₁, hrepClass, getElem?_arrOf repClass hqN]
      · exact hrepB
    let repOf' := upd repOf (τ.vars "v") (repClass q)
    let τ₂ := τ₁.setArr repOfName (τ.vars "v") (repClass q)
    have rstore : Run B
        (.store repOfName (.var "v") (.get "repClass" (.var "cl")))
        τ₁ τ₂ 8 := by
      exact (Run.store (evalB_var (by simp [τ₁]; exact hvB)) hrepEval (by
        simp [τ₁, hrepOf, length_arrOf, hvn])).mono (by norm_num [Expr.size])
    let τ₃ := τ₂.setVar "v" (τ.vars "v" + 1)
    have rv : Run B (inc "v") τ₂ τ₃ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [τ₂, τ₁] using evalB_var hvB)
        (evalB_lit honeB) (lt_of_le_of_lt ((Nat.succ_le_iff).mpr hvn) hnB)
    have hrun : Run B
        (representativeMapBody activeName clsName repOfName) τ τ₃ 100 := by
      exact ((Run.ite_true htest (rcl.seq rstore)).seq rv).mono (by
        norm_num [representativeMapBody, activeTest, seqs, Cond.size, Expr.size])
    refine ⟨τ₃, hrun, ?_, by simp [τ₃, τ₂]⟩
    refine ⟨repOf', by simp [τ₃]; omega, by simp [τ₃, τ₂, τ₁, hn],
      hcurrentN, ?_, ?_, ?_, ?_, hlabels, ?_⟩
    · simp [τ₃, τ₂, τ₁, hactive, haRepOf, Ne.symm haRepOf]
    · simp [τ₃, τ₂, τ₁, hlabel, hcRepOf, Ne.symm hcRepOf]
    · simp [τ₃, τ₂, τ₁, hrepClass, hrepClassRepOf,
        Ne.symm hrepClassRepOf]
    · simp [τ₃, τ₂, τ₁, hrepOf, repOf', set_arrOf_eq_upd]
    · intro u hu hua
      by_cases huv : u = τ.vars "v"
      · subst u
        simp [repOf', upd, q]
      · have huold : u < τ.vars "v" := by
          simp [τ₃, τ₂] at hu
          omega
        simp [repOf', upd, huv, hfilled u huold hua]
  · have htest : activeTest.evalB B τ = some false := by
      simpa [activeTest, hav] using evalB_condEq hactiveEval (evalB_lit honeB)
    let τ₁ := τ.setVar "v" (τ.vars "v" + 1)
    have rv : Run B (inc "v") τ τ₁ 4 := by
      apply Run.assign
      exact evalB_bin (evalB_var hvB) (evalB_lit honeB)
        (lt_of_le_of_lt ((Nat.succ_le_iff).mpr hvn) hnB)
    have hrun : Run B
        (representativeMapBody activeName clsName repOfName) τ τ₁ 100 := by
      exact ((Run.ite_false htest Run.skip).seq rv).mono (by
        norm_num [representativeMapBody, activeTest, seqs, Cond.size, Expr.size])
    refine ⟨τ₁, hrun, ?_, by simp [τ₁]⟩
    refine ⟨repOf, by simp [τ₁]; omega, by simp [τ₁, hn], hcurrentN,
      by simp [τ₁, hactive], by simp [τ₁, hlabel], by simp [τ₁, hrepClass],
      by simp [τ₁, hrepOf], hlabels, ?_⟩
    intro u hu hua
    by_cases huv : u = τ.vars "v"
    · subst u
      exact (hav hua).elim
    · exact hfilled u (by simp [τ₁] at hu; omega) hua

lemma representativeMapLoop_run
    {B n current : ℕ} {active label repClass : ℕ → ℕ}
    {activeName clsName repOfName : String} {σ : Env}
    (hI : RepMapInv n current activeName clsName repOfName
      active label repClass σ)
    (hnB : n < B) (honeB : 1 < B)
    (hactiveB : ∀ v < n, active v < B)
    (hrepRange : ∀ v < n, active v = 1 → repClass (label v) < n)
    (hactiveCls : activeName ≠ clsName)
    (haRepClass : activeName ≠ "repClass")
    (haRepOf : activeName ≠ repOfName)
    (hcRepClass : clsName ≠ "repClass")
    (hcRepOf : clsName ≠ repOfName)
    (hrepClassRepOf : "repClass" ≠ repOfName) :
    ∃ σ' repOf,
      Run B (.while (.lt (.var "v") (.var "n"))
        (representativeMapBody activeName clsName repOfName))
        σ σ' (104 * n + 4) ∧
      σ'.vars "v" = n ∧ σ'.arrs repOfName = arrOf n repOf ∧
      ∀ v < n, active v = 1 → repOf v = repClass (label v) := by
  let I := RepMapInv n current activeName clsName repOfName
    active label repClass
  have hbody := representativeMapBody_spec (current := current)
    hnB honeB hactiveB hrepRange
    hactiveCls haRepClass haRepOf hcRepClass hcRepOf hrepClassRepOf
  have hvB : ∀ τ, I τ → τ.vars "v" < B := by
    intro τ hτ
    rcases hτ with ⟨_, hv, -⟩
    exact hv.trans_lt hnB
  have hnBound : ∀ τ, I τ → τ.vars "n" < B := by
    intro τ hτ
    rcases hτ with ⟨_, _, hn, -⟩
    rw [hn]
    exact hnB
  have hnEq : ∀ τ, I τ → τ.vars "n" = n := by
    intro τ hτ
    rcases hτ with ⟨_, _, hn, -⟩
    exact hn
  have hvLe : ∀ τ, I τ → τ.vars "v" ≤ n := by
    intro τ hτ
    rcases hτ with ⟨_, hv, -⟩
    exact hv
  obtain ⟨σ', r, hI', hv⟩ :=
    (Spec.forRange "v" "n" I n 100 (104 * n + 4)
      hvB hnBound hnEq hvLe hbody (fun _ h => h)
      (fun τ _ => Nat.add_le_add_right
        (Nat.mul_le_mul_left 104 (Nat.sub_le n (τ.vars "v"))) 4)).run hI
  rcases hI' with ⟨repOf, -, -, -, -, -, -, hrepOf, -, hfilled⟩
  exact ⟨σ', repOf, r, hv, hrepOf, by simpa [hv] using hfilled⟩

end Lax235315Proofs.Construction.RepresentativeSource
