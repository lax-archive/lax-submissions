import Mathlib.Tactic
import Lax457868Proofs.FullSamplePartition

/-! Materialize the mathematical prefix starts of grouped active-B classes
in a runtime array, then use a representative's class label to read its
slice bounds back from the source arrays. -/

namespace Lax457868Proofs.RepairClassOffsets

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.GroupedClassRepresentatives
open Lax457868Proofs.ClassBucketDomain

/-- One offset-scan iteration stores the current total, adds the next class
size, and advances the cursor. -/
private def offsetBody : Com :=
  seqs [
    .store "repairClassStart" (.var "repairClassCursor")
      (.var "repairClassTotal"),
    .assign "repairClassTmp" (.get "classSize" (.var "repairClassCursor")),
    .assign "repairClassTotal"
      (.add (.var "repairClassTotal") (.var "repairClassTmp")),
    inc "repairClassCursor"]

/-- Scan the runtime class-size prefix and write its exclusive prefix sums to
repairClassStart. -/
def repairClassOffsets : Com :=
  seqs [
    .assign "repairClassTotal" (.lit 0),
    .assign "repairClassCursor" (.lit 0),
    .while (.lt (.var "repairClassCursor") (.var "classCount")) offsetBody]

/-- The materialized starts agree with the mathematical prefix sum below the
cursor, while every unvisited slot still has its input value. -/
private def OffsetInv (n q : ℕ) (size oldStart : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "classCount" = q ∧
  σ.vars "repairClassCursor" ≤ q ∧
  σ.vars "repairClassTotal" = classStart size (σ.vars "repairClassCursor") ∧
  σ.arrs "classSize" = arrOf n size ∧
  σ.arrs "repairClassStart" = arrOf n
    (fun d => if d < σ.vars "repairClassCursor" then classStart size d
      else oldStart d)

/-- One body iteration preserves the exact prefix-sum invariant. -/
private lemma offsetBody_spec {B n q : ℕ} {size oldStart : ℕ → ℕ}
    (hqle : q ≤ n) (htotal : classStart size q ≤ n)
    (hnB : n < B) :
    Spec B
      (fun τ => OffsetInv n q size oldStart τ ∧
        τ.vars "repairClassCursor" < q)
      offsetBody
      (fun τ τ' => OffsetInv n q size oldStart τ' ∧
        τ'.vars "repairClassCursor" = τ.vars "repairClassCursor" + 1)
      14 := by
  intro τ hτ
  rcases hτ with ⟨⟨hcount, hcursorLe, htotalNow, hsizes, hstarts⟩, hcursorLt⟩
  let c := τ.vars "repairClassCursor"
  have hcq : c < q := by simpa [c] using hcursorLt
  have hcn : c < n := hcq.trans_le hqle
  have hcB : c < B := hcn.trans hnB
  have hnextLe : c + 1 ≤ q := by omega
  have hstartLe : classStart size (c + 1) ≤ n :=
    (classStart_mono size hnextLe).trans htotal
  have hsum : classStart size c + size c = classStart size (c + 1) := by
    simp [classStart]
  have hsumLe : classStart size c + size c ≤ n := by
    rw [hsum]
    exact hstartLe
  have htotalB : τ.vars "repairClassTotal" < B := by
    rw [htotalNow]
    exact (classStart_mono size hcursorLe).trans_lt (htotal.trans_lt hnB)
  have hsizeB : size c < B := by omega
  have hcursorEval : (Expr.var "repairClassCursor").evalB B τ = some c := by
    simpa [c] using evalB_var hcB
  have htotalEval : (Expr.var "repairClassTotal").evalB B τ =
      some (τ.vars "repairClassTotal") := evalB_var htotalB
  have hstore : Run B
      (.store "repairClassStart" (.var "repairClassCursor")
        (.var "repairClassTotal"))
      τ (τ.setArr "repairClassStart" c (τ.vars "repairClassTotal")) 3 := by
    apply Run.store hcursorEval htotalEval
    rw [hstarts, length_arrOf]
    exact hcn
  let τ₁ := τ.setArr "repairClassStart" c (τ.vars "repairClassTotal")
  have htmpEval :
      (Expr.get "classSize" (.var "repairClassCursor")).evalB B τ₁ = some (size c) := by
    have hframe : τ₁.arrs "classSize" = τ.arrs "classSize" := by
      simp [τ₁, arrs_setArr]
    have hcursor₁ : τ₁.vars "repairClassCursor" = c := by simp [τ₁, c]
    have hc₁B : τ₁.vars "repairClassCursor" < B := by
      rw [hcursor₁]
      exact hcB
    have hc₁n : τ₁.vars "repairClassCursor" < n := by
      rw [hcursor₁]
      exact hcn
    apply evalB_get (evalB_var hc₁B) ?_ hsizeB
    rw [hframe, hsizes, getElem?_arrOf size hc₁n]
    simp [hcursor₁]
  have htmpRun : Run B
      (.assign "repairClassTmp" (.get "classSize" (.var "repairClassCursor")))
      τ₁ (τ₁.setVar "repairClassTmp" (size c)) 3 := by
    exact Run.assign htmpEval
  let τ₂ := τ₁.setVar "repairClassTmp" (size c)
  have haddEval :
      (Expr.add (.var "repairClassTotal") (.var "repairClassTmp")).evalB B τ₂ =
        some (classStart size (c + 1)) := by
    have htotal₂ : τ₂.vars "repairClassTotal" = classStart size c := by
      simp [τ₂, τ₁, htotalNow, c]
    have htmp₂ : τ₂.vars "repairClassTmp" = size c := by simp [τ₂]
    have hstartB : classStart size c < B := by
      exact (classStart_mono size hcursorLe).trans_lt (htotal.trans_lt hnB)
    have haddB : classStart size c + size c < B := by
      rw [hsum]
      exact hstartLe.trans_lt hnB
    have htotal₂B : τ₂.vars "repairClassTotal" < B := by
      rw [htotal₂]
      exact hstartB
    have htmp₂B : τ₂.vars "repairClassTmp" < B := by
      rw [htmp₂]
      exact hsizeB
    have hadd₂B : Bop.add.apply (τ₂.vars "repairClassTotal")
        (τ₂.vars "repairClassTmp") < B := by
      simpa [htotal₂, htmp₂, Bop.apply] using haddB
    have hbin := evalB_bin (op := .add)
      (evalB_var htotal₂B)
      (evalB_var htmp₂B)
      hadd₂B
    simpa [Expr.add, Bop.apply, htotal₂, htmp₂, hsum] using hbin
  let τ₃ := τ₂.setVar "repairClassTotal" (classStart size (c + 1))
  have htotalRun : Run B
      (.assign "repairClassTotal"
        (.add (.var "repairClassTotal") (.var "repairClassTmp")))
      τ₂ τ₃ 4 := by
    exact Run.assign haddEval
  have hincEval :
      (Expr.add (.var "repairClassCursor") (.lit 1)).evalB B τ₃ = some (c + 1) := by
    have hcPlusB : c + 1 < B := by omega
    have hc₃B : τ₃.vars "repairClassCursor" < B := by
      simp [τ₃, τ₂, τ₁, c]
      exact hcB
    have hc₃ : τ₃.vars "repairClassCursor" = c := by
      simp [τ₃, τ₂, τ₁, c]
    have hcPlus₃B : Bop.add.apply (τ₃.vars "repairClassCursor") 1 < B := by
      simpa [hc₃, Bop.apply] using hcPlusB
    have hbin := evalB_bin (op := .add)
      (evalB_var hc₃B)
      (evalB_lit (by omega : 1 < B))
      hcPlus₃B
    simpa [Expr.add, Bop.apply, hc₃] using hbin
  let τ₄ := τ₃.setVar "repairClassCursor" (c + 1)
  have hincRun : Run B (inc "repairClassCursor") τ₃ τ₄ 4 := by
    simpa [inc, τ₄] using Run.assign hincEval
  have hrun : Run B offsetBody τ τ₄ 14 := by
    have h := hstore.seq (htmpRun.seq (htotalRun.seq hincRun))
    simpa [offsetBody, seqs, τ₁, τ₂, τ₃, τ₄] using h
  have hstartsNext :
      τ₄.arrs "repairClassStart" = arrOf n
        (fun d => if d < c + 1 then classStart size d else oldStart d) := by
    rw [show τ₄.arrs "repairClassStart" =
      (τ.setArr "repairClassStart" c (τ.vars "repairClassTotal")).arrs
        "repairClassStart" by simp [τ₄, τ₃, τ₂, τ₁]]
    rw [arrs_setArr, if_pos rfl, hstarts, set_arrOf_eq_upd]
    rw [htotalNow]
    simp only [c]
    apply arrOf_congr
    intro d hd
    by_cases hdc : d = c
    · subst d
      simp [upd, c]
    · have hlt : d < c + 1 ↔ d < c := by omega
      simp [upd, hdc, hlt, c]
  have hclassSizeFrame : τ₄.arrs "classSize" = arrOf n size := by
    rw [hincRun.frame_arr "classSize" (by decide),
      htotalRun.frame_arr "classSize" (by decide),
      htmpRun.frame_arr "classSize" (by decide),
      hstore.frame_arr "classSize" (by decide)]
    exact hsizes
  have hclassCountFrame : τ₄.vars "classCount" = q := by
    rw [hincRun.frame_var "classCount" (by decide),
      htotalRun.frame_var "classCount" (by decide),
      htmpRun.frame_var "classCount" (by decide),
      hstore.frame_var "classCount" (by decide)]
    exact hcount
  refine ⟨τ₄, hrun.mono (by omega), ⟨hclassCountFrame, ?_, ?_, hclassSizeFrame, hstartsNext⟩,
    ?_⟩
  · simpa [τ₄, c] using hnextLe
  · simp [τ₄, τ₃]
  · simp [τ₄, c]

/-- The runtime offset pass writes each class start into the matching prefix
slot, leaves the old table tail intact, and preserves the class-size input.
Its running time is linear in the class count. -/
lemma repairClassOffsets_run {B n q : ℕ} {σ : Env}
    {size oldStart : ℕ → ℕ}
    (hclassCount : σ.vars "classCount" = q)
    (hsizes : σ.arrs "classSize" = arrOf n size)
    (hstarts : σ.arrs "repairClassStart" = arrOf n oldStart)
    (hqle : q ≤ n) (htotal : classStart size q ≤ n) (hnB : n < B) :
    ∃ σ', Run B repairClassOffsets σ σ' (18 * q + 8) ∧
      σ'.arrs "repairClassStart" =
        arrOf n (fun d => if d < q then classStart size d else oldStart d) ∧
      (∀ d < q, classStart size d ≤ n) ∧
      σ'.vars "repairClassCursor" = q ∧
      σ'.vars "repairClassTotal" = classStart size q ∧
      σ'.arrs "classSize" = arrOf n size ∧
      (∀ a, a ≠ "repairClassStart" → σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "repairClassCursor" → v ≠ "repairClassTotal" →
        v ≠ "repairClassTmp" → σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let σ₀ := σ.setVar "repairClassTotal" 0
  have htotalInit : Run B (.assign "repairClassTotal" (.lit 0)) σ σ₀ 2 := by
    apply Run.assign
    exact evalB_lit (by omega)
  let I := OffsetInv n q size oldStart
  have hbody : Spec B
      (fun τ => I τ ∧ τ.vars "repairClassCursor" < q)
      offsetBody
      (fun τ τ' => I τ' ∧
        τ'.vars "repairClassCursor" = τ.vars "repairClassCursor" + 1)
      14 :=
    offsetBody_spec hqle htotal hnB
  have hloop := Spec.forRangeZero (B := B) "repairClassCursor" "classCount"
      I q 14 (lt_of_le_of_lt hqle hnB)
      (fun _ h => h.2.1)
      (fun _ h => h.1)
      hbody
  have hinit : I (σ₀.setVar "repairClassCursor" 0) := by
    refine ⟨hclassCount, by simp, ?_, hsizes, ?_⟩
    · simp [σ₀, classStart]
    · simp [σ₀, hstarts]
  obtain ⟨σ', hloopRun, hfinal, hcursor⟩ :=
    hloop.run (σ := σ₀) hinit
  have hrun : Run B repairClassOffsets σ σ' (18 * q + 8) := by
    have h := htotalInit.seq hloopRun
    have hcost : 2 + (18 * q + 6) = 18 * q + 8 := by omega
    simpa [repairClassOffsets, seqs, σ₀, hcost] using h
  rcases hfinal with ⟨hclassCount', hcursorLe, htotalFinal, hsizes', hstarts'⟩
  have hstartsExact : σ'.arrs "repairClassStart" =
      arrOf n (fun d => if d < q then classStart size d else oldStart d) := by
    simpa [hcursor] using hstarts'
  have hclassStartBound : ∀ d < q, classStart size d ≤ n := by
    intro d hd
    exact (classStart_mono size (Nat.le_of_lt hd)).trans htotal
  have hframeArrs : ∀ a, a ≠ "repairClassStart" →
      σ'.arrs a = σ.arrs a := by
    intro a ha
    exact hrun.frame_arr a (by
      simp [repairClassOffsets, offsetBody, seqs, inc, Com.warrs, ha])
  have hframeVars : ∀ v, v ≠ "repairClassCursor" →
      v ≠ "repairClassTotal" → v ≠ "repairClassTmp" →
      σ'.vars v = σ.vars v := by
    intro v hcursor' htotal' htmp'
    exact hrun.frame_var v (by
      simp [repairClassOffsets, offsetBody, seqs, inc, Com.wvars,
        hcursor', htotal', htmp'])
  have hinp := hrun.frame_inp (by
    simp [repairClassOffsets, offsetBody, seqs, inc, Com.reads])
  have hout := hrun.out_eq (by
    simp [repairClassOffsets, offsetBody, seqs, inc, Com.NoWrite])
  refine ⟨σ', hrun, hstartsExact, hclassStartBound, hcursor, ?_, hsizes',
    hframeArrs, hframeVars, hinp, hout⟩
  simpa [hcursor] using htotalFinal

/-- Read the selected representative's class, then load that class's start
and stop from the materialized prefix arrays. -/
def repairClassLookup : Com :=
  seqs [
    .assign "repairClass" (.get "classB" (.var "repairB")),
    .assign "repairStart" (.get "repairClassStart" (.var "repairClass")),
    .assign "repairStop"
      (.add (.var "repairStart") (.get "classSize" (.var "repairClass")))]

/-- Execute the three fixed source lookups. The final interval is exactly the
class slice supplied by the grouped-source invariant. -/
lemma repairClassLookup_run {B n q : ℕ} {σ : Env}
    {size starts label ord active : ℕ → ℕ} {xs : List ℕ} {rep : ℕ}
    (hn : σ.vars "n" = n)
    (hq : σ.vars "classCount" = q)
    (hrep : σ.vars "repairB" = rep)
    (hclassB : σ.arrs "classB" = arrOf n label)
    (hsizes : σ.arrs "classSize" = arrOf n size)
    (hstarts : σ.arrs "repairClassStart" = arrOf n starts)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hrepRange : rep < n)
    (hqle : q ≤ n)
    (hlabel : label rep < q)
    (hstartTable : ∀ d < q, starts d = classStart size d)
    (hclassEnd : ∀ d < q, classStart size d + size d ≤ xs.length)
    (hxsCard : xs.length = (activeVertices n active).card)
    (hactiveCard : (activeVertices n active).card ≤ n)
    (hslices : ∀ d < q, PrefixEnumerates (size d)
      (fun i => ord (classStart size d + i))
      (labelClass xs label d))
    (hnB : n < B) :
    ∃ σ', Run B repairClassLookup σ σ' 11 ∧
      σ'.vars "repairClass" = label rep ∧
      σ'.vars "repairStart" = classStart size (label rep) ∧
      σ'.vars "repairStop" =
        classStart size (label rep) + size (label rep) ∧
      σ'.vars "repairStop" ≤ xs.length ∧
      σ'.vars "repairStop" ≤ (activeVertices n active).card ∧
      (activeVertices n active).card ≤ n ∧
      PrefixEnumerates
        (σ'.vars "repairStop" - σ'.vars "repairStart")
        (fun i => ord (σ'.vars "repairStart" + i))
        (labelClass xs label (label rep)) ∧
      σ'.arrs "classB" = σ.arrs "classB" ∧
      σ'.arrs "classSize" = σ.arrs "classSize" ∧
      σ'.arrs "repairClassStart" = σ.arrs "repairClassStart" ∧
      σ'.arrs "ord" = σ.arrs "ord" ∧
      σ'.arrs "ord" = arrOf n ord ∧
      σ'.arrs "repB" = σ.arrs "repB" ∧
      σ'.arrs "sampleFlags" = σ.arrs "sampleFlags" ∧
      (∀ v, v ≠ "repairClass" → v ≠ "repairStart" →
        v ≠ "repairStop" → σ'.vars v = σ.vars v) ∧
      σ'.vars "n" = n ∧
      σ'.vars "classCount" = q ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let d := label rep
  have hdq : d < q := by simpa [d] using hlabel
  have hrepB : rep < B := hrepRange.trans hnB
  have hdN : d < n := hdq.trans_le hqle
  have hdB : d < B := hdN.trans hnB
  have hxsN : xs.length ≤ n := by
    rw [hxsCard]
    exact hactiveCard
  have hstartLe : classStart size d ≤ xs.length := by
    have := hclassEnd d hdq
    omega
  have hstopLe : classStart size d + size d ≤ xs.length := hclassEnd d hdq
  have hstartB : classStart size d < B :=
    lt_of_le_of_lt (hstartLe.trans hxsN) hnB
  have hstopB : classStart size d + size d < B :=
    lt_of_le_of_lt (hstopLe.trans hxsN) hnB
  have hrepInputB : σ.vars "repairB" < B := by
    rw [hrep]
    exact hrepB
  have hclassEval :
      (Expr.get "classB" (.var "repairB")).evalB B σ = some d := by
    apply evalB_get (evalB_var hrepInputB) ?_ (by omega)
    rw [hclassB, hrep, getElem?_arrOf label hrepRange]
  let σ₁ := σ.setVar "repairClass" d
  have hstartEval :
      (Expr.get "repairClassStart" (.var "repairClass")).evalB B σ₁ =
        some (classStart size d) := by
    have hd₁B : σ₁.vars "repairClass" < B := by
      simp [σ₁]
      exact hdB
    have hd₁N : σ₁.vars "repairClass" < n := by
      simp [σ₁]
      exact hdN
    apply evalB_get
      (evalB_var hd₁B) ?_ hstartB
    rw [show σ₁.arrs "repairClassStart" = σ.arrs "repairClassStart" by simp [σ₁],
      hstarts, getElem?_arrOf starts hd₁N]
    simpa [σ₁, d] using congrArg some (hstartTable d hdq)
  let σ₂ := σ₁.setVar "repairStart" (classStart size d)
  have hsizeEval :
      (Expr.get "classSize" (.var "repairClass")).evalB B σ₂ = some (size d) := by
    have hd₂B : σ₂.vars "repairClass" < B := by
      simp [σ₂, σ₁]
      exact hdB
    have hd₂N : σ₂.vars "repairClass" < n := by
      simp [σ₂, σ₁]
      exact hdN
    apply evalB_get
      (evalB_var hd₂B) ?_ (by omega)
    rw [show σ₂.arrs "classSize" = σ.arrs "classSize" by simp [σ₂, σ₁],
      hsizes, getElem?_arrOf size hd₂N]
    simp [σ₂, σ₁]
  have htotalEval :
      (Expr.var "repairStart").evalB B σ₂ = some (classStart size d) := by
    have hstart₂B : σ₂.vars "repairStart" < B := by
      simp [σ₂, σ₁]
      exact hstartB
    simpa [σ₂, σ₁] using evalB_var hstart₂B
  have hstopEval :
      (Expr.add (.var "repairStart")
        (.get "classSize" (.var "repairClass"))).evalB B σ₂ =
        some (classStart size d + size d) := by
    have hbin := evalB_bin (op := .add) htotalEval hsizeEval hstopB
    simpa [Expr.add, Bop.apply] using hbin
  let σ₃ := σ₂.setVar "repairStop" (classStart size d + size d)
  have hclassRun : Run B
      (.assign "repairClass" (.get "classB" (.var "repairB")))
      σ σ₁ 3 := by
    simpa [σ₁] using Run.assign hclassEval
  have hstartRun : Run B
      (.assign "repairStart" (.get "repairClassStart" (.var "repairClass")))
      σ₁ σ₂ 3 := by
    simpa [σ₂, Expr.size] using Run.assign hstartEval
  have hstopRun : Run B
      (.assign "repairStop"
        (.add (.var "repairStart")
          (.get "classSize" (.var "repairClass"))))
      σ₂ σ₃ 5 := by
    simpa [σ₃, Expr.size] using Run.assign hstopEval
  have hrun : Run B repairClassLookup σ σ₃ 11 := by
    have h := hclassRun.seq (hstartRun.seq hstopRun)
    simpa [repairClassLookup, seqs, σ₁, σ₂, σ₃] using h
  have hslice : PrefixEnumerates (size d)
      (fun i => ord (classStart size d + i)) (labelClass xs label d) :=
    hslices d hdq
  have hstopStart : σ₃.vars "repairStop" - σ₃.vars "repairStart" = size d := by
    simp [σ₃, σ₂, σ₁]
  have hprefix : PrefixEnumerates
      (σ₃.vars "repairStop" - σ₃.vars "repairStart")
      (fun i => ord (σ₃.vars "repairStart" + i))
      (labelClass xs label d) := by
    simpa [σ₃, σ₂, σ₁, hstopStart] using hslice
  have hframeVars : ∀ v, v ≠ "repairClass" → v ≠ "repairStart" →
      v ≠ "repairStop" → σ₃.vars v = σ.vars v := by
    intro v hc hs ht
    exact hrun.frame_var v (by
      simp [repairClassLookup, seqs, Com.wvars, hc, hs, ht])
  have hinp := hrun.frame_inp (by
    simp [repairClassLookup, seqs, Com.reads])
  have hout := hrun.out_eq (by
    simp [repairClassLookup, seqs, Com.NoWrite])
  refine ⟨σ₃, hrun, ?_, ?_, ?_, ?_, ?_, hactiveCard, hprefix,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hframeVars, ?_, ?_,
    hinp, hout⟩
  · simp [σ₃, σ₂, σ₁, d]
  · simp [σ₃, σ₂, σ₁, d]
  · simp [σ₃, σ₂, σ₁, d]
  · simpa [σ₃, d] using hstopLe
  · simpa [σ₃, d, hxsCard] using hstopLe
  · exact hrun.frame_arr "classB" (by
      simp [repairClassLookup, seqs, Com.warrs])
  · exact hrun.frame_arr "classSize" (by
      simp [repairClassLookup, seqs, Com.warrs])
  · exact hrun.frame_arr "repairClassStart" (by
      simp [repairClassLookup, seqs, Com.warrs])
  · exact hrun.frame_arr "ord" (by
      simp [repairClassLookup, seqs, Com.warrs])
  · rw [hrun.frame_arr "ord" (by
      simp [repairClassLookup, seqs, Com.warrs]), hord]
  · exact hrun.frame_arr "repB" (by
      simp [repairClassLookup, seqs, Com.warrs])
  · exact hrun.frame_arr "sampleFlags" (by
      simp [repairClassLookup, seqs, Com.warrs])
  · rw [hframeVars "n" (by decide) (by decide) (by decide)]
    exact hn
  · rw [hframeVars "classCount" (by decide) (by decide) (by decide)]
    exact hq
