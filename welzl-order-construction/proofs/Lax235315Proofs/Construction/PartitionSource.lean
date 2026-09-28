import Lax235315Proofs.Construction.CollisionDetection
import Lax235315Proofs.Construction.MarkingMath
import Lax235315Proofs.Construction.ReadKeys
import Mathlib.Tactic

/-! Source-level verification of the trace-partition routines. -/

namespace Lax235315Proofs.Construction.PartitionSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlStraight

lemma scanList_length_eq_activeVertices_card (active : ℕ → ℕ) (n : ℕ) :
    (scanList active 0 n).length = (activeVertices n active).card := by
  induction n with
  | zero => simp [scanList, activeVertices]
  | succ n ih =>
      rw [scanList_zero_add]
      by_cases hn : active n = 1
      · rw [activeVertices, Finset.range_add_one,
          Finset.filter_insert]
        simp [hn, ih, activeVertices]
      · rw [activeVertices, Finset.range_add_one,
          Finset.filter_insert]
        simp [hn, ih, activeVertices]

/-- The concrete one-class initialization has the exact compact size table
needed by every subsequent refinement. -/
lemma initPartition_classSizes_and_occupancy
    {n : ℕ} {active cls size : ℕ → ℕ}
    (hfill : ∀ v < n, active v = 1 → cls v = 0)
    (hsize : size 0 = (scanList active 0 n).length)
    (hnonempty : (activeVertices n active).Nonempty) :
    ClassSizes n 1 active cls size ∧
      LabelsOccupyPrefix 1 cls (activeVertices n active) := by
  have hlabels : ∀ v < n, active v = 1 → cls v < 1 := by
    intro v hv ha
    rw [hfill v hv ha]
    omega
  have hfiber : classMultiplicity cls (activeVertices n active) 0 =
      (activeVertices n active).card := by
    unfold classMultiplicity
    congr 1
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact hfill v (mem_activeVertices.mp hv).1 (mem_activeVertices.mp hv).2
  constructor
  · refine ⟨hlabels, ?_⟩
    intro q hq
    have hq0 : q = 0 := by omega
    subst q
    rw [hsize, scanList_length_eq_activeVertices_card, hfiber]
  · intro q hq
    have hq0 : q = 0 := by omega
    subst q
    rw [hfiber]
    exact Finset.card_pos.mpr hnonempty

def InitPartitionInv (n : ℕ) (active : ℕ → ℕ)
    (activeName clsName : String) (τ : Env) : Prop :=
  ∃ cls : ℕ → ℕ,
    τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧
    τ.vars "vcount" = (scanList active 0 (τ.vars "v")).length ∧
    τ.arrs activeName = arrOf n active ∧
    τ.arrs clsName = arrOf n cls ∧
    ∀ i < τ.vars "v", active i = 1 → cls i = 0

private lemma initPartition_body_spec {B n : ℕ} {active : ℕ → ℕ}
    {activeName clsName : String}
    (hactiveCls : activeName ≠ clsName)
    (hactiveB : ∀ i < n, active i < B)
    (hnB : n < B) (honeB : 1 < B) :
    Spec B
      (fun τ => InitPartitionInv n active activeName clsName τ ∧
        τ.vars "v" < n)
      (seqs [
        .ite (.eq (.get activeName (.var "v")) (.lit 1))
          (seqs [.store clsName (.var "v") (.lit 0), inc "vcount"])
          .skip,
        inc "v"])
      (fun τ τ' => InitPartitionInv n active activeName clsName τ' ∧
        τ'.vars "v" = τ.vars "v" + 1)
      20 := by
  intro τ hτ
  rcases hτ with ⟨⟨cls, hvle, hn, hvcount, hactive, hcls, hfill⟩, hvn⟩
  have hvB : τ.vars "v" < B := hvn.trans hnB
  have hactiveGet : (τ.arrs activeName)[τ.vars "v"]? =
      some (active (τ.vars "v")) := by
    rw [hactive, getElem?_arrOf active hvn]
  have hactiveEval : (Expr.get activeName (.var "v")).evalB B τ =
      some (active (τ.vars "v")) :=
    evalB_get (evalB_var hvB) hactiveGet (hactiveB _ hvn)
  let test := Cond.eq (.get activeName (.var "v")) (.lit 1)
  by_cases hav : active (τ.vars "v") = 1
  · have htest : test.evalB B τ = some true := by
      simpa [test, hav] using evalB_condEq hactiveEval (evalB_lit honeB)
    let τ₁ := τ.setArr clsName (τ.vars "v") 0
    have rstore : Run B (.store clsName (.var "v") (.lit 0)) τ τ₁ 3 := by
      exact Run.store (evalB_var hvB) (evalB_lit (by omega)) (by
        rw [hcls, length_arrOf]
        exact hvn)
    have hvcountLe : τ.vars "vcount" ≤ τ.vars "v" := by
      rw [hvcount]
      exact scanList_length_le active 0 _
    have hvcountB : τ.vars "vcount" < B := hvcountLe.trans_lt hvB
    let τ₂ := τ₁.setVar "vcount" (τ.vars "vcount" + 1)
    have rcount : Run B (inc "vcount") τ₁ τ₂ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [τ₁] using evalB_var hvcountB)
        (evalB_lit honeB) (by simp; omega)
    let τ₃ := τ₂.setVar "v" (τ.vars "v" + 1)
    have rv : Run B (inc "v") τ₂ τ₃ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [τ₂, τ₁] using evalB_var hvB)
        (evalB_lit honeB) (by simp; omega)
    have rbranch : Run B
        (seqs [.store clsName (.var "v") (.lit 0), inc "vcount"])
        τ τ₂ 7 := by
      simpa [seqs] using rstore.seq rcount
    refine ⟨τ₃, (Run.seq (Run.ite_true htest rbranch) rv).mono (by
      norm_num [test, Cond.size, Expr.size]), ?_, by simp [τ₃]⟩
    refine ⟨upd cls (τ.vars "v") 0, by simp [τ₃]; omega,
      by simp [τ₃, τ₂, τ₁, hn], ?_, ?_, ?_, ?_⟩
    · change τ.vars "vcount" + 1 =
        (scanList active 0 (τ.vars "v" + 1)).length
      rw [scanList_zero_add, if_pos hav, hvcount]
      simp
    · simp [τ₃, τ₂, τ₁, hactive, hactiveCls]
    · simp [τ₃, τ₂, τ₁, hcls, set_arrOf_eq_upd]
    · intro i hi hai
      by_cases hiv : i = τ.vars "v"
      · subst i
        simp [upd]
      · simp [upd, hiv]
        have hiold : i < τ.vars "v" := by
          change i < τ.vars "v" + 1 at hi
          omega
        exact hfill i hiold hai
  · have htest : test.evalB B τ = some false := by
      simpa [test, hav] using evalB_condEq hactiveEval (evalB_lit honeB)
    let τ₁ := τ.setVar "v" (τ.vars "v" + 1)
    have rv : Run B (inc "v") τ τ₁ 4 := by
      apply Run.assign
      exact evalB_bin (evalB_var hvB) (evalB_lit honeB) (by simp; omega)
    refine ⟨τ₁, (Run.seq (Run.ite_false htest Run.skip) rv).mono (by
      norm_num [test, Cond.size, Expr.size]), ?_, by simp [τ₁]⟩
    refine ⟨cls, by simp [τ₁]; omega, by simp [τ₁, hn], ?_,
      by simp [τ₁, hactive], by simp [τ₁, hcls], ?_⟩
    · change τ.vars "vcount" =
        (scanList active 0 (τ.vars "v" + 1)).length
      rw [scanList_zero_add, if_neg hav, List.append_nil, hvcount]
    · intro i hi hai
      by_cases hiv : i = τ.vars "v"
      · subst i
        exact (hav hai).elim
      · have hiold : i < τ.vars "v" := by
          change i < τ.vars "v" + 1 at hi
          omega
        exact hfill i hiold hai

/-- `initPartition` creates the one-class partition of the active side and
zeros the scratch arrays used by refinement. -/
lemma initPartition_run {B n : ℕ} {active cls : ℕ → ℕ}
    {activeName clsName : String} {σ : Env}
    (hactive : σ.arrs activeName = arrOf n active)
    (hcls : σ.arrs clsName = arrOf n cls)
    (hclassSize : ∃ f, σ.arrs "classSize" = arrOf n f)
    (hmarkedCount : ∃ f, σ.arrs "markedCount" = arrOf n f)
    (hstamp : ∃ f, σ.arrs "stamp" = arrOf n f)
    (hn : σ.vars "n" = n)
    (hnpos : 0 < n) (hnB : n < B) (honeB : 1 < B)
    (hactiveB : ∀ i < n, active i < B)
    (hactiveCls : activeName ≠ clsName)
    (hactiveSize : activeName ≠ "classSize")
    (hactiveMarked : activeName ≠ "markedCount")
    (hactiveStamp : activeName ≠ "stamp")
    (hclsSize : clsName ≠ "classSize")
    (hclsMarked : clsName ≠ "markedCount")
    (hclsStamp : clsName ≠ "stamp") :
    ∃ σ' cls' size' marked' stamp',
      Run B (initPartition activeName clsName) σ σ' (60 * (n + 1)) ∧
      σ'.vars "n" = n ∧
      σ'.vars "vcount" = (scanList active 0 n).length ∧
      σ'.vars "classCount" = 1 ∧
      σ'.arrs activeName = arrOf n active ∧
      σ'.arrs clsName = arrOf n cls' ∧
      σ'.arrs "classSize" = arrOf n size' ∧
      σ'.arrs "markedCount" = arrOf n marked' ∧
      σ'.arrs "stamp" = arrOf n stamp' ∧
      (∀ i < n, active i = 1 → cls' i = 0) ∧
      size' 0 = (scanList active 0 n).length ∧
      (∀ i < n, marked' i = 0) ∧
      ∀ i < n, stamp' i = 0 := by
  rcases hclassSize with ⟨size, hsize⟩
  rcases hmarkedCount with ⟨marked, hmarked⟩
  rcases hstamp with ⟨stamp, hstamp⟩
  obtain ⟨σ₁, size₁, rsize, hsize₁, hzsize⟩ :=
    clearArray_run hsize hn (by decide) hnB
  have hmarked₁ : σ₁.arrs "markedCount" = arrOf n marked := by
    rw [rsize.frame_arr "markedCount" (by decide), hmarked]
  obtain ⟨σ₂, marked₂, rmarked, hmarked₂, hzmarked⟩ :=
    clearArray_run hmarked₁ (by rw [rsize.frame_var "n" (by decide), hn])
      (by decide) hnB
  have hstamp₂ : σ₂.arrs "stamp" = arrOf n stamp := by
    rw [rmarked.frame_arr "stamp" (by decide),
      rsize.frame_arr "stamp" (by decide), hstamp]
  obtain ⟨σ₃, stamp₃, rstamp, hstamp₃, hzstamp⟩ :=
    clearArray_run hstamp₂ (by
      rw [rmarked.frame_var "n" (by decide), rsize.frame_var "n" (by decide), hn])
      (by decide) hnB
  let σ₄ := (σ₃.setVar "v" 0).setVar "vcount" 0
  have rv0 : Run B (.assign "v" (.lit 0)) σ₃ (σ₃.setVar "v" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have rc0 : Run B (.assign "vcount" (.lit 0)) (σ₃.setVar "v" 0) σ₄ 2 :=
    Run.assign (evalB_lit (by omega))
  have hactive₃ : σ₃.arrs activeName = arrOf n active := by
    rw [rstamp.frame_arr activeName (by
        simp [clearArray, seqs, inc, Com.warrs, hactiveStamp]),
      rmarked.frame_arr activeName (by
        simp [clearArray, seqs, inc, Com.warrs, hactiveMarked]),
      rsize.frame_arr activeName (by
        simp [clearArray, seqs, inc, Com.warrs, hactiveSize]), hactive]
  have hcls₃ : σ₃.arrs clsName = arrOf n cls := by
    rw [rstamp.frame_arr clsName (by
        simp [clearArray, seqs, inc, Com.warrs, hclsStamp]),
      rmarked.frame_arr clsName (by
        simp [clearArray, seqs, inc, Com.warrs, hclsMarked]),
      rsize.frame_arr clsName (by
        simp [clearArray, seqs, inc, Com.warrs, hclsSize]), hcls]
  have hn₃ : σ₃.vars "n" = n := by
    rw [rstamp.frame_var "n" (by decide), rmarked.frame_var "n" (by decide),
      rsize.frame_var "n" (by decide), hn]
  have hinit : InitPartitionInv n active activeName clsName σ₄ := by
    exact ⟨cls, by simp [σ₄], by simp [σ₄, hn₃], by simp [σ₄, scanList],
      by simp [σ₄, hactive₃], by simp [σ₄, hcls₃], by
        intro i hi hai
        simp [σ₄] at hi⟩
  obtain ⟨σ₅, rloop, hI₅, hvn⟩ :=
    (Spec.forRange "v" "n" (InitPartitionInv n active activeName clsName)
      n 20 (24 * n + 4)
      (fun _ h => by rcases h with ⟨_, hv, -⟩; exact hv.trans_lt hnB)
      (fun _ h => by rcases h with ⟨_, -, hn', -⟩; simpa [hn'] using hnB)
      (fun _ h => by rcases h with ⟨_, -, hn', -⟩; exact hn')
      (fun _ h => by rcases h with ⟨_, hv, -⟩; exact hv)
      (initPartition_body_spec hactiveCls hactiveB hnB honeB)
      (fun _ h => h)
      (fun τ h => by
        rcases h with ⟨_, hv, -⟩
        have := Nat.sub_le n (τ.vars "v")
        omega)).run hinit
  rcases hI₅ with ⟨cls₅, -, hn₅, hvcount₅, hactive₅, hcls₅, hfill₅⟩
  have hvcountn : σ₅.vars "vcount" = (scanList active 0 n).length := by
    simpa [hvn] using hvcount₅
  have hfilln : ∀ i < n, active i = 1 → cls₅ i = 0 := by
    simpa [hvn] using hfill₅
  have hsize₅ : σ₅.arrs "classSize" = arrOf n size₁ := by
    rw [rloop.frame_arr "classSize" (by
      simp [Com.warrs, seqs, inc, Ne.symm hclsSize]),
      rc0.frame_arr "classSize" (by decide), rv0.frame_arr "classSize" (by decide),
      rstamp.frame_arr "classSize" (by decide),
      rmarked.frame_arr "classSize" (by decide), hsize₁]
  let size₆ := upd size₁ 0 (scanList active 0 n).length
  let σ₆ := σ₅.setArr "classSize" 0 (scanList active 0 n).length
  have rstore : Run B (.store "classSize" (.lit 0) (.var "vcount")) σ₅ σ₆ 3 := by
    apply Run.store (evalB_lit (by omega))
    · rw [evalB_var_iff]
      refine ⟨hvcountn.symm, ?_⟩
      rw [hvcountn]
      exact (scanList_length_le active 0 n).trans_lt hnB
    · rw [hsize₅, length_arrOf]
      exact hnpos
  let σ₇ := σ₆.setVar "classCount" 1
  have rclass : Run B (.assign "classCount" (.lit 1)) σ₆ σ₇ 2 :=
    Run.assign (evalB_lit honeB)
  refine ⟨σ₇, cls₅, size₆, marked₂, stamp₃, ?_, ?_⟩
  · have rr := rsize.seq (rmarked.seq (rstamp.seq
      (rv0.seq (rc0.seq (rloop.seq (rstore.seq rclass))))))
    simpa [initPartition, seqs] using rr.mono (by omega)
  · have hmarked₅ : σ₅.arrs "markedCount" = arrOf n marked₂ := by
      rw [rloop.frame_arr "markedCount" (by
          simp [Com.warrs, seqs, inc, Ne.symm hclsMarked]),
        rc0.frame_arr "markedCount" (by decide),
        rv0.frame_arr "markedCount" (by decide),
        rstamp.frame_arr "markedCount" (by decide), hmarked₂]
    have hstamp₅ : σ₅.arrs "stamp" = arrOf n stamp₃ := by
      rw [rloop.frame_arr "stamp" (by
          simp [Com.warrs, seqs, inc, Ne.symm hclsStamp]),
        rc0.frame_arr "stamp" (by decide),
        rv0.frame_arr "stamp" (by decide), hstamp₃]
    refine ⟨by simp [σ₇, σ₆, hn₅], by simp [σ₇, σ₆, hvcountn],
      by simp [σ₇], by simp [σ₇, σ₆, hactive₅, hactiveSize],
      by simp [σ₇, σ₆, hcls₅, hclsSize], ?_, ?_, ?_, hfilln, ?_, hzmarked, hzstamp⟩
    · simp [σ₇, σ₆, hsize₅, size₆, set_arrOf_eq_upd]
    · simp [σ₇, σ₆, hmarked₅]
    · simp [σ₇, σ₆, hstamp₅]
    · simp [size₆, upd]

end Lax235315Proofs.Construction.PartitionSource
