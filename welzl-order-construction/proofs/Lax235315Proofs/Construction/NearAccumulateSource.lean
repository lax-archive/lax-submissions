import Lax235315Proofs.Construction.NearCollectSource
import Lax235315Proofs.Construction.RefineSplitMath
import Mathlib.Tactic

/-! Source-level verification of the counter-accumulation loop in the
batched near-twin check. -/

namespace Lax235315Proofs.Construction.NearAccumulateSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RefineSplitMath
open Lax235315Proofs.Construction.WelzlProgram

/-- Increment a base function once on every member of `P`. -/
def addOn (P : Finset ℕ) (base : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v ∈ P then base v + 1 else base v

/-- Increment a base function on processed vertices whose representative is
also in the current neighborhood. -/
def addCommon (P M : Finset ℕ) (rep base : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v ∈ P ∧ rep v ∈ M then base v + 1 else base v

@[simp] lemma addOn_empty (base : ℕ → ℕ) : addOn ∅ base = base := by
  funext v
  simp [addOn]

@[simp] lemma addCommon_empty (M : Finset ℕ) (rep base : ℕ → ℕ) :
    addCommon ∅ M rep base = base := by
  funext v
  simp [addCommon]

lemma upd_addOn {P : Finset ℕ} {base : ℕ → ℕ} {q : ℕ}
    (hq : q ∉ P) :
    upd (addOn P base) q (addOn P base q + 1) =
      addOn (insert q P) base := by
  funext v
  by_cases hvq : v = q
  · subst v
    simp [upd, addOn, hq]
  · simp [upd, addOn, hvq]

lemma upd_addCommon {P M : Finset ℕ} {rep base : ℕ → ℕ} {q : ℕ}
    (hq : q ∉ P) (hr : rep q ∈ M) :
    upd (addCommon P M rep base) q (addCommon P M rep base q + 1) =
      addCommon (insert q P) M rep base := by
  funext v
  by_cases hvq : v = q
  · subst v
    simp [upd, addCommon, hq, hr]
  · simp [upd, addCommon, hvq]

lemma addCommon_insert_of_rep_notMem
    {P M : Finset ℕ} {rep base : ℕ → ℕ} {q : ℕ}
    (hr : rep q ∉ M) :
    addCommon (insert q P) M rep base = addCommon P M rep base := by
  funext v
  by_cases hvq : v = q
  · subst v
    simp [addCommon, hr]
  · simp [addCommon, hvq]

/-- After `i` iterations, precisely the processed neighbor prefix has
contributed one to the degree and common-neighbor counters. -/
def AccumulateInv (n height token : ℕ) (entry rep baseDegree baseInter : ℕ → ℕ)
    (M : Finset ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ height ∧ height ≤ n ∧ τ.vars "n" = n ∧
  τ.vars "neighborLen" = height ∧ τ.vars "token" = token ∧
  τ.arrs "neighbors" = arrOf n entry ∧
  τ.arrs "repB" = arrOf n rep ∧
  (∃ stamp, τ.arrs "stamp" = arrOf n stamp ∧
    (∀ v < n, stamp v = token ↔ v ∈ M) ∧
    ∀ v < n, stamp v < n + 1) ∧
  τ.arrs "degree" = arrOf n
    (addOn (processedClasses (τ.vars "i") entry) baseDegree) ∧
  τ.arrs "inter" = arrOf n
    (addCommon (processedClasses (τ.vars "i") entry) M rep baseInter) ∧
  PrefixEnumerates height entry M

lemma accumulateInv_initial
    {n height token : ℕ} {entry rep baseDegree baseInter stamp : ℕ → ℕ}
    {M : Finset ℕ} {σ : Env}
    (hi : σ.vars "i" = 0) (hheight : height ≤ n)
    (hn : σ.vars "n" = n) (hlen : σ.vars "neighborLen" = height)
    (htoken : σ.vars "token" = token)
    (hentry : σ.arrs "neighbors" = arrOf n entry)
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hstampMem : ∀ v < n, stamp v = token ↔ v ∈ M)
    (hstampBound : ∀ v < n, stamp v < n + 1)
    (hdegree : σ.arrs "degree" = arrOf n baseDegree)
    (hinter : σ.arrs "inter" = arrOf n baseInter)
    (henum : PrefixEnumerates height entry M) :
    AccumulateInv n height token entry rep baseDegree baseInter M σ := by
  refine ⟨by omega, hheight, hn, hlen, htoken, hentry, hrep,
    ⟨stamp, hstamp, hstampMem, hstampBound⟩, ?_, ?_, henum⟩
  · simpa [hi, processedClasses, addOn] using hdegree
  · simpa [hi, processedClasses, addCommon] using hinter

/-- One neighbor-prefix step performs the two advertised increments. -/
lemma accumulateNearBody_spec
    {B n height token : ℕ} {entry rep baseDegree baseInter : ℕ → ℕ}
    {M : Finset ℕ}
    (hnB : n + 1 < B)
    (hvertexN : ∀ q ∈ M, q < n)
    (hrepN : ∀ q ∈ M, rep q < n)
    (hdegreeB : ∀ q ∈ M, baseDegree q + 1 < B)
    (hinterB : ∀ q ∈ M, baseInter q + 1 < B) :
    Spec B
      (fun τ => AccumulateInv n height token entry rep baseDegree baseInter M τ ∧
        τ.vars "i" < height)
      accumulateNearBody
      (fun τ τ' =>
        AccumulateInv n height token entry rep baseDegree baseInter M τ' ∧
        τ'.vars "i" = τ.vars "i" + 1) 50 := by
  intro σ hσ
  rcases hσ with ⟨⟨hile, hheight, hn, hlen, htoken, hentry, hrep,
    ⟨stamp, hstamp, hstampMem, hstampBound⟩, hdegree, hinter, henum⟩,
    hilt⟩
  let P := processedClasses (σ.vars "i") entry
  let q := entry (σ.vars "i")
  have hnext := PrefixEnumerates.next_mem_not_processed henum hilt
  have hqM : q ∈ M := hnext.1
  have hqP : q ∉ P := hnext.2
  have hqN : q < n := hvertexN q hqM
  have hqB : q < B := hqN.trans (by omega)
  have hiB : σ.vars "i" < B :=
    (hilt.trans_le hheight).trans (by omega)
  have hget : (σ.arrs "neighbors")[σ.vars "i"]? = some q := by
    rw [hentry, getElem?_arrOf entry (hilt.trans_le hheight)]
  have hqEval : (Expr.get "neighbors" (.var "i")).evalB B σ = some q :=
    evalB_get (evalB_var hiB) hget hqB
  let σ₁ := σ.setVar "b" q
  have rb : Run B (.assign "b" (.get "neighbors" (.var "i"))) σ σ₁ 6 :=
    (Run.assign hqEval).mono (by norm_num [Expr.size])
  have hdegreeVal : addOn P baseDegree q = baseDegree q := by
    simp [addOn, hqP]
  have hdegreeEval : (Expr.get "degree" (.var "b")).evalB B σ₁ =
      some (addOn P baseDegree q) := by
    apply evalB_get
    · exact evalB_var (by simp [σ₁]; exact hqB)
    · simp [σ₁, hdegree, getElem?_arrOf _ hqN, P]
    · rw [hdegreeVal]
      exact (Nat.lt_of_succ_lt (hdegreeB q hqM))
  have hdegreeAdd :
      (Expr.add (.get "degree" (.var "b")) (.lit 1)).evalB B σ₁ =
        some (addOn P baseDegree q + 1) :=
    evalB_bin hdegreeEval (evalB_lit (by omega)) (by
      rw [hdegreeVal]
      exact hdegreeB q hqM)
  let σ₂ := σ₁.setArr "degree" q (addOn P baseDegree q + 1)
  have rdegree : Run B (.store "degree" (.var "b")
      (.add (.get "degree" (.var "b")) (.lit 1))) σ₁ σ₂ 8 := by
    have hbEval : (Expr.var "b").evalB B σ₁ = some q := by
      rw [show (Expr.var "b").evalB B σ₁ = some (σ₁.vars "b") from
        evalB_var (by simp [σ₁]; exact hqB)]
      simp [σ₁]
    have hr := Run.store (a := "degree") hbEval hdegreeAdd (by
      simp [σ₁, hdegree, length_arrOf, hqN])
    simpa [σ₂] using hr.mono (by norm_num [Expr.size])
  let r := rep q
  have hrN : r < n := hrepN q hqM
  have hrB : r < B := hrN.trans (by omega)
  have hrEval : (Expr.get "repB" (.var "b")).evalB B σ₂ = some r := by
    apply evalB_get
    · exact evalB_var (by simp [σ₂, σ₁]; exact hqB)
    · simp [σ₂, σ₁, hrep, getElem?_arrOf rep hqN, r]
    · exact hrB
  let σ₃ := σ₂.setVar "r" r
  have rr : Run B (.assign "r" (.get "repB" (.var "b"))) σ₂ σ₃ 6 :=
    (Run.assign hrEval).mono (by norm_num [Expr.size])
  have hstampEval : (Expr.get "stamp" (.var "r")).evalB B σ₃ =
      some (stamp r) := by
    apply evalB_get
    · exact evalB_var (by simp [σ₃]; exact hrB)
    · simp [σ₃, σ₂, σ₁, hstamp, getElem?_arrOf stamp hrN]
    · exact (hstampBound r hrN).trans hnB
  have htokenEval : (Expr.var "token").evalB B σ₃ = some token := by
    have htokenN : token < n + 1 := by
      have := hstampBound q hqN
      have hqStamp := (hstampMem q hqN).mpr hqM
      omega
    rw [show (Expr.var "token").evalB B σ₃ = some (σ₃.vars "token") from
      evalB_var (by simp [σ₃, σ₂, σ₁, htoken]; exact htokenN.trans hnB)]
    simp [σ₃, σ₂, σ₁, htoken]
  by_cases hrM : r ∈ M
  · have hstampR : stamp r = token := (hstampMem r hrN).mpr hrM
    have htest :
        (Cond.eq (.get "stamp" (.var "r")) (.var "token")).evalB B σ₃ =
          some true := by
      simpa [hstampR] using evalB_condEq hstampEval htokenEval
    have hinterVal : addCommon P M rep baseInter q = baseInter q := by
      simp [addCommon, hqP]
    have hinterEval : (Expr.get "inter" (.var "b")).evalB B σ₃ =
        some (addCommon P M rep baseInter q) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₃]; exact hqB)
      · simp [σ₃, σ₂, σ₁, hinter, getElem?_arrOf _ hqN, P]
      · rw [hinterVal]
        exact Nat.lt_of_succ_lt (hinterB q hqM)
    have hinterAdd :
        (Expr.add (.get "inter" (.var "b")) (.lit 1)).evalB B σ₃ =
          some (addCommon P M rep baseInter q + 1) :=
      evalB_bin hinterEval (evalB_lit (by omega)) (by
        rw [hinterVal]
        exact hinterB q hqM)
    let σ₄ := σ₃.setArr "inter" q (addCommon P M rep baseInter q + 1)
    have rinter : Run B (.store "inter" (.var "b")
        (.add (.get "inter" (.var "b")) (.lit 1))) σ₃ σ₄ 8 := by
      have hbEval : (Expr.var "b").evalB B σ₃ = some q := by
        rw [show (Expr.var "b").evalB B σ₃ = some (σ₃.vars "b") from
          evalB_var (by simp [σ₃, σ₂, σ₁]; exact hqB)]
        simp [σ₃, σ₂, σ₁]
      have hr := Run.store (a := "inter") hbEval hinterAdd (by
        simp [σ₃, σ₂, σ₁, hinter, length_arrOf, hqN])
      simpa [σ₄] using hr.mono (by norm_num [Expr.size])
    have rif : Run B
        (.ite (.eq (.get "stamp" (.var "r")) (.var "token"))
          (.store "inter" (.var "b")
            (.add (.get "inter" (.var "b")) (.lit 1))) .skip)
        σ₃ σ₄ 20 := (Run.ite_true htest rinter).mono (by
      norm_num [Cond.size, Expr.size])
    let σ₅ := σ₄.setVar "i" (σ.vars "i" + 1)
    have ri : Run B (inc "i") σ₄ σ₅ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [σ₄, σ₃, σ₂, σ₁] using evalB_var hiB)
        (evalB_lit (by omega)) (by
          simpa using (show σ.vars "i" + 1 < B by omega))
    refine ⟨σ₅, (rb.seq (rdegree.seq (rr.seq (rif.seq ri)))).mono (by
      norm_num [accumulateNearBody, seqs, Cond.size, Expr.size]), ?_,
      by simp [σ₅]⟩
    refine ⟨by simp [σ₅]; omega, hheight,
      by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hn],
      by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hlen],
      by simp [σ₅, σ₄, σ₃, σ₂, σ₁, htoken],
      by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hentry],
      by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hrep],
      ⟨stamp, by simp [σ₅, σ₄, σ₃, σ₂, σ₁, hstamp], hstampMem,
        hstampBound⟩, ?_, ?_, henum⟩
    · simp only [σ₅, σ₄, σ₃, σ₂, σ₁, arrs_setVar, vars_setVar,
        arrs_setArr, if_pos]
      rw [if_neg (by decide : "degree" ≠ "inter"), hdegree,
        set_arrOf_eq_upd, processedClasses_succ, upd_addOn hqP]
    · simp only [σ₅, σ₄, σ₃, σ₂, σ₁, arrs_setVar, vars_setVar,
        arrs_setArr, if_pos]
      rw [if_neg (by decide : "inter" ≠ "degree"), hinter,
        set_arrOf_eq_upd, processedClasses_succ,
        upd_addCommon hqP hrM]
  · have hstampR : stamp r ≠ token := by
      intro heq
      exact hrM ((hstampMem r hrN).mp heq)
    have htest :
        (Cond.eq (.get "stamp" (.var "r")) (.var "token")).evalB B σ₃ =
          some false := by
      simpa [hstampR] using evalB_condEq hstampEval htokenEval
    have rif : Run B
        (.ite (.eq (.get "stamp" (.var "r")) (.var "token"))
          (.store "inter" (.var "b")
            (.add (.get "inter" (.var "b")) (.lit 1))) .skip)
        σ₃ σ₃ 20 := (Run.ite_false htest Run.skip).mono (by
      norm_num [Cond.size, Expr.size])
    let σ₄ := σ₃.setVar "i" (σ.vars "i" + 1)
    have ri : Run B (inc "i") σ₃ σ₄ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [σ₃, σ₂, σ₁] using evalB_var hiB)
        (evalB_lit (by omega)) (by
          simpa using (show σ.vars "i" + 1 < B by omega))
    refine ⟨σ₄, (rb.seq (rdegree.seq (rr.seq (rif.seq ri)))).mono (by
      norm_num [accumulateNearBody, seqs, Cond.size, Expr.size]), ?_,
      by simp [σ₄]⟩
    refine ⟨by simp [σ₄]; omega, hheight,
      by simp [σ₄, σ₃, σ₂, σ₁, hn],
      by simp [σ₄, σ₃, σ₂, σ₁, hlen],
      by simp [σ₄, σ₃, σ₂, σ₁, htoken],
      by simp [σ₄, σ₃, σ₂, σ₁, hentry],
      by simp [σ₄, σ₃, σ₂, σ₁, hrep],
      ⟨stamp, by simp [σ₄, σ₃, σ₂, σ₁, hstamp], hstampMem,
        hstampBound⟩, ?_, ?_, henum⟩
    · simp only [σ₄, σ₃, σ₂, σ₁, arrs_setVar, vars_setVar,
        arrs_setArr, if_pos]
      rw [hdegree, set_arrOf_eq_upd, processedClasses_succ, upd_addOn hqP]
    · simp only [σ₄, σ₃, σ₂, σ₁, arrs_setVar, vars_setVar,
        arrs_setArr, if_pos]
      rw [if_neg (by decide : "inter" ≠ "degree"), hinter,
        processedClasses_succ, addCommon_insert_of_rep_notMem hrM]

/-- Replaying the complete neighbor stack updates exactly its members. -/
lemma accumulateNearLoop_run
    {B n height token : ℕ} {entry rep baseDegree baseInter : ℕ → ℕ}
    {M : Finset ℕ} {σ : Env}
    (hI : AccumulateInv n height token entry rep baseDegree baseInter M σ)
    (hnB : n + 1 < B)
    (hvertexN : ∀ q ∈ M, q < n)
    (hrepN : ∀ q ∈ M, rep q < n)
    (hdegreeB : ∀ q ∈ M, baseDegree q + 1 < B)
    (hinterB : ∀ q ∈ M, baseInter q + 1 < B) :
    ∃ σ', Run B (.while (.lt (.var "i") (.var "neighborLen"))
        accumulateNearBody) σ σ' (54 * height + 4) ∧
      AccumulateInv n height token entry rep baseDegree baseInter M σ' ∧
      σ'.vars "i" = height ∧
      σ'.arrs "degree" = arrOf n (addOn M baseDegree) ∧
      σ'.arrs "inter" = arrOf n (addCommon M M rep baseInter) := by
  let I := AccumulateInv n height token entry rep baseDegree baseInter M
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < height)
      accumulateNearBody
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 50 :=
    accumulateNearBody_spec hnB hvertexN hrepN hdegreeB hinterB
  obtain ⟨σ', rloop, hI', hi'⟩ :=
    (Spec.forRange (B := B) "i" "neighborLen" I height 50
      (54 * height + 4)
      (fun _ h => (h.1.trans h.2.1).trans_lt (by omega))
      (fun _ h => by
        rw [h.2.2.2.1]
        exact h.2.1.trans_lt (by omega))
      (fun _ h => h.2.2.2.1) (fun _ h => h.1) hbody
      (fun _ h => h)
      (fun τ _ => Nat.add_le_add_right
        (Nat.mul_le_mul_left 54 (Nat.sub_le height (τ.vars "i"))) 4)).run hI
  have hprocessed : processedClasses height entry = M :=
    PrefixEnumerates.processedClasses_eq hI'.2.2.2.2.2.2.2.2.2.2
  refine ⟨σ', rloop, hI', hi', ?_, ?_⟩
  · simpa [hi', hprocessed] using hI'.2.2.2.2.2.2.2.2.1
  · simpa [hi', hprocessed] using hI'.2.2.2.2.2.2.2.2.2.1

end Lax235315Proofs.Construction.NearAccumulateSource
