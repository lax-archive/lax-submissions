import Mathlib.Tactic
import Lax808846Proofs.Imp
import Lax808846Proofs.Reasoning
import Lax457868Proofs.FairBitRam
import Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-!
The source draw from a class-order array uses the accepted rejection index as
an offset from the beginning of the active class slice.
-/

namespace Lax457868Proofs.ClassOffsetDraw

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.FairBitRam

/-- Read the class-order entry at the active slice offset after selection. -/
def classOffsetDrawLookup : Com :=
  .ite (.eq (.var "drawFound") (.lit 1))
    (.assign "drawVertex"
      (.get "ord" (.add (.var "drawOffset") (.var "drawValue")))) .skip

/-- Execute the offset lookup for an already selected index. The fixed array
`ord` contains the entire order, and the active class occupies the slice
starting at `drawOffset` with length `m`. -/
lemma classOffsetDrawLookup_run_selected {B m ordCap offset : ℕ}
    {σ : Env} {ord : ℕ → ℕ} {i : Fin m}
    (hfound : σ.vars "drawFound" = 1)
    (hdraw : σ.vars "drawValue" = i.val)
    (hoffset : σ.vars "drawOffset" = offset)
    (hoffsetB : offset < B)
    (hmCap : offset + m ≤ ordCap)
    (hordCap : ordCap < B)
    (hord : σ.arrs "ord" = arrOf ordCap ord)
    (hvalueB : ∀ j < m, ord (offset + j) < B) :
    ∃ σ', Run B classOffsetDrawLookup σ σ' 9 ∧
      σ'.vars "drawVertex" = ord (offset + i.val) := by
  have hindexCap : offset + i.val < ordCap := by omega
  have hindexB : offset + i.val < B := lt_of_lt_of_le hindexCap hordCap.le
  have hoffsetVarB : σ.vars "drawOffset" < B := by rw [hoffset]; exact hoffsetB
  have hdrawVarB : σ.vars "drawValue" < B := by rw [hdraw]; omega
  have hsum : (Expr.add (.var "drawOffset") (.var "drawValue")).evalB B σ =
      some (offset + i.val) := by
    apply evalB_bin
    · rw [evalB_var hoffsetVarB, hoffset]
    · rw [evalB_var hdrawVarB, hdraw]
    · exact hindexB
  have hget : (σ.arrs "ord")[offset + i.val]? = some (ord (offset + i.val)) := by
    rw [hord, getElem?_arrOf _ hindexCap]
  have hgetEval : (Expr.get "ord"
      (.add (.var "drawOffset") (.var "drawValue"))).evalB B σ =
        some (ord (offset + i.val)) :=
    evalB_get hsum hget (hvalueB i.val i.isLt)
  let σ' := σ.setVar "drawVertex" (ord (offset + i.val))
  have hassign : Run B
      (.assign "drawVertex"
        (.get "ord" (.add (.var "drawOffset") (.var "drawValue")))) σ σ' 5 := by
    exact Run.assign hgetEval
  have hcond : (Cond.eq (.var "drawFound") (.lit 1)).evalB B σ = some true := by
    rw [evalB_condEq (evalB_var (by rw [hfound]; omega))
      (evalB_lit (by omega : 1 < B))]
    simp [hfound]
  have hrun : Run B classOffsetDrawLookup σ σ' 9 := by
    change Run B
      (.ite (.eq (.var "drawFound") (.lit 1))
        (.assign "drawVertex"
          (.get "ord" (.add (.var "drawOffset") (.var "drawValue")))) .skip)
      σ σ' 9
    have hrun' : Run B
        (.ite (.eq (.var "drawFound") (.lit 1))
          (.assign "drawVertex"
            (.get "ord" (.add (.var "drawOffset") (.var "drawValue")))) .skip)
        σ σ' (1 + Cond.size (Cond.eq (.var "drawFound") (.lit 1)) + 5) :=
      Run.ite_true hcond hassign
    have hcost : 1 + Cond.size (Cond.eq (.var "drawFound") (.lit 1)) + 5 ≤ 9 := by
      decide
    exact hrun'.mono hcost
  exact ⟨σ', hrun, by simp [σ']⟩

/-- Run the capped fair-bit selector, then store the order entry at
`drawOffset + drawValue`. A successful selection returns the corresponding
entry of the active order slice; exhaustion leaves `drawVertex` unchanged.
The selector consumes exactly the attempted tape blocks. -/
lemma countedClassOffsetDraw_run_tape {B n v m t ordCap offset : ℕ}
    {σ : Env} {g ord : ℕ → ℕ} {rest : List ℕ}
    (tape : BitTape m t) (hm : 0 < m)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hord : σ.arrs "ord" = arrOf ordCap ord)
    (hordCap : ordCap < B)
    (hordValue : ∀ j < m, ord (offset + j) < B)
    (hactiveCap : offset + m ≤ ordCap)
    (hoffset : σ.vars "drawOffset" = offset)
    (hkeyOffset : σ.vars "drawOffset" < B)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = Nat.clog 2 m)
    (hmod : σ.vars "drawModulus" = m)
    (hcap : σ.vars "drawCap" = t)
    (hinp : σ.inp = flattenBitBlocks tape ++ rest)
    (hpowB : 2 ^ Nat.clog 2 m < B) (hnB : n < B) (htwoB : 2 < B)
    (htB : t < B) (hmB : m < B) :
    ∃ σ' g',
      Run B (seqs [countedRejectionSelector, classOffsetDrawLookup]) σ σ'
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 21) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ j < n, j ≠ v → g' j = g j) ∧
      (∀ i, (selectBitIndexWithCount m hm t tape).1 = some i →
        σ'.vars "drawVertex" = ord (offset + i.val)) ∧
      ((selectBitIndexWithCount m hm t tape).1 = none →
        σ'.vars "drawVertex" = σ.vars "drawVertex") ∧
      σ'.vars "drawUsed" = bitTapeAttemptsUsed m t tape ∧
      σ'.vars "drawFound" =
        (if (selectBitIndexWithCount m hm t tape).1 = none then 0 else 1) ∧
      σ'.inp = flattenBitBlockList
        ((List.ofFn tape).drop (bitTapeAttemptsUsed m t tape)) ++ rest ∧
      σ'.arrs "ord" = arrOf ordCap ord ∧
      (∀ a, a ≠ "key0" → σ'.arrs a = σ.arrs a) ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = Nat.clog 2 m ∧
      σ'.vars "drawModulus" = m ∧ σ'.vars "drawCap" = t ∧
      σ'.vars "drawOffset" = offset := by
  obtain ⟨σ₁, g', hselector, hkey₁, hframe₁, hselected, hused₁, hfound₁,
      hinp₁, hv₁, hL₁, hmod₁, hcap₁, harrframe₁⟩ :=
    countedRejectionSelector_run_tape tape hm hkey hv hvn hL hmod hcap hinp
      hpowB hnB htwoB htB hmB
  have hord₁ : σ₁.arrs "ord" = arrOf ordCap ord := by
    exact (harrframe₁ "ord" (by decide)).trans hord
  have hoffset₁ : σ₁.vars "drawOffset" = offset :=
    (hselector.frame_var "drawOffset" (by decide)).trans hoffset
  have hoffsetB : offset < B := by
    rw [← hoffset]
    exact hkeyOffset
  have hvertex₁ : σ₁.vars "drawVertex" = σ.vars "drawVertex" :=
    hselector.frame_var "drawVertex" (by decide)
  by_cases hsuccess : (selectBitIndexWithCount m hm t tape).1 ≠ none
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hsuccess
    have hfoundOne : σ₁.vars "drawFound" = 1 := by
      simp [hfound₁, hsuccess]
    have hdraw : σ₁.vars "drawValue" = i.val :=
      (hselected i hi).2
    obtain ⟨σ₂, hlookup, hvertex₂⟩ :=
      classOffsetDrawLookup_run_selected hfoundOne hdraw hoffset₁
        hoffsetB hactiveCap hordCap hord₁ hordValue
    have hwhole : Run B (seqs [countedRejectionSelector, classOffsetDrawLookup])
        σ σ₂
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 21) := by
      have hseq := Run.seq hselector hlookup
      simpa [seqs, Nat.add_assoc] using hseq
    have hord₂ : σ₂.arrs "ord" = arrOf ordCap ord :=
      (hlookup.frame_arr "ord" (by decide)).trans hord₁
    have hkey₂ : σ₂.arrs "key0" = arrOf n g' :=
      (hlookup.frame_arr "key0" (by decide)).trans hkey₁
    have hused₂ : σ₂.vars "drawUsed" = bitTapeAttemptsUsed m t tape :=
      (hlookup.frame_var "drawUsed" (by decide)).trans hused₁
    have hfound₂ : σ₂.vars "drawFound" =
        (if (selectBitIndexWithCount m hm t tape).1 = none then 0 else 1) :=
      (hlookup.frame_var "drawFound" (by decide)).trans hfound₁
    have hinp₂ : σ₂.inp = flattenBitBlockList
        ((List.ofFn tape).drop (bitTapeAttemptsUsed m t tape)) ++ rest :=
      (hlookup.frame_inp (by decide)).trans hinp₁
    have hv₂ : σ₂.vars "v" = v := (hlookup.frame_var "v" (by decide)).trans hv₁
    have hL₂ : σ₂.vars "L" = Nat.clog 2 m :=
      (hlookup.frame_var "L" (by decide)).trans hL₁
    have hmod₂ : σ₂.vars "drawModulus" = m :=
      (hlookup.frame_var "drawModulus" (by decide)).trans hmod₁
    have hcap₂ : σ₂.vars "drawCap" = t :=
      (hlookup.frame_var "drawCap" (by decide)).trans hcap₁
    have hoffset₂ : σ₂.vars "drawOffset" = offset :=
      (hlookup.frame_var "drawOffset" (by decide)).trans hoffset₁
    refine ⟨σ₂, g', hwhole, hkey₂, hframe₁, ?_⟩
    constructor
    · intro j hj
      have hji : j = i := by
        apply Fin.ext
        calc
          j.val = σ₁.vars "drawValue" := ((hselected j hj).2).symm
          _ = i.val := hdraw
      subst j
      exact hvertex₂
    constructor
    · intro hnone
      rw [hnone] at hi
      cases hi
    constructor
    · exact hused₂
    constructor
    · exact hfound₂
    constructor
    · exact hinp₂
    constructor
    · exact hord₂
    constructor
    · intro a ha
      exact (hlookup.frame_arr a (by simp [classOffsetDrawLookup, Com.warrs])).trans
        (harrframe₁ a ha)
    constructor
    · exact hv₂
    constructor
    · exact hL₂
    constructor
    · exact hmod₂
    constructor
    · exact hcap₂
    · exact hoffset₂
  · have hnone : (selectBitIndexWithCount m hm t tape).1 = none := by
      cases hsel : (selectBitIndexWithCount m hm t tape).1 with
      | none => rfl
      | some i => simp [hsel] at hsuccess
    have hfoundZero : σ₁.vars "drawFound" = 0 := by
      simp [hfound₁, hnone]
    have hcondFalse : (Cond.eq (.var "drawFound") (.lit 1)).evalB B σ₁ =
        some false := by
      rw [evalB_condEq (evalB_var (by rw [hfoundZero]; omega))
        (evalB_lit (by omega : 1 < B))]
      simp [hfoundZero]
    have hlookup : Run B classOffsetDrawLookup σ₁ σ₁ 9 := by
      change Run B
        (.ite (.eq (.var "drawFound") (.lit 1))
          (.assign "drawVertex"
          (.get "ord" (.add (.var "drawOffset") (.var "drawValue")))) .skip)
        σ₁ σ₁ 9
      have hit : Run B
          (.ite (.eq (.var "drawFound") (.lit 1))
            (.assign "drawVertex"
              (.get "ord" (.add (.var "drawOffset") (.var "drawValue")))) .skip)
          σ₁ σ₁ (1 + Cond.size (Cond.eq (.var "drawFound") (.lit 1)) + 1) :=
        Run.ite_false hcondFalse Run.skip
      have hcost : 1 + Cond.size (Cond.eq (.var "drawFound") (.lit 1)) + 1 ≤ 9 := by
        decide
      exact hit.mono hcost
    have hwhole : Run B (seqs [countedRejectionSelector, classOffsetDrawLookup])
        σ σ₁
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 21) := by
      have hseq := Run.seq hselector hlookup
      simpa [seqs, Nat.add_assoc] using hseq
    have hoffset₁' : σ₁.vars "drawOffset" = offset := hoffset₁
    refine ⟨σ₁, g', hwhole, hkey₁, hframe₁, ?_⟩
    constructor
    · intro i hi
      simp [hnone] at hi
    constructor
    · intro _
      exact hvertex₁
    constructor
    · exact hused₁
    constructor
    · exact hfound₁
    constructor
    · exact hinp₁
    constructor
    · exact hord₁
    constructor
    · exact harrframe₁
    constructor
    · exact hv₁
    constructor
    · exact hL₁
    constructor
    · exact hmod₁
    constructor
    · exact hcap₁
    · exact hoffset₁'

end Lax457868Proofs.ClassOffsetDraw
