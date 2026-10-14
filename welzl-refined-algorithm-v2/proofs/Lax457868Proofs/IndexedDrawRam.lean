import Mathlib.Tactic
import Lax808846Proofs.Imp
import Lax808846Proofs.Reasoning
import Lax457868Proofs.FairBitRam
import Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-!
An indexed draw from a raw domain array. The selector consumes exactly its
attempted bit blocks; a successful index is then looked up in the domain
array. Exhaustion leaves the caller's `drawVertex` value unchanged.
-/

namespace Lax457868Proofs.IndexedDrawRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.FairBitRam

/-- Look up the selected domain entry only after the capped selector succeeds. -/
def indexedDrawLookup : Com :=
  .ite (.eq (.var "drawFound") (.lit 1))
    (.assign "drawVertex" (.get "drawDomain" (.var "drawValue"))) .skip

/-- Run one capped fair-bit draw and store its selected domain value. The
active domain has size `m` and occupies a prefix of an array of capacity at
least `m`; active values fit in a RAM word. On exhaustion, the prior
`drawVertex` value is preserved. -/
lemma countedIndexedDraw_run_tape {B n v m domainCap t : ℕ}
    {σ : Env} {g domain : ℕ → ℕ} {rest : List ℕ}
    (tape : BitTape m t) (hm : 0 < m)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hdomain : σ.arrs "drawDomain" = arrOf domainCap domain)
    (hmCap : m ≤ domainCap)
    (hvalueB : ∀ i < m, domain i < B)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = Nat.clog 2 m)
    (hmod : σ.vars "drawModulus" = m)
    (hcap : σ.vars "drawCap" = t)
    (hinp : σ.inp = flattenBitBlocks tape ++ rest)
    (hpowB : 2 ^ Nat.clog 2 m < B) (hnB : n < B) (htwoB : 2 < B)
    (htB : t < B) (hmB : m < B) :
    ∃ σ' g',
      Run B (seqs [countedRejectionSelector, indexedDrawLookup]) σ σ'
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 19) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ i < n, i ≠ v → g' i = g i) ∧
      (∀ i, (selectBitIndexWithCount m hm t tape).1 = some i →
        σ'.vars "drawVertex" = domain i.val) ∧
      ((selectBitIndexWithCount m hm t tape).1 = none →
        σ'.vars "drawVertex" = σ.vars "drawVertex") ∧
      σ'.vars "drawUsed" = bitTapeAttemptsUsed m t tape ∧
      σ'.vars "drawFound" =
        (if (selectBitIndexWithCount m hm t tape).1 = none then 0 else 1) ∧
      σ'.inp = flattenBitBlockList
        ((List.ofFn tape).drop (bitTapeAttemptsUsed m t tape)) ++ rest ∧
      σ'.arrs "drawDomain" = arrOf domainCap domain ∧
      (∀ a, a ≠ "key0" → σ'.arrs a = σ.arrs a) ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = Nat.clog 2 m ∧
      σ'.vars "drawModulus" = m ∧ σ'.vars "drawCap" = t := by
  obtain ⟨σ₁, g', hselector, hkey₁, hframe₁, hselected, hused₁, hfound₁,
      hinp₁, hv₁, hL₁, hmod₁, hcap₁, harrframe₁⟩ :=
    countedRejectionSelector_run_tape tape hm hkey hv hvn hL hmod hcap hinp
      hpowB hnB htwoB htB hmB
  have hdomain₁ : σ₁.arrs "drawDomain" = arrOf domainCap domain := by
    exact (harrframe₁ "drawDomain" (by decide)).trans hdomain
  have hvertex₁ : σ₁.vars "drawVertex" = σ.vars "drawVertex" :=
    hselector.frame_var "drawVertex" (by decide)
  by_cases hsuccess : (selectBitIndexWithCount m hm t tape).1 ≠ none
  · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hsuccess
    have hfoundOne : σ₁.vars "drawFound" = 1 := by
      simp [hfound₁, hsuccess]
    have hdraw : σ₁.vars "drawValue" = i.val := by
      exact (hselected i hi).2
    have hiB : i.val < B := lt_trans i.isLt hmB
    have hdrawB : σ₁.vars "drawValue" < B := by rw [hdraw]; exact hiB
    have hget : (Expr.get "drawDomain" (.var "drawValue")).evalB B σ₁ =
        some (domain i.val) := by
      apply evalB_get (evalB_var hdrawB) _ (hvalueB i.val i.isLt)
      rw [hdraw, hdomain₁, getElem?_arrOf _ (lt_of_lt_of_le i.isLt hmCap)]
    let σ₂ := σ₁.setVar "drawVertex" (domain i.val)
    have hassign : Run B
        (.assign "drawVertex" (.get "drawDomain" (.var "drawValue"))) σ₁ σ₂ 3 := by
      simpa [σ₂] using (Run.assign hget)
    have hcondTrue :
        (Cond.eq (.var "drawFound") (.lit 1)).evalB B σ₁ = some true := by
      rw [evalB_condEq (evalB_var (by rw [hfoundOne]; omega))
        (evalB_lit (by omega : 1 < B))]
      simp [hfoundOne]
    have hlookup : Run B indexedDrawLookup σ₁ σ₂ 7 := by
      change Run B
        (.ite (.eq (.var "drawFound") (.lit 1))
          (.assign "drawVertex" (.get "drawDomain" (.var "drawValue"))) .skip)
        σ₁ σ₂ 7
      have hit : Run B
          (.ite (.eq (.var "drawFound") (.lit 1))
            (.assign "drawVertex" (.get "drawDomain" (.var "drawValue"))) .skip)
          σ₁ σ₂
          (1 + Cond.size (Cond.eq (.var "drawFound") (.lit 1)) + 3) :=
        Run.ite_true hcondTrue hassign
      have hcost : 1 + Cond.size (Cond.eq (.var "drawFound") (.lit 1)) + 3 ≤ 7 := by
        decide
      exact hit.mono hcost
    have hwhole : Run B (seqs [countedRejectionSelector, indexedDrawLookup])
        σ σ₂
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 19) := by
      have hseq := Run.seq hselector hlookup
      simpa [seqs, Nat.add_assoc] using hseq
    have hv₂ : σ₂.vars "v" = v :=
      (hlookup.frame_var "v" (by decide)).trans hv₁
    have hL₂ : σ₂.vars "L" = Nat.clog 2 m :=
      (hlookup.frame_var "L" (by decide)).trans hL₁
    have hmod₂ : σ₂.vars "drawModulus" = m :=
      (hlookup.frame_var "drawModulus" (by decide)).trans hmod₁
    have hcap₂ : σ₂.vars "drawCap" = t :=
      (hlookup.frame_var "drawCap" (by decide)).trans hcap₁
    refine ⟨σ₂, g', hwhole, hkey₁, hframe₁, ?_⟩
    constructor
    · intro j hj
      have hji : j = i := by
        apply Fin.ext
        calc
          j.val = σ₁.vars "drawValue" := ((hselected j hj).2).symm
          _ = i.val := hdraw
      subst j
      simp [σ₂]
    constructor
    · intro hnone
      rw [hnone] at hi
      cases hi
    constructor
    · exact hused₁
    constructor
    · exact hfound₁
    constructor
    · exact hinp₁
    constructor
    · exact hdomain₁
    constructor
    · intro a ha
      exact (hlookup.frame_arr a (by simp [indexedDrawLookup, Com.warrs])).trans
        (harrframe₁ a ha)
    constructor
    · exact hv₂
    constructor
    · exact hL₂
    constructor
    · exact hmod₂
    · exact hcap₂
  · have hnone : (selectBitIndexWithCount m hm t tape).1 = none := by
      cases hsel : (selectBitIndexWithCount m hm t tape).1 with
      | none => rfl
      | some i => simp [hsel] at hsuccess
    have hfoundZero : σ₁.vars "drawFound" = 0 := by
      simp [hfound₁, hnone]
    have hcondFalse :
        (Cond.eq (.var "drawFound") (.lit 1)).evalB B σ₁ = some false := by
      rw [evalB_condEq (evalB_var (by rw [hfoundZero]; omega))
        (evalB_lit (by omega : 1 < B))]
      simp [hfoundZero]
    have hlookup : Run B indexedDrawLookup σ₁ σ₁ 7 := by
      change Run B
        (.ite (.eq (.var "drawFound") (.lit 1))
          (.assign "drawVertex" (.get "drawDomain" (.var "drawValue"))) .skip)
        σ₁ σ₁ 7
      have hit : Run B
          (.ite (.eq (.var "drawFound") (.lit 1))
            (.assign "drawVertex" (.get "drawDomain" (.var "drawValue"))) .skip)
          σ₁ σ₁
          (1 + Cond.size (Cond.eq (.var "drawFound") (.lit 1)) + 1) :=
        Run.ite_false hcondFalse Run.skip
      have hcost : 1 + Cond.size (Cond.eq (.var "drawFound") (.lit 1)) + 1 ≤ 7 := by
        decide
      exact hit.mono hcost
    have hwhole : Run B (seqs [countedRejectionSelector, indexedDrawLookup])
        σ σ₁
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t tape + 19) := by
      have hseq := Run.seq hselector hlookup
      simpa [seqs, Nat.add_assoc] using hseq
    have hv₂ : σ₁.vars "v" = v :=
      (hlookup.frame_var "v" (by decide)).trans hv₁
    have hL₂ : σ₁.vars "L" = Nat.clog 2 m :=
      (hlookup.frame_var "L" (by decide)).trans hL₁
    have hmod₂ : σ₁.vars "drawModulus" = m :=
      (hlookup.frame_var "drawModulus" (by decide)).trans hmod₁
    have hcap₂ : σ₁.vars "drawCap" = t :=
      (hlookup.frame_var "drawCap" (by decide)).trans hcap₁
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
    · exact hdomain₁
    constructor
    · exact harrframe₁
    constructor
    · exact hv₂
    constructor
    · exact hL₂
    constructor
    · exact hmod₂
    · exact hcap₂

end Lax457868Proofs.IndexedDrawRam
