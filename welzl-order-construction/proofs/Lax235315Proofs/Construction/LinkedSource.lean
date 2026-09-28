import Lax235315Proofs.Construction.LinkedReconstruction
import Lax808846Proofs.Reasoning
import Mathlib.Tactic

/-! Bounded source execution of the linked-list insertion body from
`WelzlProgram.reconstructAndWrite`. -/

namespace Lax235315Proofs.Construction.LinkedSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.LinkedReconstruction
open Lax235315Proofs.Construction.WelzlProgram

/-- The literal body of one iteration of the inner reconstruction loop. -/
def linkedInsertBody : Com :=
  seqs [
    .assign "v" (.get "removed" (.var "i")),
    .assign "r" (.get "removedRep" (.var "i")),
    .store "nextVertex" (.var "v") (.get "nextVertex" (.var "r")),
    .store "nextVertex" (.var "r") (.var "v"),
    inc "i"]

/-- This is the exact command expression nested in `reconstructAndWrite`. -/
lemma linkedInsertBody_eq_source_excerpt :
    linkedInsertBody =
      seqs [
        .assign "v" (.get "removed" (.var "i")),
        .assign "r" (.get "removedRep" (.var "i")),
        .store "nextVertex" (.var "v") (.get "nextVertex" (.var "r")),
        .store "nextVertex" (.var "r" ) (.var "v"),
        inc "i"] := rfl

/-- The inner bounded scan in `reconstructAndWrite`, isolated from the outer
round loop. -/
def linkedInsertLoop : Com :=
  .while (.lt (.var "i") (.var "iend")) linkedInsertBody

/-- The ordered writes addressed by a contiguous interval in the source's
log-indexed `removed` and `removedRep` arrays. -/
def writeLogPrefix (representative removed : ℕ → ℕ) (start : ℕ) :
    ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, next => next
  | k + 1, next =>
      writeAfter (writeLogPrefix representative removed start k next)
        (representative (start + k)) (removed (start + k))

/-- The indexed successor step of a log prefix. -/
lemma writeLogPrefix_succ (representative removed : ℕ → ℕ) (start k : ℕ)
    (next : ℕ → ℕ) :
    writeLogPrefix representative removed start (k + 1) next =
      writeAfter (writeLogPrefix representative removed start k next)
        (representative (start + k)) (removed (start + k)) := rfl

lemma writeAfter_preserves_bound {B n : ℕ} (next : ℕ → ℕ) (r x : ℕ)
    (hr : r < n) (hxB : x < B) (hnextB : ∀ k < n, next k < B) :
    ∀ k < n, writeAfter next r x k < B := by
  intro k hk
  by_cases hkr : k = r
  · subst k
    rw [writeAfter_apply_r]
    exact hxB
  · by_cases hkx : k = x
    · subst k
      rw [writeAfter_apply_x next r x (fun h => hkr h.symm)]
      exact hnextB r hr
    · rw [writeAfter_apply_of_ne next r x k hkr hkx]
      exact hnextB k hk

/-- Invariant for an inner restoration scan.  Its pointer array is the
log-indexed fold of exactly the entries already processed. -/
def LinkedInsertInv (B n m start stop : ℕ)
    (removed representative initialNext : ℕ → ℕ)
    (initialHead : ℕ) (initialInput initialOutput : List ℕ) (σ : Env) : Prop :=
  let i := σ.vars "i"
  start ≤ i ∧ i ≤ stop ∧ σ.vars "iend" = stop ∧
    σ.arrs "removed" = arrOf m removed ∧
    σ.arrs "removedRep" = arrOf m representative ∧
    σ.arrs "nextVertex" =
      arrOf n (writeLogPrefix representative removed start (i - start) initialNext) ∧
    (∀ k < n, writeLogPrefix representative removed start
      (i - start) initialNext k < B) ∧
    σ.vars "head" = initialHead ∧ σ.inp = initialInput ∧
    σ.out = initialOutput

/-- Running one insertion iteration performs exactly the source writes.
The array hypotheses expose numeric representations of the three arrays;
`hnextAllB` bounds every existing pointer, including the unconstrained tail
cell, so bounded array reads remain valid. -/
lemma linkedInsertBody_run
    {B n m i x r : ℕ} {removed representative next : ℕ → ℕ} {σ : Env}
    (hi : σ.vars "i" = i) (hiB : i < B) (hiNextB : i + 1 < B)
    (hremoved : σ.arrs "removed" = arrOf m removed)
    (hrepresentative : σ.arrs "removedRep" = arrOf m representative)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (him : i < m) (hx : removed i = x) (hr : representative i = r)
    (hxm : x < n) (hrn : r < n)
    (hremovedB : ∀ k < m, removed k < B)
    (hrepresentativeB : ∀ k < m, representative k < B)
    (hnextAllB : ∀ k < n, next k < B) :
    ∃ σ', Run B linkedInsertBody σ σ' 17 ∧
      σ'.vars "i" = i + 1 ∧ σ'.vars "v" = x ∧ σ'.vars "r" = r ∧
      σ'.arrs "nextVertex" = arrOf n (writeAfter next r x) ∧
      σ'.arrs "removed" = σ.arrs "removed" ∧
      σ'.arrs "removedRep" = σ.arrs "removedRep" ∧
      σ'.vars "iend" = σ.vars "iend" ∧
      σ'.vars "head" = σ.vars "head" ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let σ₁ := σ.setVar "v" x
  let σ₂ := σ₁.setVar "r" r
  let σ₃ := σ₂.setArr "nextVertex" x (next r)
  let σ₄ := σ₃.setArr "nextVertex" r x
  let σ₅ := σ₄.setVar "i" (i + 1)
  have hxB : x < B := by rw [← hx]; exact hremovedB i him
  have hrB : r < B := by rw [← hr]; exact hrepresentativeB i him
  have hnextB : next r < B := hnextAllB r hrn
  have rV : Run B (.assign "v" (.get "removed" (.var "i"))) σ σ₁ 3 := by
    apply Run.assign
    apply evalB_get (evalB_var (by rw [hi]; exact hiB))
    · simpa [hremoved, hi, hx] using getElem?_arrOf removed him
    · exact hxB
  have rR : Run B (.assign "r" (.get "removedRep" (.var "i"))) σ₁ σ₂ 3 := by
    apply Run.assign
    apply evalB_get (evalB_var (by simp [σ₁, hi]; exact hiB))
    · simpa [σ₁, hrepresentative, hi, hr] using
        getElem?_arrOf representative him
    · exact hrB
  have rStoreNext : Run B
      (.store "nextVertex" (.var "v") (.get "nextVertex" (.var "r")))
      σ₂ σ₃ 4 := by
    apply Run.store
    · simpa [σ₂, σ₁] using (evalB_var (B := B) (x := "v") (σ := σ₂) hxB)
    · apply evalB_get (evalB_var (by simp [σ₂, σ₁]; exact hrB))
      · simpa [σ₂, σ₁, hnext] using getElem?_arrOf next hrn
      · exact hnextB
    · rw [show σ₂.arrs "nextVertex" = arrOf n next by simp [σ₂, σ₁, hnext], length_arrOf]
      exact hxm
  have rStoreRep : Run B
      (.store "nextVertex" (.var "r") (.var "v")) σ₃ σ₄ 3 := by
    apply Run.store
    · simpa [σ₃, σ₂, σ₁] using (evalB_var (B := B) (x := "r") (σ := σ₃) hrB)
    · simpa [σ₃, σ₂, σ₁] using (evalB_var (B := B) (x := "v") (σ := σ₃) hxB)
    · rw [show σ₃.arrs "nextVertex" =
        (arrOf n next).set x (next r) by simp [σ₃, σ₂, σ₁, hnext], List.length_set,
        length_arrOf]
      exact hrn
  have rInc : Run B (inc "i") σ₄ σ₅ 4 := by
    apply Run.assign
    have hi4 : σ₄.vars "i" = i := by simp [σ₄, σ₃, σ₂, σ₁, hi]
    have hi4B : σ₄.vars "i" < B := by rw [hi4]; exact hiB
    have hival : (Expr.var "i").evalB B σ₄ = some i := by
      rw [evalB_var hi4B, hi4]
    exact evalB_bin hival (evalB_lit (by omega)) hiNextB
  have hrun : Run B linkedInsertBody σ σ₅ 17 := by
    simpa [linkedInsertBody, seqs, inc] using
      rV.seq (rR.seq (rStoreNext.seq (rStoreRep.seq rInc)))
  have hremovedFrame : σ₅.arrs "removed" = σ.arrs "removed" :=
    hrun.frame_arr "removed" (by decide)
  have hrepresentativeFrame : σ₅.arrs "removedRep" = σ.arrs "removedRep" :=
    hrun.frame_arr "removedRep" (by decide)
  have hiendFrame : σ₅.vars "iend" = σ.vars "iend" :=
    hrun.frame_var "iend" (by decide)
  have hheadFrame : σ₅.vars "head" = σ.vars "head" :=
    hrun.frame_var "head" (by decide)
  have hinpFrame : σ₅.inp = σ.inp := hrun.frame_inp (by decide)
  have houtFrame : σ₅.out = σ.out :=
    hrun.out_eq (by simp [linkedInsertBody, seqs, inc, Com.NoWrite])
  have harr : σ₅.arrs "nextVertex" = arrOf n (writeAfter next r x) := by
    have hσ₃arr : σ₃.arrs "nextVertex" =
        (arrOf n next).set x (next r) := by simp [σ₃, σ₂, σ₁, hnext]
    have hσ₄arr : σ₄.arrs "nextVertex" =
        ((arrOf n next).set x (next r)).set r x := by
      simp [σ₄, hσ₃arr]
    rw [show σ₅.arrs "nextVertex" = σ₄.arrs "nextVertex" by simp [σ₅], hσ₄arr]
    rw [set_arrOf, set_arrOf]
    apply arrOf_congr
    intro k hk
    simp [writeAfter, Function.update]
  refine ⟨σ₅, hrun, ?_⟩
  exact ⟨by simp [σ₅, σ₄, σ₃, σ₂, σ₁],
    by simp [σ₅, σ₄, σ₃, σ₂, σ₁],
    by simp [σ₅, σ₄, σ₃, σ₂, σ₁], harr, hremovedFrame,
    hrepresentativeFrame, hiendFrame, hheadFrame, hinpFrame, houtFrame⟩

/-- Execute the literal `i < iend` loop.  Its cost is linear in the log
interval length; the invariant records each iteration's array writes as the
corresponding log-indexed prefix of `writeAfter` updates. -/
lemma linkedInsertLoop_run
    {B n m start stop : ℕ} {removed representative initialNext : ℕ → ℕ}
    {initialHead : ℕ} {initialInput initialOutput : List ℕ} {σ : Env}
    (hstart : σ.vars "i" = start) (hend : σ.vars "iend" = stop)
    (hstartStop : start ≤ stop) (hstop : stop < B)
    (hstopm : stop ≤ m) (hnB : n < B)
    (hremovedN : ∀ k < m, removed k < n)
    (hrepresentativeN : ∀ k < m, representative k < n)
    (hremoved : σ.arrs "removed" = arrOf m removed)
    (hrepresentative : σ.arrs "removedRep" = arrOf m representative)
    (hnext : σ.arrs "nextVertex" = arrOf n initialNext)
    (hnextB : ∀ k < n, initialNext k < B)
    (hhead : σ.vars "head" = initialHead)
    (hinp : σ.inp = initialInput) (hout : σ.out = initialOutput) :
    ∃ σ', Run B linkedInsertLoop σ σ' (21 * (stop - start) + 4) ∧
      σ'.vars "i" = stop ∧
      σ'.arrs "nextVertex" =
        arrOf n (writeLogPrefix representative removed start
          (stop - start) initialNext) ∧
      σ'.vars "head" = initialHead ∧
      σ'.inp = initialInput ∧ σ'.out = initialOutput := by
  let Inv := LinkedInsertInv B n m start stop removed representative
    initialNext initialHead initialInput initialOutput
  have hInv : Inv σ := by
    simp [Inv, LinkedInsertInv, writeLogPrefix, hstart, hend, hstartStop,
      hremoved, hrepresentative, hnext, hhead, hinp, hout]
    exact hnextB
  have hdef : ∀ τ, Inv τ → ∃ v,
      (Cond.lt (.var "i") (.var "iend")).evalB B τ = some v := by
    intro τ hτ
    simp only [Inv, LinkedInsertInv] at hτ
    rcases hτ with ⟨hlo, hle, hiend, _, _, _, _, _, _, _⟩
    have hiB : τ.vars "i" < B := by omega
    have hiendB : τ.vars "iend" < B := by rw [hiend]; exact hstop
    refine ⟨decide (τ.vars "i" < stop), ?_⟩
    simpa [hiend] using evalB_condLt (evalB_var hiB) (evalB_var hiendB)
  have hstep : ∀ τ, Inv τ →
      (Cond.lt (.var "i") (.var "iend")).evalB B τ = some true →
      ∃ τ', Run B linkedInsertBody τ τ' 17 ∧ Inv τ' ∧
        (fun ρ => stop - ρ.vars "i") τ' <
          (fun ρ => stop - ρ.vars "i") τ := by
    intro τ hτ hcond
    simp only [Inv, LinkedInsertInv] at hτ
    rcases hτ with ⟨hlo, hle, hiend, hrem, hrep, hnextCur, hcurB,
      hheadCur, hinpCur, houtCur⟩
    have hiLt : τ.vars "i" < stop := by
      have heval := evalB_condLt
        (evalB_var (by omega : τ.vars "i" < B))
        (evalB_var (by rw [hiend]; exact hstop))
      have hcond' : some (decide (τ.vars "i" < stop)) = some true := by
        rw [heval] at hcond
        simpa [hiend] using hcond
      have hdec : decide (τ.vars "i" < stop) = true := Option.some.inj hcond'
      exact of_decide_eq_true hdec
    let i := τ.vars "i"
    let cur := writeLogPrefix representative removed start (i - start) initialNext
    let x := removed i
    let r := representative i
    have him : i < m := by omega
    have hxN : x < n := hremovedN i him
    have hrN : r < n := hrepresentativeN i him
    have hiB : i < B := by omega
    have hiNextB : i + 1 < B := by omega
    have hxB : x < B := hxN.trans hnB
    have hrB : r < B := hrN.trans hnB
    have hcurEq : τ.arrs "nextVertex" = arrOf n cur := by
      simpa [cur, i] using hnextCur
    obtain ⟨τ', hrun, hi', hv', hr', hnext', hremoved', hrepresentative',
      hiend', hhead', hinp', hout'⟩ := linkedInsertBody_run
        (B := B) (n := n) (m := m) (i := i) (x := x) (r := r)
        (removed := removed) (representative := representative) (next := cur)
        (σ := τ) rfl hiB hiNextB hrem hrep hcurEq him rfl rfl hxN hrN
        (fun k hk => (hremovedN k hk).trans hnB)
        (fun k hk => (hrepresentativeN k hk).trans hnB) hcurB
    have hlen : (i + 1) - start = (i - start) + 1 := by omega
    have hprefix : start + (i - start) = i := by omega
    have hnextInv : τ'.arrs "nextVertex" =
        arrOf n (writeLogPrefix representative removed start
          ((τ'.vars "i") - start) initialNext) := by
      rw [hi', hlen, hnext', writeLogPrefix_succ, hprefix]
    have hnextInvB : ∀ k < n,
        writeLogPrefix representative removed start
          (τ'.vars "i" - start) initialNext k < B := by
      intro k hk
      rw [hi', hlen, writeLogPrefix_succ, hprefix]
      exact writeAfter_preserves_bound cur r x hrN hxB hcurB k hk
    have hinv' : Inv τ' := by
      simp only [Inv, LinkedInsertInv]
      refine ⟨?_, ?_, hiend'.trans hiend, hremoved'.trans hrem,
        hrepresentative'.trans hrep, hnextInv, hnextInvB,
        hhead'.trans hheadCur, hinp'.trans hinpCur, hout'.trans houtCur⟩
      · rw [hi']; omega
      · rw [hi']; omega
    refine ⟨τ', hrun, hinv', ?_⟩
    change stop - τ'.vars "i" < stop - τ.vars "i"
    rw [hi']
    omega
  obtain ⟨τ', hrun, hinv', hfalse⟩ :=
    Run.while_count Inv (fun τ => stop - τ.vars "i") 17
      hdef hstep hInv
  simp only [Inv, LinkedInsertInv] at hinv'
  rcases hinv' with ⟨hlo, hle, hiend, _, _, hnextFinal, _, hheadFinal,
    hinpFinal, houtFinal⟩
  have hfinal : τ'.vars "i" = stop := by
    have heval := evalB_condLt
      (evalB_var (by omega : τ'.vars "i" < B))
      (evalB_var (by rw [hiend]; exact hstop))
    rw [heval] at hfalse
    have hdec : decide (τ'.vars "i" < stop) = false := by
      simpa [hiend] using Option.some.inj hfalse
    have hnot : ¬ τ'.vars "i" < stop := of_decide_eq_false hdec
    omega
  refine ⟨τ', ?_, hfinal, ?_, hheadFinal, hinpFinal, houtFinal⟩
  · simpa [linkedInsertLoop, Cond.size, Expr.size, hstart] using hrun
  · simpa [hfinal] using hnextFinal

end Lax235315Proofs.Construction.LinkedSource
