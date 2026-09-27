import Lax235315Proofs.Construction.ReadKeys
import Mathlib.Tactic

/-! Source-level verification of the deletion log written at an accepted
Welzl reduction. -/

namespace Lax235315Proofs.Construction.RecordRemovedSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.ReadKeys (scanList)
open Lax235315Proofs.Construction.WelzlProgram

/-- Vertices recorded by the deletion pass in the scanned prefix. -/
def removedList (active next : ℕ → ℕ) (start : ℕ) : ℕ → List ℕ
  | 0 => []
  | count + 1 =>
      if active start = 1 ∧ next start = 0 then
        start :: removedList active next (start + 1) count
      else removedList active next (start + 1) count

/-- The same deletion list, paired with the representative selected by
`repA` for each recorded vertex. -/
def removedRepList (active next rep : ℕ → ℕ) (start : ℕ) (count : ℕ) : List ℕ :=
  (removedList active next start count).map rep

@[simp] lemma removedList_zero (active next : ℕ → ℕ) (start : ℕ) :
    removedList active next start 0 = [] := rfl

lemma removedList_step (active next : ℕ → ℕ) (start count : ℕ) :
    removedList active next start (count + 1) =
      removedList active next start count ++
        if active (start + count) = 1 ∧ next (start + count) = 0
        then [start + count] else [] := by
  induction count generalizing start with
  | zero => simp [removedList]
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega, removedList]
      rw [ih (start + 1)]
      have hs : start + 1 + count = start + (count + 1) := by omega
      rw [hs]
      by_cases h : active start = 1 ∧ next start = 0
      · simp [removedList, h]
      · simp [removedList, h]

lemma removedList_length_le (active next : ℕ → ℕ) (start count : ℕ) :
    (removedList active next start count).length ≤ count := by
  induction count generalizing start with
  | zero => simp [removedList]
  | succ count ih =>
      simp only [removedList]
      split
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih (start + 1))
      · exact (ih (start + 1)).trans (Nat.le_succ count)

lemma removedList_length_le_scanList
    (active next : ℕ → ℕ) (start count : ℕ) :
    (removedList active next start count).length ≤
      (scanList active start count).length := by
  induction count generalizing start with
  | zero => simp [removedList, scanList]
  | succ count ih =>
      by_cases ha : active start = 1
      · by_cases hn : next start = 0
        · have hdel : active start = 1 ∧ next start = 0 := ⟨ha, hn⟩
          simp only [removedList, if_pos hdel, scanList, if_pos ha,
            List.length_cons]
          exact Nat.succ_le_succ (ih (start + 1))
        · have hnot : ¬ (active start = 1 ∧ next start = 0) := by
            simp [ha, hn]
          simp only [removedList, if_neg hnot, scanList, if_pos ha,
            List.length_cons]
          exact (ih (start + 1)).trans (Nat.le_succ _)
      · have hnot : ¬ (active start = 1 ∧ next start = 0) := by
          simp [ha]
        simp only [removedList, if_neg hnot, scanList, if_neg ha]
        exact ih (start + 1)

lemma removedList_capacity_of_scanList
    (active next : ℕ → ℕ) (base n : ℕ)
    (hcapacity : base + (scanList active 0 n).length ≤ n) :
    base + (removedList active next 0 n).length ≤ n := by
  have hle := removedList_length_le_scanList active next 0 n
  omega

lemma removedList_append (active next : ℕ → ℕ) (start first second : ℕ) :
    removedList active next start (first + second) =
      removedList active next start first ++
        removedList active next (start + first) second := by
  induction first generalizing start with
  | zero => simp [removedList]
  | succ first ih =>
      rw [Nat.succ_add, removedList, ih (start + 1)]
      have hs : start + 1 + first = start + (first + 1) := by omega
      rw [hs]
      by_cases h : active start = 1 ∧ next start = 0
      · simp [removedList, h]
      · simp [removedList, h]

lemma removedList_zero_succ (active next : ℕ → ℕ) (v : ℕ) :
    removedList active next 0 (v + 1) =
      removedList active next 0 v ++
        if active v = 1 ∧ next v = 0 then [v] else [] := by
  rw [removedList_append active next 0 v 1]
  simp [removedList]

/-- One literal iteration of the deletion scan. -/
def recordRemovedBody : Com :=
  seqs [
    .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
      (.ite (.eq (.get "nextA" (.var "v")) (.lit 0))
        (seqs [
          .store "removed" (.var "removedCount") (.var "v"),
          .store "removedRep" (.var "removedCount")
            (.get "repA" (.var "v")),
          inc "removedCount"])
        .skip)
      .skip,
    inc "v"]

/-- Each scan turn appends the current vertex and its selected representative
precisely when `activeA[v]=1` and `nextA[v]=0`. -/
lemma recordRemovedBody_run {B n i count cap : ℕ} {σ : Env}
    {active next rep : ℕ → ℕ}
    (hvi : σ.vars "v" = i) (hci : σ.vars "removedCount" = count)
    (hi : i < n) (hcount : active i = 1 → next i = 0 → count < cap)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hnext : σ.arrs "nextA" = arrOf n next)
    (hrep : σ.arrs "repA" = arrOf n rep)
    (hremoved : (σ.arrs "removed").length = cap)
    (hremovedRep : (σ.arrs "removedRep").length = cap)
    (hiB : i < B) (hcountB : count < B) (honeB : 1 < B)
    (hactiveB : active i < B) (hnextB : next i < B)
    (hrepB : rep i < B)
    (hcountSuccB : active i = 1 → next i = 0 → count + 1 < B)
    (hiSuccB : i + 1 < B) :
    ∃ σ', Run B recordRemovedBody σ σ' 40 ∧
      σ'.vars "v" = i + 1 ∧
      σ'.vars "removedCount" = count +
        (if active i = 1 ∧ next i = 0 then 1 else 0) ∧
      (σ'.arrs "removed" =
        if active i = 1 ∧ next i = 0 then
          (σ.arrs "removed").set count i else σ.arrs "removed") ∧
      (σ'.arrs "removedRep" =
        if active i = 1 ∧ next i = 0 then
          (σ.arrs "removedRep").set count (rep i) else σ.arrs "removedRep") := by
  have hzeroB : 0 < B := by omega
  have hvEval : (Expr.var "v").evalB B σ = some i := by
    have hbound : σ.vars "v" < B := by rw [hvi]; exact hiB
    simpa [hvi] using (evalB_var (B := B) (x := "v") (σ := σ) hbound)
  have hcEval : (Expr.var "removedCount").evalB B σ = some count := by
    have hbound : σ.vars "removedCount" < B := by rw [hci]; exact hcountB
    simpa [hci] using
      (evalB_var (B := B) (x := "removedCount") (σ := σ) hbound)
  have hactiveEval :
      (Expr.get "activeA" (.var "v")).evalB B σ = some (active i) :=
    evalB_get hvEval (by rw [hactive, getElem?_arrOf active hi]) hactiveB
  have hnextEval :
      (Expr.get "nextA" (.var "v")).evalB B σ = some (next i) :=
    evalB_get hvEval (by rw [hnext, getElem?_arrOf next hi]) hnextB
  have htestA :
      (Cond.eq (.get "activeA" (.var "v")) (.lit 1)).evalB B σ =
        some (active i == 1) := by
    exact evalB_condEq hactiveEval (evalB_lit (by omega))
  by_cases ha : active i = 1
  · have htestA' :
        (Cond.eq (.get "activeA" (.var "v")) (.lit 1)).evalB B σ = some true := by
      simpa [ha] using htestA
    have hrepEval :
        (Expr.get "repA" (.var "v")).evalB B σ = some (rep i) :=
      evalB_get hvEval (by rw [hrep, getElem?_arrOf rep hi]) hrepB
    have htestN :
        (Cond.eq (.get "nextA" (.var "v")) (.lit 0)).evalB B σ =
          some (next i == 0) := by
      exact evalB_condEq hnextEval (evalB_lit hzeroB)
    by_cases hn : next i = 0
    · have htestN' :
          (Cond.eq (.get "nextA" (.var "v")) (.lit 0)).evalB B σ = some true := by
        simpa [hn] using htestN
      let σ₁ := σ.setArr "removed" count i
      have r₁ : Run B (.store "removed" (.var "removedCount") (.var "v"))
          σ σ₁ 3 := by
        apply Run.store hcEval hvEval
        simpa [hremoved] using hcount ha hn
      let σ₂ := σ₁.setArr "removedRep" count (rep i)
      have hcEval₁ :
          (Expr.var "removedCount").evalB B σ₁ = some count := by
        simpa [σ₁] using hcEval
      have hrepEval₁ :
          (Expr.get "repA" (.var "v")).evalB B σ₁ = some (rep i) := by
        simpa [σ₁] using hrepEval
      have r₂ : Run B
          (.store "removedRep" (.var "removedCount") (.get "repA" (.var "v")))
          σ₁ σ₂ 4 := by
        apply Run.store hcEval₁ hrepEval₁
        simpa [σ₁, hremovedRep] using hcount ha hn
      let σ₃ := σ₂.setVar "removedCount" (count + 1)
      have r₃ : Run B (inc "removedCount") σ₂ σ₃ 4 := by
        apply Run.assign
        apply evalB_bin
        · have hcountB₂ : σ₂.vars "removedCount" < B := by
            simpa [σ₂, σ₁, hci] using hcountB
          simpa [σ₂, σ₁, hci] using (evalB_var hcountB₂)
        · exact evalB_lit (by omega)
        · exact hcountSuccB ha hn
      have rbranch : Run B
          (seqs [
            .store "removed" (.var "removedCount") (.var "v"),
            .store "removedRep" (.var "removedCount") (.get "repA" (.var "v")),
            inc "removedCount"]) σ σ₃ 11 := by
        simpa [seqs] using r₁.seq (r₂.seq r₃)
      have rinner : Run B
          (.ite (.eq (.get "nextA" (.var "v")) (.lit 0))
            (seqs [
              .store "removed" (.var "removedCount") (.var "v"),
              .store "removedRep" (.var "removedCount") (.get "repA" (.var "v")),
              inc "removedCount"]) .skip) σ σ₃ 16 := by
        exact (Run.ite_true htestN' rbranch).mono (by norm_num [Cond.size])
      have router : Run B
          (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
            (.ite (.eq (.get "nextA" (.var "v")) (.lit 0))
              (seqs [
                .store "removed" (.var "removedCount") (.var "v"),
                .store "removedRep" (.var "removedCount") (.get "repA" (.var "v")),
                inc "removedCount"]) .skip) .skip) σ σ₃ 21 := by
        exact (Run.ite_true htestA' rinner).mono (by norm_num [Cond.size])
      let σ₄ := σ₃.setVar "v" (i + 1)
      have rv : Run B (inc "v") σ₃ σ₄ 4 := by
        apply Run.assign
        apply evalB_bin
        · have hiB₃ : σ₃.vars "v" < B := by
            simpa [σ₃, σ₂, σ₁, hvi] using hiB
          simpa [σ₃, σ₂, σ₁, hvi] using (evalB_var hiB₃)
        · exact evalB_lit (by omega)
        · exact hiSuccB
      have rr : Run B recordRemovedBody σ σ₄ 40 := by
        simpa [recordRemovedBody, seqs] using (router.seq rv).mono (by omega)
      refine ⟨σ₄, rr, by simp [σ₄, σ₃, σ₂, σ₁], ?_, ?_, ?_⟩
      · simp [σ₄, σ₃, hn, ha]
      · simp [σ₄, σ₃, σ₂, σ₁, ha, hn]
      · simp [σ₄, σ₃, σ₂, σ₁, ha, hn]
    · have htestN' :
        (Cond.eq (.get "nextA" (.var "v")) (.lit 0)).evalB B σ = some false := by
        rw [htestN, beq_eq_false_iff_ne.mpr hn]
      let σ₄ := σ.setVar "v" (i + 1)
      have rv : Run B (inc "v") σ σ₄ 4 := by
        apply Run.assign
        apply evalB_bin
        · exact hvEval
        · exact evalB_lit (by omega)
        · exact hiSuccB
      have rinner : Run B
          (.ite (.eq (.get "nextA" (.var "v")) (.lit 0))
            (seqs [
              .store "removed" (.var "removedCount") (.var "v"),
              .store "removedRep" (.var "removedCount") (.get "repA" (.var "v")),
              inc "removedCount"]) .skip) σ σ 6 :=
        (Run.ite_false htestN' Run.skip).mono (by norm_num)
      have router : Run B
          (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
            (.ite (.eq (.get "nextA" (.var "v")) (.lit 0))
              (seqs [
                .store "removed" (.var "removedCount") (.var "v"),
                .store "removedRep" (.var "removedCount") (.get "repA" (.var "v")),
                inc "removedCount"]) .skip) .skip) σ σ 11 :=
        (Run.ite_true htestA' rinner).mono (by norm_num [Cond.size])
      have rr : Run B recordRemovedBody σ σ₄ 40 := by
        simpa [recordRemovedBody, seqs] using (router.seq rv).mono (by omega)
      refine ⟨σ₄, rr, by simp [σ₄], ?_, ?_, ?_⟩
      · simpa [σ₄, ha, hn] using hci
      · simp [σ₄, ha, hn]
      · simp [σ₄, ha, hn]
  · have htestA' :
        (Cond.eq (.get "activeA" (.var "v")) (.lit 1)).evalB B σ = some false := by
      rw [htestA, beq_eq_false_iff_ne.mpr ha]
    let σ₄ := σ.setVar "v" (i + 1)
    have rv : Run B (inc "v") σ σ₄ 4 := by
      apply Run.assign
      apply evalB_bin
      · exact hvEval
      · exact evalB_lit (by omega)
      · exact hiSuccB
    have router : Run B
        (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
          (.ite (.eq (.get "nextA" (.var "v")) (.lit 0))
            (seqs [
              .store "removed" (.var "removedCount") (.var "v"),
              .store "removedRep" (.var "removedCount") (.get "repA" (.var "v")),
              inc "removedCount"]) .skip) .skip) σ σ 6 :=
      (Run.ite_false htestA' Run.skip).mono (by norm_num [Cond.size])
    have rr : Run B recordRemovedBody σ σ₄ 40 := by
      simpa [recordRemovedBody, seqs] using (router.seq rv).mono (by omega)
    refine ⟨σ₄, rr, by simp [σ₄], ?_, ?_, ?_⟩
    · simpa [σ₄, ha] using hci
    · simp [σ₄, ha]
    · simp [σ₄, ha]

/-- State invariant for the deletion scan. The occupied suffix of each log
is exactly the filtered scan prefix, while every earlier log cell retains
its value from before this reduction. -/
def RecordInv (n base round : ℕ) (active next rep oldRemoved oldRemovedRep : ℕ → ℕ)
    (roundStarts : List ℕ) (τ : Env) : Prop :=
  ∃ r rr,
    τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧ τ.vars "round" = round ∧
    τ.vars "removedCount" = base +
      (removedList active next 0 (τ.vars "v")).length ∧
    τ.arrs "activeA" = arrOf n active ∧
    τ.arrs "nextA" = arrOf n next ∧
    τ.arrs "repA" = arrOf n rep ∧
    τ.arrs "roundStart" = roundStarts ∧
    τ.arrs "removed" = arrOf n r ∧
    τ.arrs "removedRep" = arrOf n rr ∧
    (∀ j < base, r j = oldRemoved j) ∧
    (∀ j < (removedList active next 0 (τ.vars "v")).length,
      r (base + j) = (removedList active next 0 (τ.vars "v")).getD j 0) ∧
    (∀ j < base, rr j = oldRemovedRep j) ∧
    (∀ j < (removedList active next 0 (τ.vars "v")).length,
      rr (base + j) =
        (removedRepList active next rep 0 (τ.vars "v")).getD j 0)

lemma removedList_prefix_length {active next : ℕ → ℕ} {v n : ℕ} (hv : v ≤ n) :
    (removedList active next 0 v).length ≤
      (removedList active next 0 n).length := by
  rw [← Nat.add_sub_of_le hv, removedList_append active next 0 v (n - v)]
  simp

lemma removedList_current_in_total {active next : ℕ → ℕ} {v n : ℕ}
    (hv : v < n) (ha : active v = 1) (hn : next v = 0) :
    (removedList active next 0 v).length + 1 ≤
      (removedList active next 0 n).length := by
  have hsplit := removedList_append active next 0 (v + 1) (n - (v + 1))
  have hvn : v + 1 + (n - (v + 1)) = n := by omega
  rw [hvn] at hsplit
  rw [removedList_zero_succ active next v] at hsplit
  simp [ha, hn] at hsplit
  have hlen := congrArg List.length hsplit
  simp at hlen
  omega

lemma append_getD_left {α : Type} (xs ys : List α) (i : ℕ) (d : α)
    (hi : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

lemma append_getD_last {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD xs.length d = x := by
  simp [List.getD_eq_getElem?_getD]

lemma recordRemoved_body_spec {B n base round : ℕ}
    {active next rep oldRemoved oldRemovedRep : ℕ → ℕ}
    {roundStarts : List ℕ}
    (hnB : n < B)
    (hactiveB : ∀ i < n, active i < B)
    (hnextB : ∀ i < n, next i < B)
    (hrepB : ∀ i < n, rep i < B)
    (hcapacity : base + (removedList active next 0 n).length ≤ n) :
    Spec B
      (fun τ => RecordInv n base round active next rep oldRemoved oldRemovedRep
        roundStarts τ ∧ τ.vars "v" < n)
      recordRemovedBody
      (fun τ τ' =>
        RecordInv n base round active next rep oldRemoved oldRemovedRep roundStarts τ' ∧
        τ'.vars "v" = τ.vars "v" + 1) 40 := by
  intro τ ⟨hI, hvlt⟩
  rcases hI with ⟨r, rr, hvle, hn, hround, hcount, hactive, hnext, hrep,
    hroundStarts, hremoved, hremovedRep, hprefix, hsuffix, hprefixRep,
    hsuffixRep⟩
  let i := τ.vars "v"
  let count := τ.vars "removedCount"
  have hi : i < n := by simpa [i] using hvlt
  have hprefixLen : (removedList active next 0 i).length ≤
      (removedList active next 0 n).length :=
    removedList_prefix_length (by simpa [i] using hvle)
  have hcountLe : count ≤ n := by
    rw [show count = base + (removedList active next 0 i).length by
      simp [count, i, hcount]]
    omega
  have hcountB : count < B := hcountLe.trans_lt hnB
  have hiB : i < B := hi.trans hnB
  have hiSuccB : i + 1 < B := by omega
  have hcountWhen : active i = 1 → next i = 0 → count < n := by
    intro ha hnxt
    have htotal := removedList_current_in_total hi ha hnxt
    rw [show count = base + (removedList active next 0 i).length by
      simp [count, i, hcount]]
    omega
  have hcountSuccWhen : active i = 1 → next i = 0 → count + 1 < B := by
    intro ha hnxt
    have hc := hcountWhen ha hnxt
    omega
  have hrlen : (τ.arrs "removed").length = n := by
    rw [hremoved, length_arrOf]
  have hrrlen : (τ.arrs "removedRep").length = n := by
    rw [hremovedRep, length_arrOf]
  have hactiveBi : active i < B := hactiveB i hi
  have hnextBi : next i < B := hnextB i hi
  have hrepBi : rep i < B := hrepB i hi
  obtain ⟨τ', hr, hv', hcount', hremoved', hremovedRep'⟩ :=
    recordRemovedBody_run (σ := τ) (active := active) (next := next) (rep := rep)
      (hvi := rfl) (hci := rfl) hi (hcountWhen) hactive hnext hrep hrlen hrrlen
      hiB hcountB (by omega) hactiveBi hnextBi hrepBi hcountSuccWhen hiSuccB
  by_cases hhit : active i = 1 ∧ next i = 0
  · have hlist : removedList active next 0 (i + 1) =
        removedList active next 0 i ++ [i] := by
      rw [removedList_zero_succ]
      simp [hhit]
    have hrepList : removedRepList active next rep 0 (i + 1) =
        removedRepList active next rep 0 i ++ [rep i] := by
      simp [removedRepList, hlist]
    let r' := upd r count i
    let rr' := upd rr count (rep i)
    have hhit' : active (τ.vars "v") = 1 ∧ next (τ.vars "v") = 0 := by
      simpa [i] using hhit
    simp [hhit'] at hremoved' hremovedRep'
    have hremovedShape : τ'.arrs "removed" = arrOf n r' := by
      rw [hremoved', hremoved, set_arrOf_eq_upd]
    have hrepShape : τ'.arrs "removedRep" = arrOf n rr' := by
      rw [hremovedRep', hremovedRep, set_arrOf_eq_upd]
    have hcountEq : count = base + (removedList active next 0 i).length := by
      simpa [count, i] using hcount
    have hiv' : τ'.vars "v" = i + 1 := by simpa [i] using hv'
    have hcount'Eq : τ'.vars "removedCount" =
        base + (removedList active next 0 (τ'.vars "v")).length := by
      calc
        τ'.vars "removedCount" = τ.vars "removedCount" + 1 := by
          simpa [hhit'] using hcount'
        _ = base + (removedList active next 0 i).length + 1 := by rw [hcount]
        _ = base + (removedList active next 0 (τ'.vars "v")).length := by
          rw [hiv', hlist]
          simp
          omega
    refine ⟨τ', hr, ⟨⟨r', rr', ?_, ?_, ?_, hcount'Eq, ?_, ?_, ?_, ?_,
      hremovedShape, hrepShape, ?_, ?_, ?_, ?_⟩, hv'⟩⟩
    · have : i + 1 ≤ n := Nat.succ_le_of_lt hi
      simpa [i, hv'] using this
    · exact (hr.frame_var "n" (by decide)).trans hn
    · exact (hr.frame_var "round" (by decide)).trans hround
    · exact (hr.frame_arr "activeA" (by decide)).trans hactive
    · exact (hr.frame_arr "nextA" (by decide)).trans hnext
    · exact (hr.frame_arr "repA" (by decide)).trans hrep
    · exact (hr.frame_arr "roundStart" (by decide)).trans hroundStarts
    · intro j hj
      have hne : j ≠ count := by rw [hcountEq]; omega
      simpa [r', upd, hne] using hprefix j hj
    · intro j hj
      have hnewLen : (removedList active next 0 (τ'.vars "v")).length =
          (removedList active next 0 i).length + 1 := by
        rw [hiv', hlist, List.length_append]
        simp
      have hjcases : j < (removedList active next 0 i).length ∨
          j = (removedList active next 0 i).length := by omega
      rcases hjcases with hjold | rfl
      · have hne : base + j ≠ count := by rw [hcountEq]; omega
        rw [hiv', hlist, append_getD_left _ _ _ _ hjold]
        simpa [r', upd, hne] using hsuffix j hjold
      · rw [hiv', hlist, append_getD_last]
        simp [r', hcountEq]
    · intro j hj
      have hne : j ≠ count := by rw [hcountEq]; omega
      simpa [rr', upd, hne] using hprefixRep j hj
    · intro j hj
      have hnewLen : (removedList active next 0 (τ'.vars "v")).length =
          (removedList active next 0 i).length + 1 := by
        rw [hiv', hlist, List.length_append]
        simp
      have hjcases : j < (removedList active next 0 i).length ∨
          j = (removedList active next 0 i).length := by omega
      rcases hjcases with hjold | rfl
      · have hne : base + j ≠ count := by rw [hcountEq]; omega
        have hget :
            (removedRepList active next rep 0 i ++ [rep i]).getD j 0 =
          (removedRepList active next rep 0 i).getD j 0 :=
          append_getD_left _ _ j 0 (by simpa [removedRepList] using hjold)
        rw [hiv', hrepList, hget]
        simpa [rr', upd, hne] using hsuffixRep j hjold
      · have hget :
            (removedRepList active next rep 0 i ++ [rep i]).getD
                (removedRepList active next rep 0 i).length 0 = rep i :=
          append_getD_last _ _ _
        have hlenRep : (removedRepList active next rep 0 i).length =
            (removedList active next 0 i).length := by simp [removedRepList]
        rw [hiv', hrepList]
        have hget' :
            (removedRepList active next rep 0 i ++ [rep i]).getD
                (removedList active next 0 i).length 0 = rep i := by
          rw [← hlenRep]
          exact hget
        rw [hget']
        simp [rr', hcountEq]
  · have hlist : removedList active next 0 (i + 1) =
        removedList active next 0 i := by
      rw [removedList_zero_succ]
      simp [hhit]
    have hrepList : removedRepList active next rep 0 (i + 1) =
        removedRepList active next rep 0 i := by
      simp [removedRepList, hlist]
    have hhit' : ¬ (active (τ.vars "v") = 1 ∧ next (τ.vars "v") = 0) := by
      simpa [i] using hhit
    have hcountEq : count = base + (removedList active next 0 i).length := by
      simpa [count, i] using hcount
    simp [hhit'] at hremoved' hremovedRep' hcount'
    have hcount'Eq : τ'.vars "removedCount" =
        base + (removedList active next 0 (τ'.vars "v")).length := by
      simpa [hcount, hhit', hlist, hv', i] using hcount'
    have hiv' : τ'.vars "v" = i + 1 := by simpa [i] using hv'
    refine ⟨τ', hr, ⟨⟨r, rr, ?_, ?_, ?_, hcount'Eq, ?_, ?_, ?_, ?_,
      ?_, ?_, hprefix, ?_, hprefixRep, ?_⟩, hv'⟩⟩
    · have : i + 1 ≤ n := Nat.succ_le_of_lt hi
      simpa [i, hv'] using this
    · exact (hr.frame_var "n" (by decide)).trans hn
    · exact (hr.frame_var "round" (by decide)).trans hround
    · exact (hr.frame_arr "activeA" (by decide)).trans hactive
    · exact (hr.frame_arr "nextA" (by decide)).trans hnext
    · exact (hr.frame_arr "repA" (by decide)).trans hrep
    · exact (hr.frame_arr "roundStart" (by decide)).trans hroundStarts
    · exact hremoved'.trans hremoved
    · exact hremovedRep'.trans hremovedRep
    · simpa [hlist, hiv'] using hsuffix
    · simpa [hrepList, hlist, hiv', i] using hsuffixRep

lemma recordRemoved_run {B n base round roundCap : ℕ} {σ : Env}
    {active next rep oldRemoved oldRemovedRep : ℕ → ℕ}
    (hn : σ.vars "n" = n) (hround : σ.vars "round" = round)
    (hbase : σ.vars "removedCount" = base)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hnext : σ.arrs "nextA" = arrOf n next)
    (hrep : σ.arrs "repA" = arrOf n rep)
    (hremoved : σ.arrs "removed" = arrOf n oldRemoved)
    (hremovedRep : σ.arrs "removedRep" = arrOf n oldRemovedRep)
    (hroundStarts : (σ.arrs "roundStart").length = roundCap)
    (hroundRange : round < roundCap)
    (hnB : n < B) (hroundB : round < B) (hbaseB : base < B)
    (hactiveB : ∀ i < n, active i < B)
    (hnextB : ∀ i < n, next i < B)
    (hrepB : ∀ i < n, rep i < B)
    (hcapacity : base + (removedList active next 0 n).length ≤ n) :
    ∃ σ' removed' removedRep' roundStarts',
      Run B recordRemoved σ σ' (50 * (n + 1)) ∧
      σ'.vars "removedCount" = base +
        (removedList active next 0 n).length ∧
      σ'.vars "v" = n ∧ σ'.vars "n" = n ∧ σ'.vars "round" = round ∧
      σ'.arrs "removed" = arrOf n removed' ∧
      σ'.arrs "removedRep" = arrOf n removedRep' ∧
      σ'.arrs "roundStart" = roundStarts' ∧
      roundStarts' = (σ.arrs "roundStart").set round base ∧
      (∀ j < base, removed' j = oldRemoved j) ∧
      (∀ j < (removedList active next 0 n).length,
        removed' (base + j) = (removedList active next 0 n).getD j 0) ∧
      (∀ j < base, removedRep' j = oldRemovedRep j) ∧
      (∀ j < (removedList active next 0 n).length,
        removedRep' (base + j) =
          (removedRepList active next rep 0 n).getD j 0) := by
  let roundStarts' := (σ.arrs "roundStart").set round base
  let σ₁ := σ.setArr "roundStart" round base
  have rstore : Run B (.store "roundStart" (.var "round") (.var "removedCount"))
      σ σ₁ 3 := by
    apply Run.store
    · simpa [hround] using (evalB_var (B := B) (x := "round")
        (σ := σ) (by rw [hround]; exact hroundB))
    · simpa [hbase] using (evalB_var (B := B) (x := "removedCount")
        (σ := σ) (by rw [hbase]; exact hbaseB))
    · simpa [hroundStarts] using hroundRange
  let I := RecordInv n base round active next rep oldRemoved oldRemovedRep roundStarts'
  have hbody := recordRemoved_body_spec (B := B) (n := n) (base := base)
    (round := round) (active := active) (next := next) (rep := rep)
    (oldRemoved := oldRemoved) (oldRemovedRep := oldRemovedRep)
    (roundStarts := roundStarts') hnB hactiveB hnextB hrepB hcapacity
  have hloop := Spec.forRangeZero (B := B) "v" "n" I n 40 hnB
    (fun τ h => by rcases h with ⟨r, rr, hv, hn', hr, hc, ha, hnx, hp, hrs,
      hrem, hremrep, hpre, hsuf, hprerep, hsufrep⟩; exact hv)
    (fun τ h => by rcases h with ⟨r, rr, hv, hn', hr, hc, ha, hnx, hp, hrs,
      hrem, hremrep, hpre, hsuf, hprerep, hsufrep⟩; exact hn') hbody
  have hI0 : I (σ₁.setVar "v" 0) := by
    refine ⟨oldRemoved, oldRemovedRep,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₁]
    · simp [σ₁, hn]
    · simp [σ₁, hround]
    · simp [σ₁, hbase]
    · simpa [σ₁] using hactive
    · simpa [σ₁] using hnext
    · simpa [σ₁] using hrep
    · simp [roundStarts', σ₁]
    · simpa [σ₁] using hremoved
    · simpa [σ₁] using hremovedRep
    · intro j hj
      rfl
    · intro j hj
      simp at hj
    · constructor
      · intro j hj
        rfl
      · intro j hj
        simp at hj
  obtain ⟨σ₃, rloop, ⟨r', rr', hv3, hn3, hr3, hc3, ha3, hnxt3, hp3,
      hrs3, hremoved3, hremovedRep3, hprefix3, hsuffix3, hprefixRep3,
      hsuffixRep3⟩, hvn3⟩ := hloop.run hI0
  have hshape : recordRemoved =
      seqs [
        .store "roundStart" (.var "round") (.var "removedCount"),
        .assign "v" (.lit 0),
        .while (.lt (.var "v") (.var "n")) recordRemovedBody] := by
    simp [recordRemoved, recordRemovedBody, seqs, inc]
  have rrun : Run B recordRemoved σ σ₃ (50 * (n + 1)) := by
    rw [hshape]
    exact (rstore.seq rloop).mono (by omega)
  refine ⟨σ₃, r', rr', roundStarts', rrun, ?_, hvn3, hn3,
    hr3, hremoved3, hremovedRep3, hrs3, rfl, hprefix3, ?_, hprefixRep3, ?_⟩
  · simpa [hvn3] using hc3
  · simpa [hvn3] using hsuffix3
  · simpa [hvn3] using hsuffixRep3


end Lax235315Proofs.Construction.RecordRemovedSource
