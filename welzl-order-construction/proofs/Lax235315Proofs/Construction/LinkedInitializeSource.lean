import Lax235315Proofs.Construction.LinkedOutputSource
import Lax235315Proofs.Construction.ReadKeys
import Lax808846Proofs.Lib.Basic
import Mathlib.Tactic

/-! Bounded execution of the first pass of
`WelzlProgram.reconstructAndWrite`, which links the active vertices in
increasing order before the restoration passes begin. -/

namespace Lax235315Proofs.Construction.LinkedInitializeSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.LinkedReconstruction
open Lax235315Proofs.Construction.ReadKeys (scanList)
open Lax235315Proofs.Construction.WelzlProgram

/-- One literal iteration of the initial linked-list scan. -/
def linkedInitializeBody : Com :=
  seqs [
    .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
      (.ite (.eq (.var "last") (.var "n"))
        (.assign "head" (.var "v"))
        (.store "nextVertex" (.var "last") (.var "v")))
      .skip,
    .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
      (.assign "last" (.var "v")) .skip,
    inc "v"]

/-- The literal initial excerpt of `reconstructAndWrite`, through the first
scan and before the restoration loop. -/
def linkedInitialize : Com :=
  seqs [
    .assign "head" (.var "n"),
    .assign "last" (.var "n"),
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n")) linkedInitializeBody]

lemma linkedInitialize_eq_source_excerpt :
    linkedInitialize =
      seqs [
        .assign "head" (.var "n"),
        .assign "last" (.var "n"),
        .assign "v" (.lit 0),
        .while (.lt (.var "v") (.var "n")) <|
          seqs [
            .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
              (.ite (.eq (.var "last") (.var "n"))
                (.assign "head" (.var "v"))
                (.store "nextVertex" (.var "last") (.var "v")))
              .skip,
            .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
              (.assign "last" (.var "v")) .skip,
              inc "v"]] := rfl

lemma linkedInitializeBody_run
    {B n v : ℕ} {σ : Env} {active next : ℕ → ℕ}
    (hv : σ.vars "v" = v) (hn : σ.vars "n" = n)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hvn : v < n) (hnB : n < B)
    (hactiveB : active v < B) (hnextB : ∀ k < n, next k < B)
    (hlastB : σ.vars "last" < B)
    (hlastRange : σ.vars "last" = n ∨ σ.vars "last" < n) :
    ∃ σ' next', Run B linkedInitializeBody σ σ' 24 ∧
      σ'.vars "v" = v + 1 ∧ σ'.vars "n" = n ∧
      σ'.vars "head" =
        (if active v = 1 ∧ σ.vars "last" = n then v else σ.vars "head") ∧
      (if active v = 1 then σ'.vars "last" = v else
        σ'.vars "last" = σ.vars "last") ∧
      σ'.arrs "nextVertex" = arrOf n next' ∧
      (active v = 1 ∧ σ.vars "last" ≠ n →
        next' = upd next (σ.vars "last") v) ∧
      (active v = 1 ∧ σ.vars "last" = n ∨ active v ≠ 1 → next' = next) ∧
      (∀ k < n, next' k < B) := by
  have hvB : v < B := hvn.trans hnB
  have hactiveGet : (σ.arrs "activeA")[v]? = some (active v) := by
    rw [hactive]
    exact getElem?_arrOf active hvn
  have hactiveEval : (Expr.get "activeA" (.var "v")).evalB B σ =
      some (active v) := by
    exact evalB_get (by rw [evalB_var (by rw [hv]; exact hvB), hv]) hactiveGet hactiveB
  have hact : (Cond.eq (.get "activeA" (.var "v")) (.lit 1)).evalB B σ =
      some (active v == 1) := by
    exact evalB_condEq hactiveEval (evalB_lit (by omega))
  have hlastEq : (Cond.eq (.var "last") (.var "n")).evalB B σ =
      some (σ.vars "last" == n) := by
    exact evalB_condEq (evalB_var hlastB)
      (by rw [evalB_var (by rw [hn]; exact hnB), hn])
  by_cases ha : active v = 1
  · by_cases hln : σ.vars "last" = n
    · let σ₁ := σ.setVar "head" v
      let σ₂ := σ₁.setVar "last" v
      let σ₃ := σ₂.setVar "v" (v + 1)
      have rHead : Run B (.assign "head" (.var "v")) σ σ₁ 2 := by
        exact Run.assign (by rw [evalB_var (by rw [hv]; exact hvB), hv])
      have rFirst : Run B
          (.ite (.eq (.var "last") (.var "n"))
            (.assign "head" (.var "v"))
            (.store "nextVertex" (.var "last") (.var "v"))) σ σ₁ 6 := by
        apply (Run.ite_true (by simpa [hln] using hlastEq) rHead).mono
        simp [Cond.size, Expr.size]
      have rOuter : Run B
          (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
            (.ite (.eq (.var "last") (.var "n"))
              (.assign "head" (.var "v"))
              (.store "nextVertex" (.var "last") (.var "v"))) .skip)
          σ σ₁ 11 := by
        apply (Run.ite_true (by simpa [ha] using hact) rFirst).mono
        simp [Cond.size, Expr.size]
      have rLast : Run B
          (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
            (.assign "last" (.var "v")) .skip) σ₁ σ₂ 7 := by
        have hact₁ : (Cond.eq (.get "activeA" (.var "v")) (.lit 1)).evalB B σ₁ =
            some true := by simpa [σ₁, ha] using hact
        have hvEval : (Expr.var "v").evalB B σ₁ = some v := by
          simpa [σ₁] using
            (show (Expr.var "v").evalB B σ = some v from
              by rw [evalB_var (by rw [hv]; exact hvB), hv])
        have rAssign : Run B (.assign "last" (.var "v")) σ₁ σ₂ 2 :=
          Run.assign hvEval
        apply (Run.ite_true hact₁ rAssign).mono
        norm_num [Cond.size, Expr.size]
      have rInc : Run B (inc "v") σ₂ σ₃ 4 := by
        apply Run.assign
        have hv₂ : σ₂.vars "v" = v := by simp [σ₂, σ₁, hv]
        have hv₂B : σ₂.vars "v" < B := by rw [hv₂]; omega
        have hv₂eval : (Expr.var "v").evalB B σ₂ = some v := by
          rw [evalB_var hv₂B, hv₂]
        have hsum : Bop.add.apply v 1 < B := by
          change v + 1 < B
          omega
        simpa [inc, Bop.apply] using
          evalB_bin hv₂eval (evalB_lit (by omega)) hsum
      have rbody : Run B linkedInitializeBody σ σ₃ 24 := by
        have := rOuter.seq (rLast.seq rInc)
        simpa [linkedInitializeBody, seqs, inc, σ₁, σ₂, σ₃] using
          this.mono (by omega)
      refine ⟨σ₃, next, rbody, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ₃, σ₂, σ₁]
      · simp [σ₃, σ₂, σ₁, hn]
      · simp [σ₃, σ₂, σ₁, ha, hln]
      · simp [σ₃, σ₂, σ₁, ha]
      · simpa [σ₃, σ₂, σ₁]
      · intro ⟨_, hne⟩
        exact (hne hln).elim
      · intro _
        rfl
      · intro k hk
        exact hnextB k hk
    · have hlastLt : σ.vars "last" < n := by
        rcases hlastRange with h | h
        · exact (hln h).elim
        · exact h
      let σ₁ := σ.setArr "nextVertex" (σ.vars "last") v
      let σ₂ := σ₁.setVar "last" v
      let σ₃ := σ₂.setVar "v" (v + 1)
      let next' := upd next (σ.vars "last") v
      have rStore : Run B
          (.store "nextVertex" (.var "last") (.var "v")) σ σ₁ 4 := by
        have hlen : (σ.arrs "nextVertex").length = n := by
          rw [hnext]
          simp
        have hraw := Run.store (evalB_var hlastB)
          (by rw [evalB_var (by rw [hv]; exact hvB), hv])
          (by rw [hlen]; exact hlastLt)
        simpa [σ₁, Expr.size] using hraw.mono (by norm_num [Expr.size])
      have rFirst : Run B
          (.ite (.eq (.var "last") (.var "n"))
            (.assign "head" (.var "v"))
            (.store "nextVertex" (.var "last") (.var "v"))) σ σ₁ 8 := by
        apply (Run.ite_false (by simpa [hln] using hlastEq) rStore).mono
        simp [Cond.size, Expr.size]
      have rOuter : Run B
          (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
            (.ite (.eq (.var "last") (.var "n"))
              (.assign "head" (.var "v"))
              (.store "nextVertex" (.var "last") (.var "v"))) .skip)
          σ σ₁ 13 := by
        apply (Run.ite_true (by simpa [ha] using hact) rFirst).mono
        simp [Cond.size, Expr.size]
      have rLast : Run B
          (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
            (.assign "last" (.var "v")) .skip) σ₁ σ₂ 7 := by
        have hact₁ : (Cond.eq (.get "activeA" (.var "v")) (.lit 1)).evalB B σ₁ =
            some true := by simpa [σ₁, ha] using hact
        have hvEval : (Expr.var "v").evalB B σ₁ = some v := by
          simpa [σ₁] using
            (show (Expr.var "v").evalB B σ = some v from
              by rw [evalB_var (by rw [hv]; exact hvB), hv])
        have rAssign : Run B (.assign "last" (.var "v")) σ₁ σ₂ 2 :=
          Run.assign hvEval
        apply (Run.ite_true hact₁ rAssign).mono
        norm_num [Cond.size, Expr.size]
      have rInc : Run B (inc "v") σ₂ σ₃ 4 := by
        apply Run.assign
        have hv₂ : σ₂.vars "v" = v := by simp [σ₂, σ₁, hv]
        have hv₂B : σ₂.vars "v" < B := by rw [hv₂]; omega
        have hv₂eval : (Expr.var "v").evalB B σ₂ = some v := by
          rw [evalB_var hv₂B, hv₂]
        have hsum : Bop.add.apply v 1 < B := by
          change v + 1 < B
          omega
        simpa [inc, Bop.apply] using
          evalB_bin hv₂eval (evalB_lit (by omega)) hsum
      have rbody : Run B linkedInitializeBody σ σ₃ 24 := by
        have := rOuter.seq (rLast.seq rInc)
        simpa [linkedInitializeBody, seqs, inc, σ₁, σ₂, σ₃] using
          this.mono (by omega)
      refine ⟨σ₃, next', rbody, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ₃, σ₂, σ₁]
      · simp [σ₃, σ₂, σ₁, hn]
      · simp [σ₃, σ₂, σ₁, ha, hln]
      · simp [σ₃, σ₂, σ₁, ha]
      · simpa [σ₃, σ₂, σ₁, hnext, set_arrOf_eq_upd, next']
      · intro _
        rfl
      · intro h
        rcases h with ⟨_, hne⟩ | hne
        · exact (hln hne).elim
        · exact (hne ha).elim
      · intro k hk
        change (if k = σ.vars "last" then v else next k) < B
        split_ifs
        · exact hvB
        · exact hnextB k hk
  · let σ₁ := σ
    let σ₂ := σ
    let σ₃ := σ.setVar "v" (v + 1)
    have rFirst : Run B
        (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
          (.ite (.eq (.var "last") (.var "n"))
            (.assign "head" (.var "v"))
            (.store "nextVertex" (.var "last") (.var "v"))) .skip)
        σ σ₁ 6 := by
      apply (Run.ite_false (by simpa [ha] using hact) Run.skip).mono
      norm_num [Cond.size, Expr.size]
    have rLast : Run B
        (.ite (.eq (.get "activeA" (.var "v")) (.lit 1))
          (.assign "last" (.var "v")) .skip) σ₁ σ₂ 6 := by
      have hact₁ : (Cond.eq (.get "activeA" (.var "v")) (.lit 1)).evalB B σ₁ =
          some false := by simpa [σ₁, ha] using hact
      apply (Run.ite_false hact₁ Run.skip).mono
      norm_num [Cond.size, Expr.size]
    have rInc : Run B (inc "v") σ₂ σ₃ 4 := by
      apply Run.assign
      have hv₂B : σ₂.vars "v" < B := by simp [σ₂, hv]; omega
      have hv₂eval : (Expr.var "v").evalB B σ₂ = some v := by
        rw [evalB_var hv₂B]; simp [σ₂, hv]
      have hsum : Bop.add.apply v 1 < B := by
        change v + 1 < B
        omega
      simpa [inc, σ₂, Bop.apply] using
        evalB_bin hv₂eval (evalB_lit (by omega)) hsum
    have rbody : Run B linkedInitializeBody σ σ₃ 24 := by
      have := rFirst.seq (rLast.seq rInc)
      simpa [linkedInitializeBody, seqs, inc, σ₁, σ₂, σ₃] using
        this.mono (by omega)
    refine ⟨σ₃, next, rbody, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₃, hv]
    · simp [σ₃, hn]
    · simp [σ₃, ha]
    · simp [σ₃, ha]
    · simpa [σ₃, hnext]
    · intro h
      exact (ha h.1).elim
    · intro _
      rfl
    · exact hnextB

/-- The literal predecessor write extends the successor links of a list by
one fresh final vertex. -/
lemma successorLinks_append_fresh
    {α : Type*} [DecidableEq α] {next : α → α} {l : List α}
    {z x : α} (hnodup : l.Nodup) (hlinks : SuccessorLinks next l)
    (hlast : l.getLast? = some z) (hfresh : x ∉ l) :
    SuccessorLinks (Function.update next z x) (l ++ [x]) := by
  induction l with
  | nil => simp at hlast
  | cons a tail ih =>
      cases tail with
      | nil =>
          have haz : a = z := by simpa using hlast
          subst z
          change Function.update next a x a = x ∧
            SuccessorLinks (Function.update next a x) [x]
          simp [Function.update, SuccessorLinks]
      | cons b rest =>
          have htail : (b :: rest).getLast? = some z := by simpa using hlast
          have haNotTail : a ∉ b :: rest := (List.nodup_cons.mp hnodup).1
          have hzTail : z ∈ b :: rest := List.mem_of_getLast? htail
          have haz : a ≠ z := by
            intro heq
            subst z
            exact haNotTail hzTail
          have hrestNodup : (b :: rest).Nodup := (List.nodup_cons.mp hnodup).2
          have hlinks' : next a = b ∧ SuccessorLinks next (b :: rest) := by
            simpa [SuccessorLinks] using hlinks
          have ih' := ih hrestNodup hlinks'.2 htail (by
            intro hx
            exact hfresh (by simp [hx]))
          change Function.update next z x a = b ∧
            SuccessorLinks (Function.update next z x) ((b :: rest) ++ [x])
          exact ⟨by simp [Function.update, haz, hlinks'.1], ih'⟩

/-- A represented nonempty list remains represented when its final pointer
is set to a fresh vertex and that vertex is appended. -/
lemma nodup_append_singleton_of_fresh
    {α : Type*} [DecidableEq α] {x : α} {l : List α}
    (hnodup : l.Nodup) (hfresh : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons a tail ih =>
      have hsplit := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      constructor
      · intro hx
        rcases List.mem_append.mp hx with htail | hlast
        · exact hsplit.1 htail
        · simp at hlast
          exact hfresh (by simp [hlast])
      · apply ih hsplit.2
        intro hx
        exact hfresh (by simp [hx])

lemma represents_append_fresh
    {α : Type*} [DecidableEq α] {head z x : α} {next : α → α}
    {l : List α} (hrep : Represents head next l)
    (hlast : l.getLast? = some z) (hfresh : x ∉ l) :
    Represents head (Function.update next z x) (l ++ [x]) := by
  rcases hrep with ⟨hnodup, hhead, hlinks⟩
  refine ⟨?_, ?_, successorLinks_append_fresh hnodup hlinks hlast hfresh⟩
  · exact nodup_append_singleton_of_fresh hnodup hfresh
  · cases l with
    | nil => simp at hlast
    | cons a tail =>
        simpa using hhead


private def initializeScanInv (B n : ℕ) (active : ℕ → ℕ)
    (initial : Env) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars "v" ≤ n ∧
  τ.arrs "activeA" = arrOf n active ∧
  (∀ a, a ≠ "nextVertex" → τ.arrs a = initial.arrs a) ∧
  τ.inp = initial.inp ∧ τ.out = initial.out ∧
  ∃ next : ℕ → ℕ,
    τ.arrs "nextVertex" = arrOf n next ∧
    (∀ k < n, next k < B) ∧
    ((scanList active 0 (τ.vars "v") = [] ∧
        τ.vars "head" = n ∧ τ.vars "last" = n) ∨
      (scanList active 0 (τ.vars "v") ≠ [] ∧
        Represents (τ.vars "head") next (scanList active 0 (τ.vars "v")) ∧
        (scanList active 0 (τ.vars "v")).getLast? = some (τ.vars "last") ∧
        τ.vars "last" < n))

private lemma scanList_prefix_fresh
    {active : ℕ → ℕ} {v : ℕ} : v ∉ scanList active 0 v := by
  rw [Lax235315Proofs.Construction.ReadKeys.mem_scanList]
  omega

private lemma linkedInitialize_body_spec
    {B n : ℕ} {active : ℕ → ℕ} {initial : Env}
    (hnB : n < B) (hactiveB : ∀ k < n, active k < B) :
    Spec B
      (fun τ => initializeScanInv B n active initial τ ∧ τ.vars "v" < n)
      linkedInitializeBody
      (fun τ τ' => initializeScanInv B n active initial τ' ∧
        τ'.vars "v" = τ.vars "v" + 1) 24 := by
  intro τ ⟨hinv, hvlt⟩
  rcases hinv with ⟨hn, hvle, hactiveArr, harrays, hin, hout,
    next, hnextArr, hnextB, hstate⟩
  have hlastB : τ.vars "last" < B := by
    rcases hstate with ⟨hempty, hhead, hlast⟩ | ⟨hne, hrep, htail, hlast⟩
    · rw [hlast]
      exact hnB
    · exact hlast.trans hnB
  have hlastRange : τ.vars "last" = n ∨ τ.vars "last" < n := by
    rcases hstate with ⟨_, _, hlast⟩ | ⟨_, _, _, hlast⟩
    · exact Or.inl hlast
    · exact Or.inr hlast
  obtain ⟨τ', next', hrun, hv', hn', hhead', hlast', hnextArr', hupdate,
    hunchanged, hnextB'⟩ := linkedInitializeBody_run
      (hv := rfl) (hn := hn) (hactive := hactiveArr)
      (hnext := hnextArr) hvlt hnB (hactiveB _ hvlt) hnextB hlastB hlastRange
  have hlistStep := Lax235315Proofs.Construction.ReadKeys.scanList_zero_add
    active (τ.vars "v")
  have hlist' : scanList active 0 (τ.vars "v" + 1) =
      scanList active 0 (τ.vars "v") ++
        if active (τ.vars "v") = 1 then [τ.vars "v"] else [] := by
    exact hlistStep
  have hotherArrays : ∀ a, a ≠ "nextVertex" → τ'.arrs a = initial.arrs a := by
    intro a hne
    have hframe := hrun.frame_arr a (by
      simp [Com.warrs, linkedInitializeBody, seqs, inc]
      exact hne)
    exact hframe.trans (harrays a hne)
  refine ⟨τ', hrun, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hn', ?_, ?_, hotherArrays,
      (hrun.frame_inp (by decide)).trans hin,
      (hrun.out_eq (by simp [linkedInitializeBody, seqs, inc, Com.NoWrite])).trans hout, ?_⟩
    · omega
    · exact (hrun.frame_arr "activeA" (by simp [Com.warrs, linkedInitializeBody, seqs, inc])).trans hactiveArr
    · refine ⟨next', hnextArr', hnextB', ?_⟩
      rcases hstate with ⟨hempty, hhead, hlast⟩ | ⟨hne, hrep, htail, hlastlt⟩
      · by_cases ha : active (τ.vars "v") = 1
        · rw [hv', hlist', hempty, if_pos ha]
          refine Or.inr ⟨by simp, ?_, ?_, ?_⟩
          · refine ⟨by simp, ?_, trivial⟩
            simpa [ha, hlast] using hhead'.symm
          · have hlastv : τ'.vars "last" = τ.vars "v" := by
              simpa [ha] using hlast'
            simpa [hlastv]
          · have hlastv : τ'.vars "last" = τ.vars "v" := by
              simpa [ha] using hlast'
            rw [hlastv]
            exact hvlt
        · rw [hv', hlist', hempty, if_neg ha]
          refine Or.inl ⟨by simp, ?_, ?_⟩
          · simpa [ha, hhead] using hhead'
          · simpa [ha, hlast] using hlast'
      · by_cases ha : active (τ.vars "v") = 1
        · have hfresh : τ.vars "v" ∉ scanList active 0 (τ.vars "v") :=
            scanList_prefix_fresh
          have hrep' : Represents (τ'.vars "head") next'
              (scanList active 0 (τ.vars "v") ++ [τ.vars "v"]) := by
            have hupd : next' = Function.update next (τ.vars "last") (τ.vars "v") := by
              have hu := hupdate ⟨ha, by omega⟩
              have hfun : upd next (τ.vars "last") (τ.vars "v") =
                  Function.update next (τ.vars "last") (τ.vars "v") := by
                funext i
                simp [upd, Function.update]
              simpa [hfun] using hu
            have hnew := represents_append_fresh hrep htail hfresh
            have hheadEq : τ'.vars "head" = τ.vars "head" := by
              simpa [ha, show τ.vars "last" ≠ n by omega] using hhead'
            rw [hupd]
            simpa [hheadEq] using hnew
          have hlastEq : τ'.vars "last" = τ.vars "v" := by
            simpa [ha] using hlast'
          rw [hv', hlist', if_pos ha]
          refine Or.inr ⟨by simp [hne], hrep', ?_, ?_⟩
          · simp [hlastEq]
          · simpa [hlastEq] using hvlt
        · have hnextEq : next' = next := hunchanged (Or.inr ha)
          rw [hv', hlist', if_neg ha]
          have hheadEq : τ'.vars "head" = τ.vars "head" := by
            simpa [ha] using hhead'
          have hlastEq : τ'.vars "last" = τ.vars "last" := by
            simpa [ha] using hlast'
          refine Or.inr ⟨by simpa using hne, ?_, ?_, ?_⟩
          · simpa [hheadEq, hnextEq] using hrep
          · simpa [hlastEq] using htail
          · simpa [hlastEq] using hlastlt
  · simpa [hv']

/-- Execute the complete linked-list initialization excerpt. The active list
is accumulated in increasing order, while its final pointer remains
unconstrained just as in `Represents`. -/
lemma linkedInitialize_run
    {B n : ℕ} {σ : Env} {active next : ℕ → ℕ}
    (hnB : n < B)
    (hn : σ.vars "n" = n)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hactiveB : ∀ k < n, active k < B)
    (hnextB : ∀ k < n, next k < B) :
    ∃ σ' next', Run B linkedInitialize σ σ' (40 * (n + 1)) ∧
      σ'.vars "n" = n ∧ σ'.vars "v" = n ∧
      (∀ a, a ≠ "nextVertex" → σ'.arrs a = σ.arrs a) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      σ'.arrs "nextVertex" = arrOf n next' ∧
      (∀ k < n, next' k < B) ∧
      ((scanList active 0 n = [] ∧
          σ'.vars "head" = n ∧ σ'.vars "last" = n) ∨
        (scanList active 0 n ≠ [] ∧
          Represents (σ'.vars "head") next' (scanList active 0 n) ∧
          (scanList active 0 n).getLast? = some (σ'.vars "last") ∧
          σ'.vars "last" < n)) := by
  let σ₁ := σ.setVar "head" n
  let σ₂ := σ₁.setVar "last" n
  have rHead : Run B (.assign "head" (.var "n")) σ σ₁ 2 := by
    apply Run.assign
    rw [evalB_var (by rw [hn]; exact hnB), hn]
  have rLast : Run B (.assign "last" (.var "n")) σ₁ σ₂ 2 := by
    apply Run.assign
    have hnn : σ₁.vars "n" = n := by simp [σ₁, hn]
    rw [evalB_var (by rw [hnn]; exact hnB), hnn]
  let I := initializeScanInv B n active σ
  have hbody := linkedInitialize_body_spec (B := B) (n := n)
    (active := active) (initial := σ) hnB hactiveB
  have hI0 : I (σ₂.setVar "v" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₂, σ₁, hn]
    · simp [σ₂, σ₁]
    · simp [σ₂, σ₁, hactive]
    · intro a hne
      simp [σ₂, σ₁]
    · simp [σ₂, σ₁]
    · simp [σ₂, σ₁]
    · refine ⟨next, ?_, hnextB, ?_⟩
      · simpa [σ₂, σ₁] using hnext
      · left
        simp [σ₂, σ₁, scanList]
  obtain ⟨τ, hloop, hinv, hvn⟩ :=
    (Spec.forRangeZero "v" "n" I n 24 hnB
      (fun _ h => by simpa [I, initializeScanInv] using h.2.1)
      (fun _ h => by simpa [I, initializeScanInv] using h.1)
      hbody).run (σ := σ₂) hI0
  have hshape : linkedInitialize =
        .seq (.assign "head" (.var "n"))
          (.seq (.assign "last" (.var "n"))
            (.seq (.assign "v" (.lit 0))
              (.while (.lt (.var "v") (.var "n")) linkedInitializeBody))) := by
    simp [linkedInitialize, linkedInitializeBody, seqs]
  have hrun : Run B linkedInitialize σ τ (40 * (n + 1)) := by
    rw [hshape]
    exact (rHead.seq (rLast.seq hloop)).mono (by omega)
  rcases hinv with ⟨hn', hvle, hactive', harrays, hin, hout,
    next', hnext', hnextB', hstate⟩
  refine ⟨τ, next', hrun, hn', hvn, ?_, hin, hout, hnext', hnextB', ?_⟩
  · intro a hne
    exact harrays a hne
  · simpa [hvn] using hstate


end Lax235315Proofs.Construction.LinkedInitializeSource
