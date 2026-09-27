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
      (active v = 1 →
        (σ'.vars "head" = v ∨ σ'.vars "head" = σ.vars "head") ∧
        σ'.vars "last" = v) ∧
      (active v ≠ 1 → σ'.vars "head" = σ.vars "head" ∧
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
      · intro _
        simp [σ₃, σ₂, σ₁]
      · intro h
        exact (h ha).elim
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
      · intro _
        exact ⟨Or.inr (by simp [σ₃, σ₂, σ₁]), by simp [σ₃, σ₂, σ₁]⟩
      · intro h
        exact (h ha).elim
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
    · intro h
      exact (ha h).elim
    · intro _
      simp [σ₃]
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


end Lax235315Proofs.Construction.LinkedInitializeSource
