import Lax235315Proofs.Construction.LinkedReconstruction
import Lax808846Proofs.Reasoning
import Mathlib.Tactic

/-! Bounded source execution of the final list traversal in
`WelzlProgram.reconstructAndWrite`. -/

namespace Lax235315Proofs.Construction.LinkedOutputSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.LinkedReconstruction
open Lax235315Proofs.Construction.WelzlProgram

/-- One output iteration writes the current vertex, follows its successor,
and advances the output count. -/
def linkedOutputBody : Com :=
  seqs [
    .write (.var "v"),
    .assign "v" (.get "nextVertex" (.var "v")),
    inc "i"]

/-- The exact final traversal excerpt in `reconstructAndWrite`, including its
head and counter initializations. -/
def linkedOutputAndWrite : Com :=
  seqs [
    .assign "i" (.lit 0),
    .assign "v" (.var "head"),
    .while (.lt (.var "i") (.var "n")) linkedOutputBody]

lemma linkedOutputAndWrite_eq_source_excerpt :
    linkedOutputAndWrite =
      seqs [
        .assign "i" (.lit 0),
        .assign "v" (.var "head"),
        .while (.lt (.var "i") (.var "n")) <|
          seqs [
            .write (.var "v"),
            .assign "v" (.get "nextVertex" (.var "v")),
            inc "i"]] := rfl

/-- Run one iteration of the final traversal. -/
lemma linkedOutputBody_run
    {B n i x : ℕ} {next : ℕ → ℕ} {σ : Env}
    (hi : σ.vars "i" = i) (hv : σ.vars "v" = x)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hin : i < n) (hxn : x < n) (hnB : n < B)
    (hnextB : ∀ k < n, next k < B)
    (hiNextB : i + 1 < B) :
    ∃ σ', Run B linkedOutputBody σ σ' 9 ∧
      σ'.vars "i" = i + 1 ∧ σ'.vars "v" = next x ∧
      σ'.arrs "nextVertex" = σ.arrs "nextVertex" ∧
      σ'.vars "n" = σ.vars "n" ∧ σ'.vars "head" = σ.vars "head" ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out ++ [x] := by
  let σ₁ := { σ with out := σ.out ++ [x] }
  let σ₂ := σ₁.setVar "v" (next x)
  let σ₃ := σ₂.setVar "i" (i + 1)
  have rWrite : Run B (.write (.var "v")) σ σ₁ 2 := by
    apply Run.write
    have hvB : σ.vars "v" < B := by rw [hv]; omega
    calc
      (Expr.var "v").evalB B σ = some (σ.vars "v") := evalB_var hvB
      _ = some x := by simp [hv]
  have rNext : Run B (.assign "v" (.get "nextVertex" (.var "v"))) σ₁ σ₂ 3 := by
    apply Run.assign
    apply evalB_get (evalB_var (by rw [hv]; exact (hxn.trans hnB)))
    · simpa [σ₁, hnext, hv] using getElem?_arrOf next hxn
    · exact hnextB x hxn
  have rInc : Run B (inc "i") σ₂ σ₃ 4 := by
    apply Run.assign
    have hi₂ : σ₂.vars "i" = i := by simp [σ₂, σ₁, hi]
    have hi₂B : σ₂.vars "i" < B := by rw [hi₂]; omega
    have hival : (Expr.var "i").evalB B σ₂ = some i := by
      rw [evalB_var hi₂B, hi₂]
    exact evalB_bin hival (evalB_lit (by omega)) hiNextB
  have hrun : Run B linkedOutputBody σ σ₃ 9 := by
    simpa [linkedOutputBody, seqs, inc] using rWrite.seq (rNext.seq rInc)
  refine ⟨σ₃, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [σ₃, σ₂, σ₁, hi]
  · simp [σ₃, σ₂, σ₁]
  · exact hrun.frame_arr "nextVertex" (by decide)
  · exact hrun.frame_var "n" (by decide)
  · exact hrun.frame_var "head" (by decide)
  · exact hrun.frame_inp (by decide)
  · simp [σ₃, σ₂, σ₁]

/-- State of the output scan: `done` is the already written prefix and
`todo` is the remaining suffix of the represented list. -/
def LinkedOutputInv (B n : ℕ) (head : ℕ) (next : ℕ → ℕ)
    (initialInput initialOutput : List ℕ) (l : List ℕ) (σ : Env) : Prop :=
  ∃ done todo,
    l = done ++ todo ∧
    σ.vars "i" = done.length ∧ done.length + todo.length = n ∧
    σ.vars "n" = n ∧ σ.vars "head" = head ∧
    (todo = [] ∨ ∃ x, todo.head? = some x ∧ σ.vars "v" = x) ∧
    σ.arrs "nextVertex" = arrOf n next ∧
    SuccessorLinks next todo ∧
    σ.inp = initialInput ∧ σ.out = initialOutput ++ done

/-- The output loop emits exactly a represented list of length `n` at a
linear source cost. The linked-list head requirement is conditional so the
empty list (with its unused head cell) is covered too. -/
lemma linkedOutputLoop_run
    {B n : ℕ} {head : ℕ} {next : ℕ → ℕ} {l : List ℕ}
    {initialInput initialOutput : List ℕ} {σ : Env}
    (hrep : l = [] ∨ Represents head next l) (hlen : l.length = n)
    (hvertex : ∀ x ∈ l, x < n) (hnB : n < B)
    (hnextB : ∀ k < n, next k < B)
    (hi0 : σ.vars "i" = 0) (hv0 : l = [] ∨ σ.vars "v" = head)
    (hn : σ.vars "n" = n)
    (hhead : σ.vars "head" = head)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hin : σ.inp = initialInput) (hout : σ.out = initialOutput) :
    ∃ σ', Run B (.while (.lt (.var "i") (.var "n")) linkedOutputBody)
      σ σ' (13 * n + 4) ∧
      σ'.vars "i" = n ∧ σ'.vars "head" = head ∧
      σ'.vars "n" = n ∧ σ'.arrs "nextVertex" = arrOf n next ∧
      σ'.inp = initialInput ∧ σ'.out = initialOutput ++ l := by
  let Inv := LinkedOutputInv B n head next initialInput initialOutput l
  have hlinks : SuccessorLinks next l := by
    rcases hrep with hnil | hrep
    · simp [hnil, SuccessorLinks]
    · exact hrep.2.2
  have hheadRep : l = [] ∨ l.head? = some head := by
    rcases hrep with hnil | hrep
    · exact Or.inl hnil
    · exact Or.inr hrep.2.1
  have hInv : Inv σ := by
    refine ⟨[], l, by simp, ?_, ?_, hn, hhead, ?_, hnext,
      hlinks, hin, ?_⟩
    · exact hi0
    · simpa [hlen]
    · rcases hheadRep with hl | hl
      · exact Or.inl hl
      · right
        cases l with
        | nil => simp at hl
        | cons x xs =>
            refine ⟨x, rfl, ?_⟩
            rw [show x = head by simpa using hl]
            rcases hv0 with hvnil | hvhead
            · simp [hvnil] at hl
            · exact hvhead
    · simp [hout]
  have hdef : ∀ τ, Inv τ → ∃ v,
      (Cond.lt (.var "i") (.var "n")).evalB B τ = some v := by
    intro τ hτ
    rcases hτ with ⟨done, todo, _, hi, hlenParts, hnτ, _, _, _, _, _⟩
    have hiB : τ.vars "i" < B := by rw [hi]; omega
    have hnτB : τ.vars "n" < B := by rw [hnτ]; exact hnB
    refine ⟨decide (done.length < n), ?_⟩
    simpa [hi, hnτ] using
      evalB_condLt (evalB_var hiB) (evalB_var hnτB)
  have hstep : ∀ τ, Inv τ →
      (Cond.lt (.var "i") (.var "n")).evalB B τ = some true →
      ∃ τ', Run B linkedOutputBody τ τ' 9 ∧ Inv τ' ∧
        (fun ρ => n - ρ.vars "i") τ' <
          (fun ρ => n - ρ.vars "i") τ := by
    intro τ hτ hcond
    rcases hτ with ⟨done, todo, hlist, hi, hlenParts, hnτ, hheadτ,
      hvTodo, hnextτ, hlinks, hinτ, houtτ⟩
    have hiLt : done.length < n := by
      have heval := evalB_condLt
        (evalB_var (by rw [hi]; omega : τ.vars "i" < B))
        (evalB_var (by rw [hnτ]; exact hnB))
      rw [heval] at hcond
      have hdec : decide (done.length < n) = true := by
        simpa [hi, hnτ] using Option.some.inj hcond
      exact of_decide_eq_true hdec
    have htodoLen : 0 < todo.length := by omega
    cases todo with
    | nil => simp at htodoLen
    | cons x xs =>
        have hxVertex : x < n := hvertex x (by rw [hlist]; simp)
        have hxB : x < B := hxVertex.trans hnB
        have hvx : τ.vars "v" = x := by
          rcases hvTodo with hnil | ⟨y, hy, hv⟩
          · simp at hnil
          · have hyx : x = y := by simpa using hy
            rw [← hyx] at hv
            exact hv
        have hiNextB : done.length + 1 < B := by omega
        obtain ⟨τ', hrun, hi', hv', hnext', hn', hhead', hin', hout'⟩ :=
          linkedOutputBody_run (hi := hi) (hv := hvx) (hnext := hnextτ)
            (hin := hiLt) (hxn := hxVertex) (hnB := hnB)
            (hnextB := hnextB) (hiNextB := hiNextB)
        have htailLinks : SuccessorLinks next xs := by
          cases xs with
          | nil => trivial
          | cons y ys =>
              simpa [SuccessorLinks] using hlinks.right
        have hvTodo' : xs = [] ∨
            ∃ y, xs.head? = some y ∧ τ'.vars "v" = y := by
          cases xs with
          | nil => exact Or.inl rfl
          | cons y ys =>
              have hxy : next x = y := by
                simpa [SuccessorLinks] using hlinks.left
              refine Or.inr ⟨y, rfl, ?_⟩
              simpa [hv', hxy]
        let done' := done ++ [x]
        have hinv' : Inv τ' := by
          refine ⟨done', xs, ?_, ?_, ?_, hn'.trans hnτ,
            hhead'.trans hheadτ, hvTodo', hnext'.trans hnextτ,
            htailLinks, hin'.trans hinτ, ?_⟩
          · simp [done', hlist]
          · simp [done', hi']
          · simp only [List.length_cons] at hlenParts
            simp only [done', List.length_append, List.length_singleton]
            omega
          · rw [hout', houtτ]
            simp [done', List.append_assoc]
        refine ⟨τ', hrun, hinv', ?_⟩
        change n - τ'.vars "i" < n - τ.vars "i"
        rw [hi']
        omega
  obtain ⟨τ', hrun, hinv', hfalse⟩ :=
    Run.while_count Inv (fun τ => n - τ.vars "i") 9 hdef hstep hInv
  rcases hinv' with ⟨done, todo, hlist, hi, hlenParts, hnτ, hheadτ,
    _, hnextτ, _, hinτ, houtτ⟩
  have hfinal : τ'.vars "i" = n := by
    have heval := evalB_condLt
      (evalB_var (by rw [hi]; omega : τ'.vars "i" < B))
      (evalB_var (by rw [hnτ]; exact hnB))
    rw [heval] at hfalse
    have hdec : decide (done.length < n) = false := by
      simpa [hi, hnτ] using Option.some.inj hfalse
    have hnot : ¬ done.length < n := of_decide_eq_false hdec
    omega
  have htodoEmpty : todo = [] := by
    have : todo.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero this
  have hlistFinal : l = done := by simpa [htodoEmpty] using hlist
  refine ⟨τ', ?_, hfinal, hheadτ, hnτ, hnextτ, hinτ, ?_⟩
  · simpa [Cond.size, Expr.size, hi0] using hrun
  · rw [houtτ, hlistFinal]

/-- Execute the literal final output excerpt, including `i := 0` and
`v := head`. It emits exactly the represented list, preserves the input,
and costs a linear number of source steps. -/
lemma linkedOutputAndWrite_run
    {B n : ℕ} {head : ℕ} {next : ℕ → ℕ} {l : List ℕ}
    {initialInput initialOutput : List ℕ} {σ : Env}
    (hrep : l = [] ∨ Represents head next l) (hlen : l.length = n)
    (hvertex : ∀ x ∈ l, x < n) (hnB : n < B) (hheadB : head < B)
    (hnextB : ∀ k < n, next k < B)
    (hn : σ.vars "n" = n) (hhead : σ.vars "head" = head)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hin : σ.inp = initialInput) (hout : σ.out = initialOutput) :
    ∃ σ', Run B linkedOutputAndWrite σ σ' (13 * n + 9) ∧
      σ'.vars "i" = n ∧ σ'.vars "head" = head ∧
      σ'.vars "n" = n ∧ σ'.arrs "nextVertex" = arrOf n next ∧
      σ'.inp = initialInput ∧ σ'.out = initialOutput ++ l := by
  let σ₁ := σ.setVar "i" 0
  let σ₂ := σ₁.setVar "v" head
  have rInitI : Run B (.assign "i" (.lit 0)) σ σ₁ 2 := by
    apply Run.assign
    exact evalB_lit (by omega)
  have rInitV : Run B (.assign "v" (.var "head")) σ₁ σ₂ 2 := by
    have hhead₁ : σ₁.vars "head" = head := by simp [σ₁, hhead]
    have evalHead : (Expr.var "head").evalB B σ₁ = some head := calc
      (Expr.var "head").evalB B σ₁ = some (σ₁.vars "head") :=
        evalB_var (by rw [hhead₁]; exact hheadB)
      _ = some head := by simp [hhead₁]
    simpa [σ₂, Expr.size] using (Run.assign evalHead)
  have hinitv : l = [] ∨ σ₂.vars "v" = head := by
    rcases hrep with hnil | _
    · exact Or.inl hnil
    · exact Or.inr (by simp [σ₂, σ₁])
  obtain ⟨σ₃, rLoop, hi, hhead₃, hn₃, hnext₃, hin₃, hout₃⟩ :=
    linkedOutputLoop_run (σ := σ₂) (hrep := hrep) (hlen := hlen)
      (hvertex := hvertex) (hnB := hnB) (hnextB := hnextB)
      (hi0 := by simp [σ₂, σ₁]) (hv0 := hinitv)
      (hn := by simpa [σ₂, σ₁] using hn)
      (hhead := by simpa [σ₂, σ₁] using hhead)
      (hnext := by simpa [σ₂, σ₁] using hnext)
      (hin := by simpa [σ₂, σ₁] using hin)
      (hout := by simpa [σ₂, σ₁] using hout)
  have hrun : Run B linkedOutputAndWrite σ σ₃ (13 * n + 9) := by
    have hraw := rInitI.seq (rInitV.seq rLoop)
    simpa [linkedOutputAndWrite, seqs] using
      hraw.mono (by omega : 2 + (2 + (13 * n + 4)) ≤ 13 * n + 9)
  exact ⟨σ₃, hrun, hi, hhead₃, hn₃, hnext₃, hin₃, hout₃⟩

end Lax235315Proofs.Construction.LinkedOutputSource
