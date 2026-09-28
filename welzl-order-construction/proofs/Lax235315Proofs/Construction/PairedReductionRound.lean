import Lax235315Proofs.Construction.InputSuffixFrame
import Lax235315Proofs.Construction.ReductionRoundSource
import Mathlib.Tactic

set_option maxRecDepth 4096

/-! Coupling for the complete literal reduction round. -/

namespace Lax235315Proofs.Construction.PairedReductionRound

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.InputSuffixFrame
open Lax235315Proofs.Construction.ReductionRoundSource
open Lax235315Proofs.Construction.RoundInvariant

private lemma frontier_withInput {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Frontier B c n x σ) (input : List ℕ)
    (hfit : ∀ v ∈ input, v < B) (hbits : ∀ v ∈ input, v ≤ 1) :
    Frontier B c n x {σ with inp := input} := by
  rcases h with ⟨hw, hgood, hacount, hnonemptyA, hnonemptyB,
    hactiveABits, hactiveBBits, hnextABits, hnextBBits, hconservation, hshrinking⟩
  have hw' : Workspace B c n x {σ with inp := input} := by
    refine ⟨⟨hw.bounded.vars, hw.bounded.arrays, hfit⟩,
      hw.parameter, hw.vertices, hw.edges, hw.logarithm, hw.radixSize,
      hw.offsets, hw.targets, hw.lengths, hbits, hw.output⟩
  refine ⟨hw', hgood, hacount, hnonemptyA, hnonemptyB,
    hactiveABits, hactiveBBits, hnextABits, hnextBBits,
    hconservation, hshrinking⟩

/-- If two source tapes agree on the exact prefix consumed by a reduction
round, their literal executions have the same complete non-input poststate.
The proof runs the round once on that common prefix, appends each unread tail,
and uses determinism of the bounded big-step semantics to identify both
actual executions with those framed runs. -/
lemma reductionRound_pair_of_shared_prefix
    {B c n bound : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    {σ τ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hfrontS : Frontier B c n x σ) (hfrontT : Frontier B c n x τ)
    (hvars : σ.vars = τ.vars) (harrs : σ.arrs = τ.arrs) (hout : σ.out = τ.out)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (hqB : 2 ^ Nat.clog 2 n < B)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B)
    (hlenS : 8 * Nat.clog 2 n * σ.vars "acount" ≤ σ.inp.length)
    (hlenT : 8 * Nat.clog 2 n * τ.vars "acount" ≤ τ.inp.length)
    (hshared : σ.inp.take (8 * Nat.clog 2 n * σ.vars "acount") =
      τ.inp.take (8 * Nat.clog 2 n * σ.vars "acount")) :
    ∃ σ' τ',
      Run B WelzlProgram.reductionRound σ σ'
        (4500 * (x.length + 1) + 120 * Nat.clog 2 n * σ.vars "acount") ∧
      Run B WelzlProgram.reductionRound τ τ'
        (4500 * (x.length + 1) + 120 * Nat.clog 2 n * σ.vars "acount") ∧
      σ'.vars = τ'.vars ∧ σ'.arrs = τ'.arrs ∧ σ'.out = τ'.out ∧
      σ'.inp = σ.inp.drop (8 * Nat.clog 2 n * σ.vars "acount") ∧
      τ'.inp = τ.inp.drop (8 * Nat.clog 2 n * σ.vars "acount") := by
  let N := 8 * Nat.clog 2 n * σ.vars "acount"
  let blockS := σ.inp.take N
  let blockT := τ.inp.take N
  have hcountT : τ.vars "acount" = σ.vars "acount" := by
    rw [hvars]
  have hcsqT : τ.vars "csq" = c ^ 2 := by rw [← hvars]; exact hcsq
  have hboundT : τ.vars "nearBound" = bound := by rw [← hvars]; exact hbound
  have hlargeT : 12 * c ^ 2 * Nat.clog 2 n < τ.vars "acount" := by
    rw [← hvars]
    exact hlarge
  have hblockEq : blockS = blockT := by
    simpa [blockS, blockT, N, hcountT] using hshared
  have hbinaryS : ∀ v ∈ blockS, v ≤ 1 := by
    intro v hv
    exact hfrontS.workspace.randomInput v (List.mem_of_mem_take hv)
  have hbinaryT : ∀ v ∈ blockT, v ≤ 1 := by
    intro v hv
    exact hfrontT.workspace.randomInput v (List.mem_of_mem_take hv)
  have hfitS : ∀ v ∈ blockS, v < B := by
    intro v hv
    exact hfrontS.workspace.bounded.input v (List.mem_of_mem_take hv)
  have hbaseFront : Frontier B c n x {σ with inp := blockS} :=
    frontier_withInput hfrontS blockS hfitS hbinaryS
  have hlenSN : N ≤ σ.inp.length := by simpa [N] using hlenS
  have hblockLength : blockS.length = N := by
    simp [blockS, List.length_take, Nat.min_eq_left hlenSN]
  have hbaseTape : 8 * Nat.clog 2 n * σ.vars "acount" ≤ blockS.length := by
    simpa [N] using hblockLength.symm.le
  obtain ⟨μ, hbaseRun, _, hbaseTail, _⟩ := reductionRound_run hx hG
    hbaseFront hc hn hlarge hcsq hbound hbaseTape hqB hnB htargetB hdenomB hboundB
  obtain ⟨σ', hactualRunS, _, htailS, _⟩ := reductionRound_run hx hG
    hfrontS hc hn hlarge hcsq hbound hlenS hqB hnB htargetB hdenomB hboundB
  have hbaseTailEq : μ.inp = [] := by
    simpa [blockS, N] using hbaseTail
  obtain ⟨τ', hactualRunT, _, htailT, _⟩ := reductionRound_run hx hG
    hfrontT hc hn hlargeT hcsqT hboundT (by simpa [N, hcountT] using hlenT)
      hqB hnB htargetB hdenomB hboundB
  have hsplitS : σ.inp = blockS ++ σ.inp.drop N := by
    simpa [blockS, N] using (List.take_append_drop N σ.inp).symm
  have hsplitT : τ.inp = blockT ++ τ.inp.drop N := by
    simpa [blockT, N] using (List.take_append_drop N τ.inp).symm
  let σbase : Env := {σ with inp := blockS}
  let τbase : Env := {τ with inp := blockT}
  have hbaseEq : σbase = τbase := by
    cases σ
    cases τ
    cases hvars
    cases harrs
    cases hout
    simp [σbase, τbase, hblockEq]
  have hstartS : appendInput σbase (σ.inp.drop N) = σ := by
    cases σ with
    | mk varsS arraysS inpS outS =>
        change Env.mk varsS arraysS (blockS ++ List.drop N inpS) outS = _
        exact congrArg (fun input : List ℕ => Env.mk varsS arraysS input outS)
          hsplitS.symm
  have hstartT : appendInput τbase (τ.inp.drop N) = τ := by
    cases τ with
    | mk varsT arraysT inpT outT =>
        change Env.mk varsT arraysT (blockT ++ List.drop N inpT) outT = _
        exact congrArg (fun input : List ℕ => Env.mk varsT arraysT input outT)
          hsplitT.symm
  have hrunS := run_appendInput hbaseRun (σ.inp.drop N)
  have hrunT := run_appendInput hbaseRun (τ.inp.drop N)
  have hrunS' : Run B WelzlProgram.reductionRound σ (appendInput μ (σ.inp.drop N))
      (4500 * (x.length + 1) + 120 * Nat.clog 2 n * σ.vars "acount") := by
    rw [hstartS] at hrunS
    simpa [appendInput] using hrunS
  have hstartT' : appendInput σbase (τ.inp.drop N) = τ := by
    rw [← hbaseEq] at hstartT
    exact hstartT
  have hrunT' : Run B WelzlProgram.reductionRound τ (appendInput μ (τ.inp.drop N))
      (4500 * (x.length + 1) + 120 * Nat.clog 2 n * σ.vars "acount") := by
    rw [hstartT'] at hrunT
    simpa [appendInput] using hrunT
  obtain ⟨_, _, hstepS⟩ := hrunS'
  obtain ⟨_, _, hstepT⟩ := hrunT'
  have hactualRunS' := hactualRunS
  have hactualRunT' := hactualRunT
  obtain ⟨_, _, hstepActualS⟩ := hactualRunS
  obtain ⟨_, _, hstepActualT⟩ := hactualRunT
  have hendS : appendInput μ (σ.inp.drop N) = σ' :=
    (BigStep.unique hstepS.bigStep hstepActualS.bigStep).1
  have hendT : appendInput μ (τ.inp.drop N) = τ' :=
    (BigStep.unique hstepT.bigStep hstepActualT.bigStep).1
  -- The two appended runs share their initial state and canonical endpoint
  -- except for the unread input tail, so determinism identifies each actual
  -- endpoint with its corresponding framed endpoint.
  refine ⟨σ', τ', hactualRunS', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hcountT] using hactualRunT'
  · calc
      σ'.vars = (appendInput μ (σ.inp.drop N)).vars := by rw [hendS]
      _ = (appendInput μ (τ.inp.drop N)).vars := rfl
      _ = τ'.vars := by rw [hendT]
  · calc
      σ'.arrs = (appendInput μ (σ.inp.drop N)).arrs := by rw [hendS]
      _ = (appendInput μ (τ.inp.drop N)).arrs := rfl
      _ = τ'.arrs := by rw [hendT]
  · calc
      σ'.out = (appendInput μ (σ.inp.drop N)).out := by rw [hendS]
      _ = (appendInput μ (τ.inp.drop N)).out := rfl
      _ = τ'.out := by rw [hendT]
  · simpa [N] using htailS
  · simpa [N, hcountT] using htailT

end Lax235315Proofs.Construction.PairedReductionRound
