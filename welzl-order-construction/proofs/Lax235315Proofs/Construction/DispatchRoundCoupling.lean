import Lax235315Proofs.Construction.InputSuffixFrame
import Lax235315Proofs.Construction.ReductionRoundSource
import Lax235315Proofs.Construction.Sampling
import Mathlib.Tactic

set_option maxRecDepth 4096

/-! The deterministic continuation after a sampled prefix has the same
poststate on each unread suffix. -/

namespace Lax235315Proofs.Construction.DispatchRoundCoupling

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.CertifiedBranch
open Lax235315Proofs.Construction.InputSuffixFrame
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.ReductionRoundSource
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.TracePartitions

private lemma frontier_empty_input {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Frontier B c n x σ) :
    Frontier B c n x {σ with inp := []} := by
  rcases h with ⟨hw, hgood, hacount, hnonemptyA, hnonemptyB,
    hactiveABits, hactiveBBits, hnextABits, hnextBBits, hconservation, hshrinking⟩
  have hw' : Workspace B c n x {σ with inp := []} := by
    refine ⟨⟨hw.bounded.vars, hw.bounded.arrays, ?_⟩, hw.parameter, hw.vertices,
      hw.edges, hw.logarithm, hw.radixSize, hw.offsets, hw.targets,
      hw.lengths, ?_, hw.output⟩
    · intro b hb
      simp at hb
    · intro b hb
      simp at hb
  refine ⟨hw', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hgood
  · change σ.vars "acount" = (activeVertices n (view σ "activeA")).card
    exact hacount
  · intro hn
    change (activeVertices n (view σ "activeA")).Nonempty
    exact hnonemptyA hn
  · intro hn
    change (activeVertices n (view σ "activeB")).Nonempty
    exact hnonemptyB hn
  · change Lax235315Proofs.Construction.BitArrays.ArrayBits "activeA" σ
    exact hactiveABits
  · change Lax235315Proofs.Construction.BitArrays.ArrayBits "activeB" σ
    exact hactiveBBits
  · change Lax235315Proofs.Construction.BitArrays.ArrayBits "nextA" σ
    exact hnextABits
  · change Lax235315Proofs.Construction.BitArrays.ArrayBits "nextB" σ
    exact hnextBBits
  · simpa using hconservation
  · simpa using hshrinking

/-- A deterministic `dispatchRound` started from equal non-input states
produces the same next-round state on arbitrary unread suffixes. The common
empty-input run fixes the accepted/rejected outcome once; `InputSuffixFrame`
then reinstates each suffix without changing any non-input field. -/
lemma dispatchRound_pair_of_equal_state
    {B c n bound : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    {σ τ : Env} {W : Finset ℕ}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hfront : Frontier B c n x σ)
    (hvars : σ.vars = τ.vars) (harrs : σ.arrs = τ.arrs) (hout : σ.out = τ.out)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2) (hbound : σ.vars "nearBound" = bound)
    (henum : PrefixEnumerates (sampleSize (σ.vars "acount") c) (view σ "ord") W)
    (hWr : ∀ v ∈ W, v < n)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B) (hboundB : bound < B) :
    ∃ σ' τ',
      Run B dispatchRound σ σ' (2300 * (x.length + 1) + 4) ∧
      Run B dispatchRound τ τ' (2300 * (x.length + 1) + 4) ∧
      σ'.vars "collision" = τ'.vars "collision" ∧
      σ'.vars "good" = τ'.vars "good" ∧
      σ'.vars "acount" = τ'.vars "acount" ∧
      σ'.vars "round" = τ'.vars "round" ∧
      σ'.arrs "activeA" = τ'.arrs "activeA" ∧
      σ'.arrs "activeB" = τ'.arrs "activeB" ∧
      ((σ'.vars "good" = 1 ∧ τ'.vars "good" = 1) ∨
        (σ'.vars "good" ≠ 1 ∧ τ'.vars "good" ≠ 1 ∧
          σ'.vars "acount" = 0 ∧ τ'.vars "acount" = 0)) := by
  let σ₀ : Env := {σ with inp := []}
  have hfront₀ : Frontier B c n x σ₀ := by
    simpa [σ₀] using frontier_empty_input hfront
  have hvars₀ : σ₀.vars = σ.vars := rfl
  have harrs₀ : σ₀.arrs = σ.arrs := rfl
  have hout₀ : σ₀.out = σ.out := rfl
  have hvarsτ : σ.vars = τ.vars := hvars
  have harrsτ : σ.arrs = τ.arrs := harrs
  have hcsq₀ : σ₀.vars "csq" = c ^ 2 := by simpa [σ₀] using hcsq
  have hbound₀ : σ₀.vars "nearBound" = bound := by simpa [σ₀] using hbound
  have hlarge₀ : 12 * c ^ 2 * Nat.clog 2 n < σ₀.vars "acount" := by
    simpa [σ₀] using hlarge
  have henum₀ : PrefixEnumerates (sampleSize (σ₀.vars "acount") c)
      (view σ₀ "ord") W := by
    change PrefixEnumerates (sampleSize (σ.vars "acount") c) (view σ "ord") W
    exact henum
  obtain ⟨μ, hrun₀, houtcome₀⟩ := dispatchRound_run hx hG hfront₀ hc hn
    hlarge₀ hcsq₀ hbound₀ henum₀ hWr hnB htargetB hdenomB hboundB
  have hμinp : μ.inp = [] := hrun₀.frame_inp (by decide)
  have hrunσ : Run B dispatchRound σ {μ with inp := σ.inp}
      (2300 * (x.length + 1) + 4) := by
    have h := run_on_any_input_of_empty hrun₀ (by simp [σ₀]) hμinp σ.inp
    simpa [σ₀] using h
  have hinitialτ : {σ₀ with inp := τ.inp} = τ := by
    cases σ with
    | mk varsS arraysS inpS outS =>
      cases τ with
      | mk varsT arraysT inpT outT =>
        simp_all [σ₀]
  have hrunτ : Run B dispatchRound τ {μ with inp := τ.inp}
      (2300 * (x.length + 1) + 4) := by
    have h := run_on_any_input_of_empty hrun₀ (by simp [σ₀]) hμinp τ.inp
    rw [hinitialτ] at h
    exact h
  refine ⟨{μ with inp := σ.inp}, {μ with inp := τ.inp}, hrunσ, hrunτ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases houtcome₀ with haccepted | hrejected
    · rcases haccepted with ⟨hfront', _, _⟩
      exact Or.inl ⟨by simpa using hfront'.success, by simpa using hfront'.success⟩
    · rcases hrejected with ⟨hgood', hacount'⟩
      exact Or.inr ⟨by simpa using hgood', by simpa using hgood',
        by simpa using hacount', by simpa using hacount'⟩

end Lax235315Proofs.Construction.DispatchRoundCoupling
