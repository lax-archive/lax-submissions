import Lax235315Proofs.Construction.WelzlStraight
import Mathlib.Tactic

/-! Verification of the state-transition passes used after an accepted
reduction round. -/

namespace Lax235315Proofs.Construction.CommitSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.WelzlProgram

/-- Invariant for copying the two newly selected representative sets into
the active-side arrays. -/
def AdoptInv (n : ℕ) (nextA nextB : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ activeA activeB : ℕ → ℕ,
    τ.arrs "activeA" = arrOf n activeA ∧
    τ.arrs "activeB" = arrOf n activeB ∧
    τ.arrs "nextA" = arrOf n nextA ∧
    τ.arrs "nextB" = arrOf n nextB ∧
    τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧
    (∀ i < τ.vars "v", activeA i = nextA i) ∧
    (∀ i < τ.vars "v", activeB i = nextB i)

/-- The literal `adoptNext` pass replaces both active indicator arrays by
the outputs of the two verified trace partitions. -/
theorem adoptNext_run {B n : ℕ} {σ : Env}
    {activeA activeB nextA nextB : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hactiveA : σ.arrs "activeA" = arrOf n activeA)
    (hactiveB : σ.arrs "activeB" = arrOf n activeB)
    (hnextA : σ.arrs "nextA" = arrOf n nextA)
    (hnextB : σ.arrs "nextB" = arrOf n nextB)
    (hnextAB : ∀ i < n, nextA i < B)
    (hnextBB : ∀ i < n, nextB i < B)
    (hnB : n < B) :
    ∃ σ' activeA' activeB',
      Run B adoptNext σ σ' (20 * (n + 1)) ∧
      σ'.arrs "activeA" = arrOf n activeA' ∧
      σ'.arrs "activeB" = arrOf n activeB' ∧
      (∀ i < n, activeA' i = nextA i) ∧
      (∀ i < n, activeB' i = nextB i) ∧
      σ'.vars "n" = n := by
  let body : Com := seqs [
    .store "activeA" (.var "v") (.get "nextA" (.var "v")),
    .store "activeB" (.var "v") (.get "nextB" (.var "v")),
    inc "v"]
  have hbody : Spec B
      (fun τ => AdoptInv n nextA nextB τ ∧ τ.vars "v" < n)
      body
      (fun τ τ' => AdoptInv n nextA nextB τ' ∧
        τ'.vars "v" = τ.vars "v" + 1) 14 := by
    rintro τ ⟨⟨curA, curB, hcurA, hcurB, hnA, hnB', hv, hnn,
      hfillA, hfillB⟩, hlt⟩
    have hvB : τ.vars "v" < B := hlt.trans hnB
    have hlenA : τ.vars "v" < (τ.arrs "activeA").length := by
      rw [hcurA, length_arrOf]
      exact hlt
    have hlenB : τ.vars "v" < (τ.arrs "activeB").length := by
      rw [hcurB, length_arrOf]
      exact hlt
    have hgetA : (τ.arrs "nextA")[τ.vars "v"]? = some (nextA (τ.vars "v")) := by
      rw [hnA, getElem?_arrOf nextA hlt]
    have hgetB : (τ.arrs "nextB")[τ.vars "v"]? = some (nextB (τ.vars "v")) := by
      rw [hnB', getElem?_arrOf nextB hlt]
    have hevalA : (Expr.get "nextA" (.var "v")).evalB B τ =
        some (nextA (τ.vars "v")) :=
      evalB_get (evalB_var hvB) hgetA (hnextAB _ hlt)
    have hevalB : (Expr.get "nextB" (.var "v")).evalB B τ =
        some (nextB (τ.vars "v")) :=
      evalB_get (evalB_var hvB) hgetB (hnextBB _ hlt)
    run_vcg
    refine ⟨⟨upd curA (τ.vars "v") (nextA (τ.vars "v")),
      upd curB (τ.vars "v") (nextB (τ.vars "v")), ?_, ?_, ?_, ?_,
      by simp; omega, by simp [hnn], ?_, ?_⟩, by simp⟩
    · simp [hcurA, hnA, hlt, set_arrOf_eq_upd]
    · simp [hcurB, hnB', hlt, set_arrOf_eq_upd]
    · simp [hnA]
    · simp [hnB']
    · intro i hi
      exact upd_below_succ rfl hfillA i (by simpa using hi)
    · intro i hi
      exact upd_below_succ rfl hfillB i (by simpa using hi)
    all_goals simp [hnA, hnB', hlt, hnextAB, hnextBB]
  have hshape : adoptNext =
      .seq (.assign "v" (.lit 0)) (.while (.lt (.var "v") (.var "n")) body) := by
    simp [adoptNext, body, seqs]
  rw [hshape]
  obtain ⟨σ', hrun, ⟨activeA', activeB', hactiveA', hactiveB', -, -, -,
      hnn, hfillA, hfillB⟩, hvn⟩ :=
    (Spec.forRangeZero "v" "n" (AdoptInv n nextA nextB) n 14 hnB
      (fun _ h => by
        obtain ⟨_, _, _, _, _, _, hv, _, _, _⟩ := h
        exact hv)
      (fun _ h => by
        obtain ⟨_, _, _, _, _, _, _, hnn, _, _⟩ := h
        exact hnn) hbody).run (σ := σ)
      ⟨activeA, activeB, by simp [hactiveA], by simp [hactiveB],
        by simp [hnextA], by simp [hnextB], by simp, by simp [hn],
        by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  refine ⟨σ', activeA', activeB', hrun.mono (by omega), hactiveA',
    hactiveB', ?_, ?_, hnn⟩
  · intro i hi
    apply hfillA i
    simpa [hvn] using hi
  · intro i hi
    apply hfillB i
    simpa [hvn] using hi

end Lax235315Proofs.Construction.CommitSource
