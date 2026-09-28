import Lax235315Proofs.Construction.HistoryDriverSource
import Lax235315Proofs.Construction.SourceAdaptiveState
import Lax235315Proofs.Construction.InputSuffixFrame
import Mathlib.Tactic

/-! Construct the canonical adaptive round state at the first guarded loop
boundary, before any random block has been consumed. -/

namespace Lax235315Proofs.Construction.InitialRoundStateSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.FrontierFrames
open Lax235315Proofs.Construction.GuardedArithmetic
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.StoredHistory
open Lax235315Proofs.Construction.HistoryDriverSource
open Lax235315Proofs.Construction.SourceAdaptiveState
open Lax235315Proofs.Construction.InputSuffixFrame
open Lax195003.WelzlOrdersInGraphs

/-- The literal guarded prelude of `reduceAll`, ending at the `while`-loop
header. -/
def guardedRoundBoundaryPrefix : Com :=
  .ite (.lt (.var "n") (.lit 2)) .skip
    (.ite (.eq (.var "c") (.lit 0)) (.assign "good" (.lit 0))
      (.ite (.lt (.div (.var "n") (.var "c")) (.var "c")) .skip
        (.seq (.assign "csq" (.mul (.var "c") (.var "c")))
          (.ite (.lt (.div (.var "n") (.var "csq"))
              (.mul (.lit 12) (.var "L"))) .skip
            (.seq (.assign "threshold"
                (.mul (.mul (.lit 12) (.var "csq")) (.var "L")))
              (.assign "nearBound" (.div (.var "threshold") (.lit 2))))))))

/-- Starting from the empty-tape initialization, the source setup and the
literal false guards run to the first `reductionRound` boundary. Appending any
unread tape preserves that boundary run; the canonical adaptive state keeps
its input empty so each query block is appended separately. -/
lemma initial_round_state_after_setup_guarded_prefix
    {c n T : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < n)
    (ρ : Fin T → Bool) :
    ∃ s : RoundState c n x G, ∃ τ₀ τ : Env,
      Run (sourceBound c x) setup
        (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
          ((c :: x) ++ bitTape ρ)) τ₀
        (40 * (x.length + Nat.clog 2 n + 1)) ∧
      Run (sourceBound c x) guardedRoundBoundaryPrefix τ₀ τ 100 ∧
      Run (sourceBound c x) (.seq setup guardedRoundBoundaryPrefix)
        (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
          ((c :: x) ++ bitTape ρ)) τ
        (40 * (x.length + Nat.clog 2 n + 1) + 100) ∧
      τ.inp = bitTape ρ ∧ s.env = withInput τ [] := by
  let B := sourceBound c x
  let emptyBits : Fin 0 → Bool := Fin.elim0
  obtain ⟨σ, rsetup, hfront, hin, hround, hacount⟩ :=
    setup_frontier_ready (c := c) hx emptyBits
  obtain ⟨σ', rsetup', _hready, _hbounded, ⟨hstore⟩⟩ :=
    setup_stored_ready (k := 6 * c ^ 2 * Nat.clog 2 n) (c := c) hx emptyBits
  have hsetupEq := run_final_eq rsetup rsetup'
  subst σ'
  have hinEmpty : σ.inp = [] := by simpa [bitTape, emptyBits] using hin
  have hnB : n < B := by
    simpa [B, hfront.workspace.vertices] using hfront.workspace.bounded.vars "n"
  have hcsqLt : c ^ 2 < n := by
    have hLpos : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by omega) hn
    nlinarith
  have hcsqLe : c ^ 2 ≤ n := by omega
  obtain ⟨_, _, _, hqB, htwonB, hedgeB, h12LB, hdenomB⟩ :=
    source_fits_of_square_le hx hc hn hcsqLe
  have h12B : 12 < B := by dsimp [B, sourceBound]; omega
  have hcEval : (Expr.var "c").evalB B σ = some c := by
    rw [evalB_var (hfront.workspace.bounded.vars "c"), hfront.workspace.parameter]
  have hnEval : (Expr.var "n").evalB B σ = some n := by
    rw [evalB_var (hfront.workspace.bounded.vars "n"), hfront.workspace.vertices]
  have hnTest := evalB_condLt hnEval (evalB_lit (by omega : 2 < B))
  have hnFalse : (Cond.lt (.var "n") (.lit 2)).evalB B σ = some false := by
    rw [hnTest]; simp [show ¬ n < 2 by omega]
  have hcFalse : (Cond.eq (.var "c") (.lit 0)).evalB B σ = some false := by
    rw [evalB_condEq hcEval (evalB_lit (by omega))]
    simp [show c ≠ 0 by omega]
  have hquotEval := evalB_bin hnEval hcEval
    (by change n / c < B; exact (Nat.div_le_self _ _).trans_lt hnB : Bop.div.apply n c < B)
  have hquotTest := evalB_condLt hquotEval hcEval
  have hquot : ¬ n / c < c := by
    intro h
    have hmul := (Nat.div_lt_iff_lt_mul (by omega : 0 < c)).mp h
    nlinarith [hcsqLt]
  have hquotFalse : (Cond.lt (.div (.var "n") (.var "c")) (.var "c")).evalB B σ = some false := by
    rw [hquotTest]; simp [Bop.apply, hquot]
  have hsqB : c ^ 2 < B := hcsqLe.trans_lt hnB
  let σ₁ := σ.setVar "csq" (c ^ 2)
  have hf₁ : Frontier B c n x σ₁ :=
    Frontier.setVar hfront "csq" hsqB (by simp [FrontierScratchName])
  have hs₁ := stored_setScratch hstore "csq" (c ^ 2) (by decide) (by decide)
  have r₁ : Run B (.assign "csq" (.mul (.var "c") (.var "c"))) σ σ₁ 4 := by
    apply Run.assign
    simpa [pow_two, Bop.apply] using
      (evalB_bin hcEval hcEval (by simpa [pow_two, Bop.apply] using hsqB : Bop.mul.apply c c < B))
  have hnEval₁ : (Expr.var "n").evalB B σ₁ = some n := by simpa [σ₁] using hnEval
  have hsEval₁ : (Expr.var "csq").evalB B σ₁ = some (c ^ 2) := by
    simpa [σ₁] using (evalB_var (B := B) (σ := σ₁) (x := "csq")
      (by simp [σ₁]; exact hsqB))
  have hLEval₁ : (Expr.var "L").evalB B σ₁ = some (Nat.clog 2 n) := by
    rw [evalB_var (hf₁.workspace.bounded.vars "L"), hf₁.workspace.logarithm]
  have hsqQuotEval := evalB_bin hnEval₁ hsEval₁
    (by change n / c ^ 2 < B; exact (Nat.div_le_self _ _).trans_lt hnB : Bop.div.apply n (c ^ 2) < B)
  have h12L := evalB_bin (evalB_lit h12B) hLEval₁
    (by exact h12LB : Bop.mul.apply 12 (Nat.clog 2 n) < B)
  have hsTest := evalB_condLt hsqQuotEval h12L
  have hsquot : ¬ n / c ^ 2 < 12 * Nat.clog 2 n := by
    intro h
    have hmul := (Nat.div_lt_iff_lt_mul (pow_pos (by omega : 0 < c) _)).mp h
    nlinarith [hlarge]
  have hsFalse : (Cond.lt (.div (.var "n") (.var "csq"))
      (.mul (.lit 12) (.var "L"))).evalB B σ₁ = some false := by
    rw [hsTest]; simp [Bop.apply, hsquot]
  have htB : 12 * c ^ 2 * Nat.clog 2 n < B := by
    have := hlarge
    omega
  have hLpos : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by omega) hn
  have h12sqB : 12 * c ^ 2 < B := by
    have hsmall : 12 * c ^ 2 < n := by nlinarith [hlarge, hLpos]
    exact hsmall.trans hnB
  let σ₂ := σ₁.setVar "threshold" (12 * c ^ 2 * Nat.clog 2 n)
  have hf₂ : Frontier B c n x σ₂ :=
    Frontier.setVar hf₁ "threshold" htB (by simp [FrontierScratchName])
  have r₂ : Run B
      (.assign "threshold" (.mul (.mul (.lit 12) (.var "csq")) (.var "L"))) σ₁ σ₂ 6 := by
    exact Run.assign (evalB_bin (evalB_bin (evalB_lit h12B) hsEval₁ h12sqB) hLEval₁ htB)
  have hs₂ := stored_setScratch hs₁ "threshold"
    (12 * c ^ 2 * Nat.clog 2 n) (by decide) (by decide)
  have hhalfB : (12 * c ^ 2 * Nat.clog 2 n) / 2 < B :=
    (Nat.div_le_self _ _).trans_lt htB
  let σ₃ := σ₂.setVar "nearBound" ((12 * c ^ 2 * Nat.clog 2 n) / 2)
  have hf₃ : Frontier B c n x σ₃ :=
    Frontier.setVar hf₂ "nearBound" hhalfB (by simp [FrontierScratchName])
  have r₃ : Run B (.assign "nearBound" (.div (.var "threshold") (.lit 2))) σ₂ σ₃ 4 := by
    apply Run.assign
    have htEval : (Expr.var "threshold").evalB B σ₂ =
        some (12 * c ^ 2 * Nat.clog 2 n) := by
      simpa [σ₂] using (evalB_var (B := B) (σ := σ₂) (x := "threshold")
        (by simp [σ₂]; exact htB))
    exact evalB_bin htEval (evalB_lit (by omega)) hhalfB
  have hs₃ := stored_setScratch hs₂ "nearBound"
    ((12 * c ^ 2 * Nat.clog 2 n) / 2) (by decide) (by decide)
  have rprefix : Run B guardedRoundBoundaryPrefix σ σ₃ 100 := by
    have rguards : Run B guardedRoundBoundaryPrefix σ σ₃ _ :=
      Run.ite_false (c := .skip) hnFalse
        (Run.ite_false (c := .assign "good" (.lit 0)) hcFalse
          (Run.ite_false (c := .skip) hquotFalse
            (r₁.seq (Run.ite_false (c := .skip) hsFalse (r₂.seq r₃)))))
    exact rguards.mono (by norm_num [guardedRoundBoundaryPrefix, Cond.size, Expr.size])
  have hnear : (12 * c ^ 2 * Nat.clog 2 n) / 2 = 6 * c ^ 2 * Nat.clog 2 n := by
    rw [show 12 * c ^ 2 * Nat.clog 2 n =
      (6 * c ^ 2 * Nat.clog 2 n) * 2 by ring]
    omega
  have hin₃ : σ₃.inp = [] := by
    calc
      σ₃.inp = σ.inp := by exact (rprefix.frame_inp (by decide)).symm
      _ = [] := hinEmpty
  let hboundary : RoundState c n x G :=
    ⟨σ₃, hn, hf₃, hs₃,
      by simp [σ₃, σ₂, σ₁, Env.setVar],
      by simp [σ₃, σ₂, σ₁, Env.setVar, hnear],
      by simp [σ₃, σ₂, σ₁, Env.setVar],
      by simp [σ₃, σ₂, σ₁, hacount, Env.setVar, hlarge],
      hin₃⟩
  have rsourceEmpty : Run B (.seq setup guardedRoundBoundaryPrefix)
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) (c :: x)) σ₃
      (40 * (x.length + Nat.clog 2 n + 1) + 100) := by
    have hstart : initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ []) =
        initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) (c :: x) := by simp
    rw [← hstart]
    exact rsetup.seq rprefix
  have rsourceTape := run_appendInput rsourceEmpty (bitTape ρ)
  have rsetupTape := run_appendInput rsetup (bitTape ρ)
  have hsetupTapeStart : appendInput
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape emptyBits)) (bitTape ρ) =
      initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape ρ) := by
    simp [appendInput, initEnv, bitTape, emptyBits, List.append_assoc]
  rw [hsetupTapeStart] at rsetupTape
  have rprefixTape := run_appendInput rprefix (bitTape ρ)
  have hinitAppend : appendInput
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n)) (c :: x))
      (bitTape ρ) =
      initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape ρ) := by
    simp [appendInput, initEnv, List.append_assoc]
  have hτinp : (appendInput σ₃ (bitTape ρ)).inp = bitTape ρ := by
    simp [appendInput, hin₃]
  have hσ₃inp : σ₃.inp = [] := by
    calc
      σ₃.inp = σ.inp := by exact (rprefix.frame_inp (by decide)).symm
      _ = [] := hinEmpty
  have hstate : hboundary.env = withInput (appendInput σ₃ (bitTape ρ)) [] := by
    simp [hboundary, withInput, appendInput, σ₃, σ₂, σ₁, Env.setVar, hinEmpty]
  refine ⟨hboundary, appendInput σ (bitTape ρ), appendInput σ₃ (bitTape ρ),
    rsetupTape, rprefixTape, ?_, hτinp, hstate⟩
  simpa [hinitAppend] using rsourceTape

end Lax235315Proofs.Construction.InitialRoundStateSource
