import Lax235315Proofs.Construction.GuardedArithmetic
import Lax235315Proofs.Construction.FrontierFrames
import Lax235315Proofs.Construction.ReductionLoopSource

/-! Bounded execution of the overflow-avoiding guards around the randomized
loop. Every product fit follows from the preceding quotient guard. -/
namespace Lax235315Proofs.Construction.GuardedDriverSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.ReductionLoopSource
open Lax235315Proofs.Construction.GuardedArithmetic
open Lax235315Proofs.Construction.FrontierFrames

structure DriverPost (B c n : ℕ) (x : List ℕ) (σ : Env) : Prop where
  workspace : Workspace B c n x σ
  status : Frontier B c n x σ ∨ (σ.vars "good" ≠ 1 ∧ σ.vars "acount" = 0)
  small : 1 < n → σ.vars "acount" ≤ 12 * c ^ 2 * Nat.clog 2 n

/-- The public source-budget shape contains the entire adaptive bit reserve. -/
lemma initial_tape_reserve {A n T : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (hA : 24 ≤ A) (hT : sourceCost A n x ≤ T) :
    24 * Nat.clog 2 n * n ≤ T := by
  have hn : n ≤ x.length + 1 := by have := hx.length_eq; omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul hA hn)
    (show Nat.clog 2 n ≤ Nat.clog 2 n + 1 by omega)
  dsimp [sourceCost] at hT
  nlinarith

lemma reduceAll_run {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)} {σ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier (sourceBound c x) c n x σ) (hc : 1 ≤ c)
    (hround : σ.vars "round" = 0) (hacount : σ.vars "acount" = n)
    (hreserve : 24 * Nat.clog 2 n * n ≤ σ.inp.length) :
    ∃ τ, Run (sourceBound c x) reduceAll σ τ
        (5500 * (x.length + 1) * (Nat.clog 2 n + 1)) ∧
      DriverPost (sourceBound c x) c n x τ := by
  let B := sourceBound c x
  have hKbase : 1 ≤ (x.length + 1) * (Nat.clog 2 n + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  have h12B : 12 < B := by dsimp [B, sourceBound]; omega
  have hnB : n < B := by simpa [h.workspace.vertices] using h.workspace.bounded.vars "n"
  have hcB : c < B := by simpa [h.workspace.parameter] using h.workspace.bounded.vars "c"
  have hL := h.workspace.logarithm
  have hnEval : (Expr.var "n").evalB B σ = some n := by
    rw [evalB_var (h.workspace.bounded.vars "n"), h.workspace.vertices]
  have hcEval : (Expr.var "c").evalB B σ = some c := by
    rw [evalB_var (h.workspace.bounded.vars "c"), h.workspace.parameter]
  have hnTest := evalB_condLt hnEval (evalB_lit (by omega : 2 < B))
  by_cases hsmalln : n < 2
  · have ht : (Cond.lt (.var "n") (.lit 2)).evalB B σ = some true := by
      rw [hnTest]; simp [hsmalln]
    refine ⟨σ, ?_, h.workspace, Or.inl h, ?_⟩
    · exact (Run.ite_true ht Run.skip).mono (by
        simp only [Cond.size, Expr.size]; nlinarith)
    · intro hn; omega
  have hn : 1 < n := by omega
  have hnFalse : (Cond.lt (.var "n") (.lit 2)).evalB B σ = some false := by
    rw [hnTest]; simp [hsmalln]
  have hcFalse : (Cond.eq (.var "c") (.lit 0)).evalB B σ = some false := by
    rw [evalB_condEq hcEval (evalB_lit (by omega))]; simp [show c ≠ 0 by omega]
  have hquotEval := evalB_bin hnEval hcEval
    (by change n / c < B; exact (Nat.div_le_self _ _).trans_lt hnB : Bop.div.apply n c < B)
  have hquotTest := evalB_condLt hquotEval hcEval
  by_cases hquot : n / c < c
  · have ht : (Cond.lt (.div (.var "n") (.var "c")) (.var "c")).evalB B σ = some true := by
      rw [hquotTest]; simp [Bop.apply, hquot]
    refine ⟨σ, ?_, h.workspace, Or.inl h, ?_⟩
    · exact (Run.ite_false hnFalse (Run.ite_false hcFalse
        (Run.ite_true ht Run.skip))).mono (by norm_num [Cond.size, Expr.size]; nlinarith)
    · intro _; rw [hacount]; exact initial_count_le_threshold_of_quotient hc hn hquot
  have hquotFalse : (Cond.lt (.div (.var "n") (.var "c")) (.var "c")).evalB B σ = some false := by
    rw [hquotTest]; simp [Bop.apply, hquot]
  have hsqn := square_le_of_not_quotient hc hquot
  obtain ⟨_, _, _, hqB, htwonB, hedgeB, h12LB, hdenomB⟩ :=
    source_fits_of_square_le hx hc hn hsqn
  have hsqB : c ^ 2 < B := hsqn.trans_lt hnB
  let σ₁ := σ.setVar "csq" (c ^ 2)
  have hf₁ : Frontier B c n x σ₁ := Frontier.setVar h "csq" hsqB (by simp [FrontierScratchName])
  have r₁ : Run B (.assign "csq" (.mul (.var "c") (.var "c"))) σ σ₁ 4 := by
    apply Run.assign
    simpa [pow_two, Bop.apply] using
      (evalB_bin hcEval hcEval (by simpa [pow_two, Bop.apply] using hsqB : Bop.mul.apply c c < B))
  have hnEval₁ : (Expr.var "n").evalB B σ₁ = some n := by simpa [σ₁] using hnEval
  have hsEval₁ : (Expr.var "csq").evalB B σ₁ = some (c ^ 2) := by
    simpa [σ₁] using (evalB_var (B := B) (σ := σ₁) (x := "csq") (by simp [σ₁]; exact hsqB))
  have hLEval₁ : (Expr.var "L").evalB B σ₁ = some (Nat.clog 2 n) := by
    rw [evalB_var (hf₁.workspace.bounded.vars "L"), hf₁.workspace.logarithm]
  have hsQuot := evalB_bin hnEval₁ hsEval₁
    (by change n / c ^ 2 < B; exact (Nat.div_le_self _ _).trans_lt hnB : Bop.div.apply n (c ^ 2) < B)
  have h12L := evalB_bin (evalB_lit h12B) hLEval₁
    (by exact h12LB : Bop.mul.apply 12 (Nat.clog 2 n) < B)
  have hsTest := evalB_condLt hsQuot h12L
  by_cases hsquot : n / c ^ 2 < 12 * Nat.clog 2 n
  · have ht : (Cond.lt (.div (.var "n") (.var "csq"))
        (.mul (.lit 12) (.var "L"))).evalB B σ₁ = some true := by
      rw [hsTest]; simp [Bop.apply, hsquot]
    refine ⟨σ₁, ?_, hf₁.workspace, Or.inl hf₁, ?_⟩
    · exact (Run.ite_false hnFalse (Run.ite_false hcFalse
        (Run.ite_false hquotFalse (r₁.seq (Run.ite_true ht Run.skip))))).mono
        (by norm_num [Cond.size, Expr.size]; nlinarith)
    · intro _; simp only [σ₁, Env.setVar]
      rw [hacount]; exact (initial_count_lt_threshold_of_square_quotient hc hsquot).le
  have hsFalse : (Cond.lt (.div (.var "n") (.var "csq"))
      (.mul (.lit 12) (.var "L"))).evalB B σ₁ = some false := by
    rw [hsTest]; simp [Bop.apply, hsquot]
  have htN := threshold_le_of_not_square_quotient hc hn hsquot
  have htB : 12 * c ^ 2 * Nat.clog 2 n < B := htN.trans_lt hnB
  have hLpos : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by omega) hn
  have h12sqB : 12 * c ^ 2 < B := by nlinarith
  let σ₂ := σ₁.setVar "threshold" (12 * c ^ 2 * Nat.clog 2 n)
  have hf₂ : Frontier B c n x σ₂ := Frontier.setVar hf₁ "threshold" htB (by simp [FrontierScratchName])
  have r₂ : Run B (.assign "threshold" (.mul (.mul (.lit 12) (.var "csq")) (.var "L"))) σ₁ σ₂ 6 := by
    exact Run.assign (evalB_bin (evalB_bin (evalB_lit h12B) hsEval₁ h12sqB) hLEval₁ htB)
  let bound := (12 * c ^ 2 * Nat.clog 2 n) / 2
  have hboundB : bound < B := (Nat.div_le_self _ _).trans_lt htB
  let σ₃ := σ₂.setVar "nearBound" bound
  have hf₃ : Frontier B c n x σ₃ := Frontier.setVar hf₂ "nearBound" hboundB (by simp [FrontierScratchName])
  have r₃ : Run B (.assign "nearBound" (.div (.var "threshold") (.lit 2))) σ₂ σ₃ 4 := by
    apply Run.assign
    have htEval : (Expr.var "threshold").evalB B σ₂ = some (12 * c ^ 2 * Nat.clog 2 n) := by
      simpa [σ₂] using (evalB_var (B := B) (σ := σ₂) (x := "threshold") (by simp [σ₂]; exact htB))
    exact evalB_bin htEval (evalB_lit (by omega)) hboundB
  have hloop : LoopState B c n bound x σ₃ := by
    refine ⟨hf₃.workspace, ?_, ?_, ?_, Or.inl ⟨hf₃, ?_⟩⟩
    · simp [σ₃, σ₂, σ₁]
    · simp [σ₃]
    · simp [σ₃, σ₂]
    · simpa [σ₃, σ₂, σ₁, hacount] using hreserve
  obtain ⟨τ, rloop, hpost, hsmall⟩ := reductionLoop_run_initial hx hG hloop hc hn
    (by simp [σ₃, σ₂, σ₁, hround]) (by simp [σ₃, σ₂, σ₁, hacount])
    hqB htwonB hedgeB hdenomB hboundB
  refine ⟨τ, ?_, hpost.workspace, ?_, fun _ => hsmall⟩
  · exact (Run.ite_false hnFalse (Run.ite_false hcFalse
      (Run.ite_false hquotFalse (r₁.seq (Run.ite_false hsFalse
        (r₂.seq (r₃.seq rloop))))))).mono (by
      norm_num [Cond.size, Expr.size]
      nlinarith)
  · exact hpost.status.imp And.left id

/-- Compose deterministic setup and the entire guarded reduction phase on any
public-budget tape. The reserve is derived from its length, not assumed. -/
lemma setup_reduceAll_run {A c n T : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hA : 24 ≤ A) (hT : sourceCost A n x ≤ T) (ρ : Fin T → Bool) :
    ∃ τ, Run (sourceBound c x) (.seq setup reduceAll)
        (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
          ((c :: x) ++ bitTape ρ)) τ (sourceCost 5600 n x) ∧
      DriverPost (sourceBound c x) c n x τ := by
  obtain ⟨σ, rsetup, hfront, hin, hround, hacount⟩ := setup_frontier_ready (c := c) hx ρ
  have hreserve : 24 * Nat.clog 2 n * n ≤ σ.inp.length := by
    rw [hin]
    simpa [bitTape] using initial_tape_reserve hx hA hT
  obtain ⟨τ, rreduce, hpost⟩ := reduceAll_run hx hG hfront hc hround hacount hreserve
  refine ⟨τ, (rsetup.seq rreduce).mono ?_, hpost⟩
  dsimp [sourceCost]
  nlinarith

end Lax235315Proofs.Construction.GuardedDriverSource
