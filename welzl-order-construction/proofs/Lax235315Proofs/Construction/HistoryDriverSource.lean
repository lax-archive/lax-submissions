import Lax235315Proofs.Construction.HistoryLoopSource
import Lax235315Proofs.Construction.GuardedDriverSource
import Lax235315Proofs.Construction.DriverFinish
import Lax235315Proofs.Construction.SmallInputSource

/-! The guarded source driver preserves the log's graph history and feeds the
verified terminal reconstruction. -/
namespace Lax235315Proofs.Construction.HistoryDriverSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.ReductionLoopSource
open Lax235315Proofs.Construction.GuardedArithmetic
open Lax235315Proofs.Construction.FrontierFrames
open Lax235315Proofs.Construction.GuardedDriverSource
open Lax235315Proofs.Construction.HistoryLoopSource
open Lax235315Proofs.Construction.StoredHistory
open Lax235315Proofs.Construction.DriverFinish
open Lax195003.WelzlOrdersInGraphs

structure HistoryDriverPost (B c n : ℕ) (x : List ℕ)
    (G : SimpleGraph (Fin n)) (σ : Env) extends DriverPost B c n x σ where
  history : σ.vars "good" = 1 → Nonempty (Stored G (6 * c ^ 2 * Nat.clog 2 n) σ)

def stored_setScratch {n k : ℕ} {G : SimpleGraph (Fin n)} {σ : Env}
    (h : Stored G k σ) (name : String) (value : ℕ)
    (hround : name ≠ "round") (hused : name ≠ "removedCount") :
    Stored G k (σ.setVar name value) :=
  h.frame (by simp [Env.setVar, Ne.symm hround]) (by simp [Env.setVar, Ne.symm hused])
    rfl rfl rfl rfl rfl rfl

lemma reduceAll_run_stored {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)} {σ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier (sourceBound c x) c n x σ)
    (hstore : Stored G (6 * c ^ 2 * Nat.clog 2 n) σ) (hc : 1 ≤ c)
    (hround : σ.vars "round" = 0) (hacount : σ.vars "acount" = n)
    (hreserve : 24 * Nat.clog 2 n * n ≤ σ.inp.length) :
    ∃ τ, Run (sourceBound c x) reduceAll σ τ
        (5500 * (x.length + 1) * (Nat.clog 2 n + 1)) ∧
      HistoryDriverPost (sourceBound c x) c n x G τ ∧
      (n ≤ 12 * c ^ 2 * Nat.clog 2 n → τ.vars "good" = 1) := by
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
    refine ⟨σ, ?_, (⟨⟨h.workspace, Or.inl h, ?_⟩,
      fun _ => ⟨hstore⟩⟩ : HistoryDriverPost _ _ _ _ _ σ), fun _ => h.success⟩
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
    refine ⟨σ, ?_, (⟨⟨h.workspace, Or.inl h, ?_⟩,
      fun _ => ⟨hstore⟩⟩ : HistoryDriverPost _ _ _ _ _ σ), fun _ => h.success⟩
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
  let hs₁ := stored_setScratch hstore "csq" (c ^ 2) (by decide) (by decide)
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
    refine ⟨σ₁, ?_, (⟨⟨hf₁.workspace, Or.inl hf₁, ?_⟩,
      fun _ => ⟨hs₁⟩⟩ : HistoryDriverPost _ _ _ _ _ σ₁), fun _ => hf₁.success⟩
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
  have hboundeq : bound = 6 * c ^ 2 * Nat.clog 2 n := by
    dsimp [bound]
    rw [show 12 * c ^ 2 * Nat.clog 2 n = (6 * c ^ 2 * Nat.clog 2 n) * 2 by ring]
    omega
  have hs₃ : Stored G bound σ₃ := by
    rw [hboundeq]
    exact stored_setScratch (stored_setScratch hs₁ "threshold"
      (12 * c ^ 2 * Nat.clog 2 n) (by decide) (by decide))
      "nearBound" bound (by decide) (by decide)
  have hloopStored : HistoryLoopState B c n bound x G σ₃ :=
    ⟨hloop, fun _ => ⟨hs₃⟩⟩
  obtain ⟨τ, rloop, hpost, hsmall⟩ := reductionLoop_run_initial_stored hx hG hloopStored hc hn
    (by simp [σ₃, σ₂, σ₁, hround]) (by simp [σ₃, σ₂, σ₁, hacount])
    hqB htwonB hedgeB hdenomB hboundB
  refine ⟨τ, ?_, (⟨⟨hpost.workspace, ?_, fun _ => hsmall⟩,
    ?_⟩ : HistoryDriverPost _ _ _ _ _ τ), ?_⟩
  · exact (Run.ite_false hnFalse (Run.ite_false hcFalse
      (Run.ite_false hquotFalse (r₁.seq (Run.ite_false hsFalse
        (r₂.seq (r₃.seq rloop))))))).mono (by
      norm_num [Cond.size, Expr.size]
      nlinarith)
  · exact hpost.status.imp And.left id
  · intro hg; simpa only [hboundeq] using hpost.history hg
  · intro hnsmall
    have hnthreshold : n = 12 * c ^ 2 * Nat.clog 2 n := by
      have hge := threshold_le_of_not_square_quotient hc hn hsquot
      omega
    have htest : (Cond.lt (.var "threshold") (.var "acount")).evalB B σ₃ =
        some false := by
      have hthreshold : σ₃.vars "threshold" = 12 * c ^ 2 * Nat.clog 2 n := by
        simp [σ₃, σ₂]
      have hcount : σ₃.vars "acount" = n := by
        simp [σ₃, σ₂, σ₁, hacount]
      rw [evalB_condLt (evalB_var (hloop.workspace.bounded.vars "threshold"))
        (evalB_var (hloop.workspace.bounded.vars "acount"))]
      rw [hthreshold, hcount]
      have hnot : ¬ 12 * c ^ 2 * Nat.clog 2 n < n := by omega
      simp [hnot]
    have rskip : Run B
        (.while (.lt (.var "threshold") (.var "acount")) reductionRound)
        σ₃ σ₃ (1 + (Cond.lt (.var "threshold") (.var "acount")).size) :=
      ⟨_, le_rfl, BigStepB.while_false htest⟩
    have heq : τ = σ₃ := by
      obtain ⟨_, _, hrun⟩ := rloop
      obtain ⟨_, _, hskip⟩ := rskip
      exact (hrun.bigStep.unique hskip.bigStep).1
    subst τ
    exact hf₃.success

/-- Separate proofs of one deterministic source run have the same final state. -/
lemma run_final_eq {B C C' : ℕ} {cmd : Com} {σ τ υ : Env}
    (h : Run B cmd σ τ C) (h' : Run B cmd σ υ C') : τ = υ := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, h'⟩ := h'
  exact (h.bigStep.unique h'.bigStep).1

/-- Every sufficiently long tape executes the complete source program within
the near-linear budget; a successful final state contains the desired order. -/
lemma welzlCom_run_correct {c n T : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hT : sourceCost 6000 n x ≤ T) (ρ : Fin T → Bool) :
    ∃ τ, Run (sourceBound c x) welzlCom
      (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
        ((c :: x) ++ bitTape ρ)) τ (sourceCost 6000 n x) ∧
      (τ.vars "good" = 1 →
        EncodesGraphWelzlOrder G 1 (12 * c ^ 2 * (Nat.clog 2 n) ^ 2) τ.out) ∧
      (n ≤ 12 * c ^ 2 * Nat.clog 2 n → τ.vars "good" = 1) := by
  by_cases hnsmall : n ≤ 1
  · obtain ⟨τ, hr, hg, ho⟩ := SmallInputSource.smallInput_welzlCom_run hx hc hnsmall ρ
    refine ⟨τ, hr, (fun _ => ?_), fun _ => hg⟩
    simpa [Nat.clog_of_right_le_one hnsmall] using ho
  have hn : 1 < n := by omega
  obtain ⟨σ, rsetup, hfront, hin, hround, hacount⟩ := setup_frontier_ready (c := c) hx ρ
  obtain ⟨σ', rsetup', hready, hb, ⟨hstore⟩⟩ :=
    setup_stored_ready (k := 6 * c ^ 2 * Nat.clog 2 n) (c := c) hx ρ
  have heq := run_final_eq rsetup rsetup'
  subst σ'
  have hreserve : 24 * Nat.clog 2 n * n ≤ σ.inp.length := by
    rw [hin]
    simpa [bitTape] using initial_tape_reserve hx (by omega : 24 ≤ 6000) hT
  obtain ⟨τ, rreduce, hpost, hguardgood⟩ :=
    reduceAll_run_stored hx hG hfront hstore hc hround hacount hreserve
  have hnB : n < sourceBound c x := by
    simpa only [hpost.workspace.vertices] using hpost.workspace.bounded.vars "n"
  obtain ⟨υ, rfinish, hgood, hinp, hcorrect⟩ :=
    finish_run hpost.toDriverPost hc hn hnB hpost.history
  refine ⟨υ, ?_, hcorrect, fun hguard => hgood.trans (hguardgood hguard)⟩
  have hnlen : n + 1 ≤ x.length + 1 := by have := hx.length_eq; omega
  have hcost : 40 * (x.length + Nat.clog 2 n + 1) +
      (5500 * (x.length + 1) * (Nat.clog 2 n + 1) + 104 * (n + 1)) ≤
      sourceCost 6000 n x := by
    dsimp [sourceCost]
    nlinarith
  exact (rsetup.seq (rreduce.seq rfinish)).mono hcost

/-- Total execution of the literal source program, on all valid inputs. -/
lemma sourceTotal : SourceTotal 6000 := by
  intro c n G x h T hT ρ
  obtain ⟨τ, hr, _, _⟩ := welzlCom_run_correct h.2.2 h.2.1 h.1 hT ρ
  exact ⟨τ, hr⟩

/-- Determinism transfers the constructed output proof to every successful
source execution appearing in the public correctness contract. -/
lemma sourceCorrect : SourceCorrect 6000 := by
  intro c n G x h T hT ρ σ hr hg
  obtain ⟨τ, hrun, hcorrect, _⟩ := welzlCom_run_correct h.2.2 h.2.1 h.1 hT ρ
  have heq := run_final_eq hr hrun
  subst τ
  exact hcorrect hg

/-- The source's quotient guard skips randomized rounds. Consequently every
finite random tape succeeds on this branch. -/
lemma guard_sourceGoodTapes_eq_univ {c n T : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hT : sourceCost 6000 n x ≤ T)
    (hguard : n ≤ 12 * c ^ 2 * Nat.clog 2 n) :
    sourceGoodTapes c n x (sourceCost 6000 n x) T = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ρ
  obtain ⟨τ, hr, _, hgood⟩ := welzlCom_run_correct hx hG hc hT ρ
  exact ⟨τ, hr, hgood hguard⟩

lemma guard_sourceGoodTapes_ncard {c n T : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)} (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hT : sourceCost 6000 n x ≤ T)
    (hguard : n ≤ 12 * c ^ 2 * Nat.clog 2 n) :
    (sourceGoodTapes c n x (sourceCost 6000 n x) T).ncard = 2 ^ T := by
  rw [guard_sourceGoodTapes_eq_univ hx hG hc hT hguard]
  simp

end Lax235315Proofs.Construction.HistoryDriverSource
