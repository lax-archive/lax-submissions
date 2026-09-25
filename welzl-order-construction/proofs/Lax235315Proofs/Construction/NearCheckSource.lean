import Lax235315Proofs.Construction.NearSweepSource
import Mathlib.Tactic

/-! Verification of the final threshold pass of the batched near-twin check. -/

namespace Lax235315Proofs.Construction.NearCheckSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.WelzlProgram

/-- The arithmetic distance stored by the batched verifier. -/
def nearDistance (degree inter rep : ℕ → ℕ) (b : ℕ) : ℕ :=
  degree b + degree (rep b) - 2 * inter b

/-- Invariant of the final scan.  If `good` is still set, every processed
active vertex has passed the distance threshold. -/
def NearCheckInv (B n bound : ℕ)
    (activeB rep degree inter : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "b" ≤ n ∧ τ.vars "n" = n ∧
    τ.vars "nearBound" = bound ∧ τ.vars "good" < B ∧
    τ.arrs "activeB" = arrOf n activeB ∧
    τ.arrs "repB" = arrOf n rep ∧
    τ.arrs "degree" = arrOf n degree ∧
    τ.arrs "inter" = arrOf n inter ∧
    (τ.vars "good" = 1 →
      ∀ v < τ.vars "b", activeB v = 1 →
        nearDistance degree inter rep v ≤ bound)

/-- One final-check iteration preserves all previously checked vertices and
checks the current active vertex. -/
theorem checkNearBody_spec
    {B n bound : ℕ} {activeB rep degree inter : ℕ → ℕ}
    (hnB : 2 * n + 1 < B) (hboundB : bound < B)
    (hactiveB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hdegreeN : ∀ v < n, degree v ≤ n)
    (hinterN : ∀ v < n, inter v ≤ n) :
    Spec B
      (fun τ => NearCheckInv B n bound activeB rep degree inter τ ∧
        τ.vars "b" < n)
      checkNearBody
      (fun τ τ' => NearCheckInv B n bound activeB rep degree inter τ' ∧
        τ'.vars "b" = τ.vars "b" + 1)
      60 := by
  intro σ hσ
  rcases hσ with ⟨⟨hbLe, hn, hbound, hgoodB, hactive, hrep, hdegree,
    hinter, hchecked⟩, hbN⟩
  let b := σ.vars "b"
  have hbB : b < B := by omega
  have hb1B : b + 1 < B := by omega
  have hactiveGet : (σ.arrs "activeB")[b]? = some (activeB b) := by
    rw [hactive, getElem?_arrOf activeB hbN]
  have hactiveEval : (Expr.get "activeB" (.var "b")).evalB B σ =
      some (activeB b) :=
    evalB_get (evalB_var (by simpa [b] using hbB)) hactiveGet
      (hactiveB b hbN)
  let activeTest := Cond.eq (.get "activeB" (.var "b")) (.lit 1)
  by_cases hba : activeB b = 1
  · have hactiveTest : activeTest.evalB B σ = some true := by
      simpa [activeTest, hba] using evalB_condEq hactiveEval
        (evalB_lit (by omega : 1 < B))
    let r := rep b
    have hrN : r < n := hrepN b hbN hba
    have hrB : r < B := by omega
    have hrepGet : (σ.arrs "repB")[b]? = some r := by
      rw [hrep, getElem?_arrOf rep hbN]
    have hrepEval : (Expr.get "repB" (.var "b")).evalB B σ = some r :=
      evalB_get (evalB_var (by simpa [b] using hbB)) hrepGet hrB
    let σ₁ := σ.setVar "r" r
    have rr : Run B (.assign "r" (.get "repB" (.var "b"))) σ σ₁ 6 :=
      (Run.assign hrepEval).mono (by norm_num [Expr.size])
    have hdegreeBEval : (Expr.get "degree" (.var "b")).evalB B σ₁ =
        some (degree b) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₁, b]; exact hbB)
      · simp [σ₁, hdegree, getElem?_arrOf degree hbN, b]
      · exact (hdegreeN b hbN).trans_lt (by omega)
    have hdegreeREval : (Expr.get "degree" (.var "r")).evalB B σ₁ =
        some (degree r) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₁, r]; exact hrB)
      · simp [σ₁, hdegree, getElem?_arrOf degree hrN, r]
      · exact (hdegreeN r hrN).trans_lt (by omega)
    have haddB : degree b + degree r < B := by
      have := hdegreeN b hbN
      have := hdegreeN r hrN
      omega
    have haddEval : (Expr.add (.get "degree" (.var "b"))
        (.get "degree" (.var "r"))).evalB B σ₁ =
        some (degree b + degree r) :=
      evalB_bin hdegreeBEval hdegreeREval (by simpa using haddB)
    have hinterEval : (Expr.get "inter" (.var "b")).evalB B σ₁ =
        some (inter b) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₁, b]; exact hbB)
      · simp [σ₁, hinter, getElem?_arrOf inter hbN, b]
      · exact (hinterN b hbN).trans_lt (by omega)
    have htwiceB : 2 * inter b < B := by
      have := hinterN b hbN
      omega
    have htwiceEval : (Expr.mul (.lit 2)
        (.get "inter" (.var "b"))).evalB B σ₁ =
        some (2 * inter b) :=
      evalB_bin (evalB_lit (by omega)) hinterEval (by simpa using htwiceB)
    let d := nearDistance degree inter rep b
    have hdB : d < B := by
      dsimp [d, nearDistance, r]
      exact (Nat.sub_le _ _).trans_lt haddB
    have hdiffEval : (Expr.sub
        (.add (.get "degree" (.var "b")) (.get "degree" (.var "r")))
        (.mul (.lit 2) (.get "inter" (.var "b")))).evalB B σ₁ =
        some d := by
      have hsubB : degree b + degree r - 2 * inter b < B :=
        (Nat.sub_le _ _).trans_lt haddB
      simpa [d, nearDistance, r] using
        evalB_bin (op := .sub) haddEval htwiceEval hsubB
    let σ₂ := σ₁.setVar "diff" d
    have rdiff : Run B (.assign "diff"
        (.sub (.add (.get "degree" (.var "b"))
            (.get "degree" (.var "r")))
          (.mul (.lit 2) (.get "inter" (.var "b"))))) σ₁ σ₂ 20 :=
      (Run.assign hdiffEval).mono (by norm_num [Expr.size])
    have hboundEval : (Expr.var "nearBound").evalB B σ₂ = some bound := by
      rw [show (Expr.var "nearBound").evalB B σ₂ =
        some (σ₂.vars "nearBound") from evalB_var (by
          simp [σ₂, σ₁, hbound]
          exact hboundB)]
      simp [σ₂, σ₁, hbound]
    have hdiffVarEval : (Expr.var "diff").evalB B σ₂ = some d := by
      rw [show (Expr.var "diff").evalB B σ₂ = some (σ₂.vars "diff") from
        evalB_var (by simp [σ₂]; exact hdB)]
      simp [σ₂]
    let farTest := Cond.lt (.var "nearBound") (.var "diff")
    by_cases hfar : bound < d
    · have hfarTest : farTest.evalB B σ₂ = some true := by
        simpa [farTest, hfar] using evalB_condLt hboundEval hdiffVarEval
      let σ₃ := σ₂.setVar "good" 0
      have rgood : Run B (.assign "good" (.lit 0)) σ₂ σ₃ 2 :=
        Run.assign (evalB_lit (by omega))
      let σ₄ := σ₃.setVar "b" (b + 1)
      have rb : Run B (inc "b") σ₃ σ₄ 4 := by
        apply Run.assign
        exact evalB_bin (by simpa [σ₃, σ₂, σ₁, b] using evalB_var hbB)
          (evalB_lit (by omega)) (by simp; exact hb1B)
      have ractive : Run B
          (seqs [
            .assign "r" (.get "repB" (.var "b")),
            .assign "diff"
              (.sub (.add (.get "degree" (.var "b"))
                  (.get "degree" (.var "r")))
                (.mul (.lit 2) (.get "inter" (.var "b")))),
            .ite (.lt (.var "nearBound") (.var "diff"))
              (.assign "good" (.lit 0)) .skip]) σ σ₃
          (6 + 20 + (1 + farTest.size + 2)) := by
        simpa [seqs, farTest] using rr.seq (rdiff.seq
          (Run.ite_true hfarTest rgood))
      refine ⟨σ₄, (Run.seq (Run.ite_true hactiveTest ractive) rb).mono
        (by norm_num [checkNearBody, seqs, activeTest, farTest,
          Cond.size, Expr.size]), ?_, by simp [σ₄, b]⟩
      refine ⟨by simp [σ₄, b]; omega, by simp [σ₄, σ₃, σ₂, σ₁, hn],
        by simp [σ₄, σ₃, σ₂, σ₁, hbound],
        by simp [σ₄, σ₃]; omega,
        by simp [σ₄, σ₃, σ₂, σ₁, hactive],
        by simp [σ₄, σ₃, σ₂, σ₁, hrep],
        by simp [σ₄, σ₃, σ₂, σ₁, hdegree],
        by simp [σ₄, σ₃, σ₂, σ₁, hinter], by simp [σ₄, σ₃]⟩
    · have hfarTest : farTest.evalB B σ₂ = some false := by
        simpa [farTest, hfar] using evalB_condLt hboundEval hdiffVarEval
      let σ₃ := σ₂.setVar "b" (b + 1)
      have rb : Run B (inc "b") σ₂ σ₃ 4 := by
        apply Run.assign
        exact evalB_bin (by simpa [σ₂, σ₁, b] using evalB_var hbB)
          (evalB_lit (by omega)) (by simp; exact hb1B)
      have ractive : Run B
          (seqs [
            .assign "r" (.get "repB" (.var "b")),
            .assign "diff"
              (.sub (.add (.get "degree" (.var "b"))
                  (.get "degree" (.var "r")))
                (.mul (.lit 2) (.get "inter" (.var "b")))),
            .ite (.lt (.var "nearBound") (.var "diff"))
              (.assign "good" (.lit 0)) .skip]) σ σ₂
          (6 + 20 + (1 + farTest.size + 1)) := by
        simpa [seqs, farTest] using rr.seq (rdiff.seq
          (Run.ite_false hfarTest Run.skip))
      refine ⟨σ₃, (Run.seq (Run.ite_true hactiveTest ractive) rb).mono
        (by norm_num [checkNearBody, seqs, activeTest, farTest,
          Cond.size, Expr.size]), ?_, by simp [σ₃, b]⟩
      refine ⟨by simp [σ₃, b]; omega, by simp [σ₃, σ₂, σ₁, hn],
        by simp [σ₃, σ₂, σ₁, hbound],
        by simp [σ₃, σ₂, σ₁, hgoodB],
        by simp [σ₃, σ₂, σ₁, hactive],
        by simp [σ₃, σ₂, σ₁, hrep],
        by simp [σ₃, σ₂, σ₁, hdegree],
        by simp [σ₃, σ₂, σ₁, hinter], ?_⟩
      intro hgood v hv hvan
      by_cases hvb : v = b
      · subst v
        simpa [d] using Nat.le_of_not_gt hfar
      · apply hchecked (by simpa [σ₃, σ₂, σ₁] using hgood) v
          (by simp [σ₃, b] at hv; omega) hvan
  · have hactiveTest : activeTest.evalB B σ = some false := by
      simpa [activeTest, hba] using evalB_condEq hactiveEval
        (evalB_lit (by omega : 1 < B))
    let σ₁ := σ.setVar "b" (b + 1)
    have rb : Run B (inc "b") σ σ₁ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [b] using evalB_var hbB)
        (evalB_lit (by omega)) (by simp; exact hb1B)
    refine ⟨σ₁, (Run.seq (Run.ite_false hactiveTest Run.skip) rb).mono
      (by norm_num [checkNearBody, seqs, activeTest, Cond.size, Expr.size]),
      ?_, by simp [σ₁, b]⟩
    refine ⟨by simp [σ₁, b]; omega, by simp [σ₁, hn],
      by simp [σ₁, hbound], by simp [σ₁, hgoodB],
      by simp [σ₁, hactive], by simp [σ₁, hrep],
      by simp [σ₁, hdegree], by simp [σ₁, hinter], ?_⟩
    intro hgood v hv hvan
    by_cases hvb : v = b
    · subst v
      exact (hba hvan).elim
    · apply hchecked (by simpa [σ₁] using hgood) v
        (by simp [σ₁, b] at hv; omega) hvan

/-- Starting at zero and scanning every vertex proves the advertised
threshold property whenever `good` remains one. -/
theorem checkNearLoop_run
    {B n bound : ℕ} {activeB rep degree inter : ℕ → ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hbound : σ.vars "nearBound" = bound)
    (hgoodB : σ.vars "good" < B)
    (hactive : σ.arrs "activeB" = arrOf n activeB)
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hdegree : σ.arrs "degree" = arrOf n degree)
    (hinter : σ.arrs "inter" = arrOf n inter)
    (hnB : 2 * n + 1 < B) (hboundB : bound < B)
    (hactiveB : ∀ v < n, activeB v < B)
    (hrepN : ∀ v < n, activeB v = 1 → rep v < n)
    (hdegreeN : ∀ v < n, degree v ≤ n)
    (hinterN : ∀ v < n, inter v ≤ n) :
    ∃ σ', Run B finishNearCheck σ σ' (64 * n + 6) ∧
      (σ'.vars "good" = 1 →
        ∀ v < n, activeB v = 1 →
          nearDistance degree inter rep v ≤ bound) := by
  let I := NearCheckInv B n bound activeB rep degree inter
  have hspec := checkNearBody_spec hnB hboundB hactiveB hrepN hdegreeN hinterN
  obtain ⟨σ', hrun, hI', hbFinal⟩ :=
    (Spec.forRangeZero "b" "n" I n 60 (by omega)
      (fun _ h => h.1)
      (fun _ h => h.2.1)
      hspec).run (σ := σ) (by
        refine ⟨by simp, by simp [hn], by simp [hbound], by simp [hgoodB],
          by simp [hactive], by simp [hrep], by simp [hdegree],
          by simp [hinter], ?_⟩
        intro _ v hv
        simp at hv)
  refine ⟨σ', ?_, ?_⟩
  · simpa [finishNearCheck, seqs] using hrun
  · intro hgood v hv hactivev
    exact hI'.2.2.2.2.2.2.2.2 hgood v (by simpa [hbFinal] using hv) hactivev

end Lax235315Proofs.Construction.NearCheckSource
