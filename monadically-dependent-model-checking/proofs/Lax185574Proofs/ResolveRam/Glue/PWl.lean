import Lax185574Proofs.ResolveRam.Glue.PFASpec

/-!
Small commands on the word library for the pieces of lem:resolve-lift.

`sget v x j` reads entry `j` of word `x` of the library into `v`, and `0`
if the word is shorter (`sget_run`), so it computes `getD j 0` on any
word. `patch` writes the number of the words of a list over the
placeholder in front of their frames, which turns the frames into the
word of the list (`patch_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam
open Lax185574.WordEncoding

/-- `v := (word x).getD j 0`. -/
def sget (v x : String) (j : ℕ) : Com :=
  .ite (.lt (.lit j) (.get "ln" (.var x))) (.assign v (.get "a" (.add (.get "st" (.var x)) (.lit j))))
    (.assign v (.lit 0))

/-- **Reading an entry of a word, `0` beyond its end.** -/
theorem sget_run {B : ℕ} {ws : List (List ℕ)} {τ : Env} (hw : WordsAt ws τ) {v x : String} {n j : ℕ}
    (hx : τ.vars x = n) (hn : n < ws.length) (hB : total ws + ws.length + j + 1 < B)
    (hv : ∀ u ∈ ws[n], u < B) :
    Run B (sget v x j) τ (τ.setVar v (ws[n].getD j 0)) 12 := by
  have hoff := off_add_le hn
  have el : (Expr.get "ln" (.var x)).evalB B τ = some ws[n].length :=
    evalB_get (ev_var hx (by omega)) (hw.ln n hn) (by omega)
  have es : (Expr.get "st" (.var x)).evalB B τ = some (off ws n) :=
    evalB_get (ev_var hx (by omega)) (hw.st n hn) (by omega)
  unfold sget
  by_cases hj : j < ws[n].length
  · rw [List.getD_eq_getElem _ _ hj]
    exact (Run.ite_true (by rw [evalB_condLt (evalB_lit (by omega)) el]; simp [hj])
      (Run.assign (evalB_get (ev_add es (evalB_lit (by omega)) (by omega)) (hw.a n hn j hj)
        (hv _ (List.getElem_mem hj))))).mono (by simp [Cond.size, Expr.size])
  · rw [List.getD_eq_default _ _ (by omega)]
    exact (Run.ite_false (by rw [evalB_condLt (evalB_lit (by omega)) el]; simp [hj])
      (Run.assign (evalB_lit (by omega)))).mono (by simp [Cond.size, Expr.size])

/-- Write the count `fc` at the placeholder `fp`. -/
def patch : Com := .store "OB" (.var "fp") (.var "fc")

/-- **The count in front of the frames.** -/
theorem patch_run {W : ℕ} {pre : List ℕ} {l : List (List ℕ)} {τ : Env}
    (hF : Filled "OB" "po" (pre ++ [0] ++ frames l) τ) (hfp : τ.vars "fp" = pre.length)
    (hfc : τ.vars "fc" = l.length) (hB : (pre ++ [0] ++ frames l).length ≤ W) :
    ∃ τ', Run (W + 1) patch τ τ' 3 ∧ Filled "OB" "po" (pre ++ toWord l) τ' ∧ OFr τ τ' [] := by
  have hlen := hF.length_le
  have hl : l.length ≤ (frames l).length := by rw [Words.length_frames]; omega
  simp only [List.length_append, List.length_singleton] at hB hlen
  refine ⟨τ.setArr "OB" pre.length l.length, ?_, ?_,
    ⟨fun _ _ => by simp, fun b hb => by simp [hb], by simp, by simp, by simp⟩⟩
  · exact (Run.store (ev_var hfp (by omega)) (ev_var hfc (by omega)) (by omega)).mono
      (by simp [Expr.size])
  · rw [toWord_words]
    refine ⟨by simp [hF.pos], fun i hi => ?_⟩
    rw [← List.getElem?_eq_getElem hi]
    simp only [arrs_setArr, ↓reduceIte, List.getElem?_set]
    by_cases hip : pre.length = i
    · subst hip
      rw [if_pos rfl, if_pos (by omega)]
      simp
    · rw [if_neg hip, getElem?_mid pre _ _ 0 i (Ne.symm hip)]
      have hi' : i < (pre ++ [0] ++ frames l).length := by simp at hi ⊢; omega
      rw [hF.get i hi', ← List.getElem?_eq_getElem hi']
      simp

end Lax185574Proofs.ResolveRam.Glue
