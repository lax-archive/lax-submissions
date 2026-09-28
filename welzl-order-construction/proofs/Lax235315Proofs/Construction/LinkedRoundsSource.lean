import Lax235315Proofs.Construction.LinkedSource

/-! The complete outer reverse-round reconstruction loop. Contiguous log
intervals telescope, so the source cost is linear in rounds plus log size. -/
namespace Lax235315Proofs.Construction.LinkedRoundsSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.LinkedSource
open Lax235315Proofs.Construction.LinkedReconstruction

def linkedRoundBody : Com := seqs [
  .assign "round" (.sub (.var "round") (.lit 1)),
  .assign "i" (.get "roundStart" (.var "round")),
  .assign "iend" (.get "roundEnd" (.var "round")), linkedInsertLoop]

def linkedRounds : Com := .while (.lt (.lit 0) (.var "round")) linkedRoundBody

/-- Actual pointer updates, replaying round intervals from last to first. -/
def replayRounds (boundary removed rep : ℕ → ℕ) : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, next => next
  | r + 1, next => replayRounds boundary removed rep r
      (writeLogPrefix rep removed (boundary r) (boundary (r + 1) - boundary r) next)

lemma writeLogPrefix_bounded {B n start count : ℕ} {removed rep next : ℕ → ℕ}
    (hnB : n < B) (hcap : start + count ≤ n)
    (hrem : ∀ i < n, removed i < n) (hrep : ∀ i < n, rep i < n)
    (hnext : ∀ i < n, next i < B) :
    ∀ i < n, writeLogPrefix rep removed start count next i < B := by
  induction count with
  | zero => exact hnext
  | succ count ih =>
    apply writeAfter_preserves_bound
    · exact hrep _ (by omega)
    · exact (hrem _ (by omega)).trans hnB
    · exact ih (by omega)

lemma linkedRoundBody_run {B n r : ℕ} {σ : Env} {boundary starts ends removed rep next : ℕ → ℕ}
    (hround : σ.vars "round" = r + 1) (hrn : r < n) (hnB : n < B)
    (hstarts : σ.arrs "roundStart" = arrOf n starts)
    (hends : σ.arrs "roundEnd" = arrOf n ends)
    (hremoved : σ.arrs "removed" = arrOf n removed)
    (hreps : σ.arrs "removedRep" = arrOf n rep)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hstartVal : starts r = boundary r) (hendVal : ends r = boundary (r + 1))
    (hmono : boundary r ≤ boundary (r + 1)) (hend : boundary (r + 1) ≤ n)
    (hremN : ∀ i < n, removed i < n) (hrepN : ∀ i < n, rep i < n)
    (hnextB : ∀ i < n, next i < B) :
    ∃ τ, Run B linkedRoundBody σ τ (21 * (boundary (r + 1) - boundary r) + 14) ∧
      τ.vars "round" = r ∧
      τ.arrs "nextVertex" = arrOf n
        (writeLogPrefix rep removed (boundary r) (boundary (r + 1) - boundary r) next) := by
  let σ₁ := σ.setVar "round" r
  let σ₂ := σ₁.setVar "i" (boundary r)
  let σ₃ := σ₂.setVar "iend" (boundary (r + 1))
  have r₁ : Run B (.assign "round" (.sub (.var "round") (.lit 1))) σ σ₁ 4 := by
    apply Run.assign
    have he := evalB_bin (evalB_var (by rw [hround]; omega))
      (evalB_lit (by omega : 1 < B)) (op := Bop.sub)
      (by simp [hround, Bop.apply]; omega)
    simpa [hround, Bop.apply] using he
  have r₂ : Run B (.assign "i" (.get "roundStart" (.var "round"))) σ₁ σ₂ 3 := by
    apply Run.assign
    have hv : (Expr.var "round").evalB B σ₁ = some r := by
      simpa [σ₁] using (evalB_var (B := B) (σ := σ₁)
        (x := "round") (by simp [σ₁]; omega))
    apply evalB_get hv
    · simpa [σ₁, hstarts, hstartVal] using getElem?_arrOf starts hrn
    · omega
  have r₃ : Run B (.assign "iend" (.get "roundEnd" (.var "round"))) σ₂ σ₃ 3 := by
    apply Run.assign
    have hv : (Expr.var "round").evalB B σ₂ = some r := by
      simpa [σ₂, σ₁] using (evalB_var (B := B) (σ := σ₂)
        (x := "round") (by simp [σ₂, σ₁]; omega))
    apply evalB_get hv
    · simpa [σ₂, σ₁, hends, hendVal] using getElem?_arrOf ends hrn
    · omega
  obtain ⟨τ, rloop, hi, hnext', hhead, hinp, hout⟩ := linkedInsertLoop_run
    (σ := σ₃) (hstart := by simp [σ₃, σ₂]) (hend := by simp [σ₃])
    hmono (by omega) hend hnB hremN hrepN
    (by simp [σ₃, σ₂, σ₁, hremoved]) (by simp [σ₃, σ₂, σ₁, hreps])
    (by simp [σ₃, σ₂, σ₁, hnext]) hnextB rfl rfl rfl
  refine ⟨τ, ?_, ?_, hnext'⟩
  · convert r₁.seq (r₂.seq (r₃.seq rloop)) using 1 <;>
      first | rfl | omega

  · simpa [σ₃, σ₂, σ₁] using rloop.frame_var "round" (by decide)

/-- Execute every recorded round in reverse. No list correctness is needed
for termination: valid log indices and bounded pointer cells suffice. -/
lemma linkedRounds_run {B n R : ℕ} {σ : Env} {boundary starts ends removed rep next : ℕ → ℕ}
    (hround : σ.vars "round" = R) (hRn : R ≤ n) (hnB : n < B)
    (hstarts : σ.arrs "roundStart" = arrOf n starts)
    (hends : σ.arrs "roundEnd" = arrOf n ends)
    (hremoved : σ.arrs "removed" = arrOf n removed)
    (hreps : σ.arrs "removedRep" = arrOf n rep)
    (hnext : σ.arrs "nextVertex" = arrOf n next)
    (hstartVals : ∀ r < R, starts r = boundary r)
    (hendVals : ∀ r < R, ends r = boundary (r + 1))
    (hmono : ∀ r < R, boundary r ≤ boundary (r + 1))
    (hcap : ∀ r ≤ R, boundary r ≤ n)
    (hremN : ∀ i < n, removed i < n) (hrepN : ∀ i < n, rep i < n)
    (hnextB : ∀ i < n, next i < B) :
    ∃ τ, Run B linkedRounds σ τ (24 * R + 21 * boundary R + 4) ∧
      τ.vars "round" = 0 ∧
      τ.arrs "nextVertex" = arrOf n (replayRounds boundary removed rep R next) ∧
      (∀ i < n, replayRounds boundary removed rep R next i < B) := by
  induction R generalizing σ next with
  | zero =>
    refine ⟨σ, ?_, hround, hnext, hnextB⟩
    have ht : (Cond.lt (.lit 0) (.var "round")).evalB B σ = some false := by
      have he := evalB_condLt (evalB_lit (by omega : 0 < B))
        (evalB_var (by rw [hround]; omega))
      simpa [hround] using he
    exact (Run.while_false ht).mono (by simp [Cond.size, Expr.size])
  | succ R ih =>
    have hstep := hmono R (by omega)
    obtain ⟨σ₁, rbody, hr₁, hnext₁⟩ := linkedRoundBody_run hround (by omega) hnB
      hstarts hends hremoved hreps hnext (hstartVals _ (by omega))
      (hendVals _ (by omega)) hstep (hcap _ (by omega)) hremN hrepN hnextB
    have hcapLast := hcap (R + 1) (by omega)
    have hbounded := writeLogPrefix_bounded hnB (by omega :
      boundary R + (boundary (R + 1) - boundary R) ≤ n) hremN hrepN hnextB
    obtain ⟨τ, rtail, hr₀, hfinal, hfinalB⟩ := ih hr₁ (by omega)
      ((rbody.frame_arr "roundStart" (by decide)).trans hstarts)
      ((rbody.frame_arr "roundEnd" (by decide)).trans hends)
      ((rbody.frame_arr "removed" (by decide)).trans hremoved)
      ((rbody.frame_arr "removedRep" (by decide)).trans hreps) hnext₁
      (fun r hr => hstartVals r (by omega)) (fun r hr => hendVals r (by omega))
      (fun r hr => hmono r (by omega)) (fun r hr => hcap r (by omega)) hbounded
    refine ⟨τ, ?_, hr₀, hfinal, hfinalB⟩
    have ht : (Cond.lt (.lit 0) (.var "round")).evalB B σ = some true := by
      have he := evalB_condLt (evalB_lit (by omega : 0 < B))
        (evalB_var (by rw [hround]; omega))
      simpa [hround] using he
    obtain ⟨kb, hb, rbody⟩ := rbody
    obtain ⟨kt, hkt, rtail⟩ := rtail
    exact ⟨4 + kb + kt, by omega, BigStepB.while_true ht rbody rtail⟩

end Lax235315Proofs.Construction.LinkedRoundsSource
