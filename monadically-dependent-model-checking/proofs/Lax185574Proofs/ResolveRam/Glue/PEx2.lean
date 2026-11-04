import Lax185574Proofs.ResolveRam.Glue.PEx1

/-!
A loop over the frames of a list of words held in the array `a`.

`frLoop body` runs `body` once for every word `E[z]` of the list at `te`
(with `tne = |E|`), with the position of its frame in `tf` and the
counter in `tz` (`frLoop_run`). The body is given by its effect on an
invariant indexed by the number of finished words. `skipL` moves `tx`
over a list of words at `tx` (`skipL_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding

/-- Move to the next frame. -/
def frNext : Com := .assign "tf" (.add (.add (.var "tf") (.get "a" (.var "tf"))) (.lit 1))

/-- The loop over the frames of the list at `te`. -/
def frLoop (body : Com) : Com :=
  .seq (.assign "tf" (.add (.var "te") (.lit 1))) (forUp "tz" (.var "tne") (.seq body frNext))

/-- **The loop over the frames.** The invariant survives changes of `tf`
and `tz`, and the body keeps `a`, `tf`, `tz` and `tne`. -/
theorem frLoop_run {W : ℕ} {body : Com} {e : ℕ} {E : List (List ℕ)} {r : List ℕ} {X : List ℕ}
    (Kf : ℕ → ℕ) (I : ℕ → Env → Prop) {τ : Env}
    (ha : τ.arrs "a" = X) (hd : X.drop e = toWord E ++ r) (hte : τ.vars "te" = e)
    (hne : τ.vars "tne" = E.length) (hB : e + (toWord E).length + 2 < W + 1)
    (hv : ∀ v ∈ toWord E, v < W + 1)
    (hIf : ∀ z ρ x, I z ρ → I z (ρ.setVar "tf" x)) (hIz : ∀ z ρ x, I z ρ → I z (ρ.setVar "tz" x))
    (h0 : I 0 τ)
    (hstep : ∀ z (hz : z < E.length), ∀ ρ, I z ρ → ρ.vars "tz" = z →
      ρ.vars "tf" = e + 1 + (frames (E.take z)).length → ρ.arrs "a" = X → ρ.vars "tne" = E.length →
      ∃ ρ', Run (W + 1) body ρ ρ' (Kf z) ∧ I (z + 1) ρ' ∧ ρ'.vars "tz" = z ∧ ρ'.vars "tf" = ρ.vars "tf" ∧
        ρ'.arrs "a" = X ∧ ρ'.vars "tne" = E.length) :
    ∃ τ', Run (W + 1) (frLoop body) τ τ' ((∑ z ∈ Finset.range E.length, (Kf z + 16)) + 10) ∧
      I E.length τ' ∧ τ'.vars "tf" = e + (toWord E).length := by
  obtain ⟨h0', hpos, hfr, -, -⟩ := listAt hd
  set τ1 := τ.setVar "tf" (e + 1)
  have r1 : Run (W + 1) (.assign "tf" (.add (.var "te") (.lit 1))) τ τ1 4 :=
    (Run.assign (ev_add (ev_var hte (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have hlen : E.length < (toWord E).length := by
    rw [toWord_words, List.length_cons, Words.length_frames]; omega
  have hfl : ∀ z, (frames (E.take z)).length + 1 ≤ (toWord E).length := fun z => by
    have := frames_take_le E z
    rw [toWord_words, List.length_cons]; omega
  let J : ℕ → Env → Prop := fun z ρ => I z ρ ∧ ρ.vars "tf" = e + 1 + (frames (E.take z)).length ∧
    ρ.arrs "a" = X ∧ ρ.vars "tne" = E.length
  obtain ⟨τ2, r2, ⟨I2, f2, -⟩, -⟩ := forUp_run_sum (B := W + 1) (i := "tz") (e := .var "tne")
    (body := .seq body frNext) (N := E.length) (fun z => Kf z + 8) J (σ := τ1) (by omega)
    (fun z _ ρ hJ _ => ev_var hJ.2.2.2 (by omega))
    ⟨hIz _ _ _ (hIf _ _ _ h0), by simp [τ1, frames], by simp [τ1, ha], by simp [τ1, hne]⟩
    (by
      rintro z hz ρ ⟨Iρ, fρ, aρ, nρ⟩ hzρ
      obtain ⟨ρ', r', I', z', f', a', n'⟩ := hstep z hz ρ Iρ hzρ fρ aρ nρ
      obtain ⟨hp1, hp2⟩ := hpos z hz.le
      rw [frames_drop hz] at hp2
      have hxz : X[frPos X e z]? = some E[z].length := by
        have := getElem?_of_drop hp2 (i := 0) (by simp); simpa using this
      have hfs := length_frames_take_succ hz
      have hf1 := hfl (z + 1)
      have hEz : E[z].length < W + 1 := hv _ (by
        rw [toWord_words]; apply List.mem_cons_of_mem
        rw [frames_split E z, frames_drop hz]; simp)
      have hpf : frPos X e z = e + 1 + (frames (E.take z)).length := hp1
      have r2' : Run (W + 1) frNext ρ' (ρ'.setVar "tf" (e + 1 + (frames (E.take (z + 1))).length)) 7 := by
        refine (Run.assign ?_).mono (by simp [Expr.size])
        have := ev_add (ev_add (ev_var (f'.trans fρ) (by omega)) (evalB_get (ev_var (f'.trans fρ) (by omega))
          (by rw [a', ← hpf]; exact hxz) hEz) (by omega)) (evalB_lit (n := 1) (B := W + 1) (σ := ρ') (by omega))
          (by omega)
        rw [hfs, show e + 1 + ((frames (E.take z)).length + 1 + E[z].length) =
          e + 1 + (frames (E.take z)).length + E[z].length + 1 by omega]
        exact this
      refine ⟨ρ'.setVar "tf" (e + 1 + (frames (E.take (z + 1))).length), (Run.seq r' r2').mono (by omega),
        by simp [z'], hIz _ _ _ (hIf _ _ _ I'), by simp, by simp [a'], by simp [n']⟩)
  refine ⟨τ2, ?_, I2, by rw [f2, List.take_length, toWord_words, List.length_cons]; omega⟩
  unfold frLoop
  refine (Run.seq r1 r2).mono ?_
  simp only [Expr.size]
  have : ∑ z ∈ Finset.range E.length, (Kf z + 8 + 1 + 7) = ∑ z ∈ Finset.range E.length, (Kf z + 16) :=
    Finset.sum_congr rfl fun _ _ => by omega
  omega

end Lax185574Proofs.ResolveRam.Glue
