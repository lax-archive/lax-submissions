import Lax185574Proofs.ResolveRam.Glue.RdSt

/-!
The answer of the switch and copying words of the state.

The answer `rY c` of the switch is the real answer of the slot of the
call between the fixed answers of the other four slots (`rY_split`), so
it is the segment of `rY c` from `preLen c` of length `|rY c| - dLen c`
(`realY_seg`). `cpWord` appends the frame `|w| :: w` of word `ow` of the
words in the arrays of the word library to the buffer (`cpWord_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574Proofs.ResolveRam

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

/-- The real answer of a call. -/
noncomputable def realY : RCall → List ℕ
  | .stp => toWord (Lax185574.ScatterTypes.stp G k₀ q₀)
  | .shift τ => toWord (shOf G τ)
  | .ftree τ => toWord ((faOf G τ).map toWord)
  | .compose σ ν => toWord (coOf G σ ν)
  | .canon ws => canonW ws

/-- The length of the fixed answers in front of the real one. -/
noncomputable def preLen : RCall → ℕ
  | .stp => yA0.length + yB0.length + yC0.length + yE0.length
  | .shift _ => 0
  | .ftree _ => yA0.length
  | .compose _ _ => yA0.length + yB0.length
  | .canon _ => yA0.length + yB0.length + yC0.length

/-- The length of all fixed answers of a call. -/
noncomputable def dLen (c : RCall) : ℕ :=
  yA0.length + yB0.length + yC0.length + yE0.length + yF0.length -
    match c with
    | .stp => yF0.length
    | .shift _ => yA0.length
    | .ftree _ => yB0.length
    | .compose _ _ => yC0.length
    | .canon _ => yE0.length

/-- **The answer of the switch.** -/
theorem rY_split (c : RCall) :
    ∃ pre post, rY G k₀ q₀ c = pre ++ realY G k₀ q₀ c ++ post ∧ pre.length = preLen c ∧
      pre.length + post.length = dLen c := by
  cases c with
  | stp => exact ⟨yA0 ++ yB0 ++ yC0 ++ yE0, [], by simp [rY, realY, yA, yB, yC, yE, yF],
      by simp [preLen] <;> omega, by simp [dLen]; omega⟩
  | shift τ => exact ⟨[], yB0 ++ yC0 ++ yE0 ++ yF0, by simp [rY, realY, yA, yB, yC, yE, yF],
      by simp [preLen] <;> omega, by simp [dLen]; omega⟩
  | ftree τ => exact ⟨yA0, yC0 ++ yE0 ++ yF0, by simp [rY, realY, yA, yB, yC, yE, yF],
      by simp [preLen] <;> omega, by simp [dLen]; omega⟩
  | compose σ ν => exact ⟨yA0 ++ yB0, yE0 ++ yF0, by simp [rY, realY, yA, yB, yC, yE, yF],
      by simp [preLen] <;> omega, by simp [dLen]; omega⟩
  | canon ws => exact ⟨yA0 ++ yB0 ++ yC0, yF0, by simp [rY, realY, yA, yB, yC, yE, yF],
      by simp [preLen] <;> omega, by simp [dLen]; omega⟩

/-- The real answer as a segment of the answer of the switch. -/
theorem realY_seg (c : RCall) :
    ((rY G k₀ q₀ c).drop (preLen c)).take ((rY G k₀ q₀ c).length - dLen c) = realY G k₀ q₀ c := by
  obtain ⟨pre, post, h, h1, h2⟩ := rY_split G k₀ q₀ c
  rw [h, ← h1, List.append_assoc, List.drop_left]
  simp only [List.length_append]
  rw [show pre.length + ((realY G k₀ q₀ c).length + post.length) - dLen c = (realY G k₀ q₀ c).length by
    omega, List.take_left]

/-! ### Copying a word of the state -/

/-- Append the frame of word `ow` to the buffer. -/
def cpWord : Com :=
  .seq (.assign "wa" (.get "st" (.var "ow"))) (.seq (.assign "wl" (.get "ln" (.var "ow")))
    (.seq (push1 "OB" "po" (.var "wl")) (cpSeg "a" "wa" "wl")))

/-- **Copying a word.** -/
theorem cpWord_run {W : ℕ} {ws : List (List ℕ)} {σ : Env} {pre : List ℕ} {i : ℕ}
    (hw : WordsAt ws σ) (hi : σ.vars "ow" = i) (hil : i < ws.length)
    (hF : Filled "OB" "po" pre σ) (hcap : pre.length + ws[i].length + 1 ≤ (σ.arrs "OB").length)
    (hB : pre.length + ws[i].length + 1 ≤ W) (hT : total ws + ws.length ≤ W)
    (hv : ∀ v ∈ ws[i], v ≤ W) (ha : total ws ≤ (σ.arrs "a").length) :
    ∃ σ', Run (W + 1) cpWord σ σ' (ws[i].length * 20 + 20) ∧
      Filled "OB" "po" (pre ++ (ws[i].length :: ws[i])) σ' ∧ OFr σ σ' ["wa", "wl", "po", "ci"] := by
  have hoi := off_add_le hil
  have hst := hw.st i hil
  have hln := hw.ln i hil
  have hoff : off ws i + ws[i].length ≤ total ws := hoi
  set σ1 := σ.setVar "wa" (off ws i)
  have r1 : Run (W + 1) (.assign "wa" (.get "st" (.var "ow"))) σ σ1 3 :=
    (Run.assign (evalB_get (ev_var hi (by omega)) hst (by omega))).mono (by simp [Expr.size])
  set σ2 := σ1.setVar "wl" ws[i].length
  have r2 : Run (W + 1) (.assign "wl" (.get "ln" (.var "ow"))) σ1 σ2 3 :=
    (Run.assign (evalB_get (ev_var (x := "ow") (v := i) (by simp [σ1, hi]) (by omega)) (by simpa [σ1] using hln)
      (by omega))).mono (by simp [Expr.size])
  have hF2 : Filled "OB" "po" pre σ2 := (hF.setVar (by decide) _).setVar (by decide) _
  obtain ⟨σ3, r3, F3, o3⟩ := push1_ofr (W := W) (e := .var "wl") (v := ws[i].length) hF2
    (ev_var (by simp [σ2]) (by omega)) (by simp [σ2, σ1]; omega) (by omega)
  have ha3 : σ3.arrs "a" = σ.arrs "a" := by rw [o3.arrs _ (by decide)]; simp [σ2, σ1]
  have hseg : seg (σ3.arrs "a") (off ws i) ws[i].length = ws[i] := by
    rw [ha3]
    apply List.ext_getElem?
    intro j
    simp only [seg, List.getElem?_take, List.getElem?_drop]
    split_ifs with hj
    · rw [hw.a i hil j hj, List.getElem?_eq_getElem hj]
    · rw [List.getElem?_eq_none (by omega)]
  have halen : off ws i + ws[i].length ≤ (σ3.arrs "a").length := by rw [ha3]; omega
  obtain ⟨σ4, r4, F4, o4⟩ := cpSeg_ofr (W := W) (src := "a") (s := "wa") (l := "wl")
    (a := off ws i) (N := ws[i].length) (by decide)
    (by rw [o3.vars _ (by decide)]; simp [σ2, σ1]) (by rw [o3.vars _ (by decide)]; simp [σ2])
    (by decide) (by decide) (by decide) (by decide) F3 halen
    (by rw [o3.len]; simp [σ2, σ1]; omega) (by omega) (by simp; omega)
    (by rw [hseg]; exact hv)
  rw [hseg] at F4
  refine ⟨σ4, ?_, by simpa using F4, ?_⟩
  · unfold cpWord
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by simp [Expr.size]; omega)
  · have := ((OFr.setVar σ "wa" (off ws i)).trans (OFr.setVar σ1 "wl" ws[i].length)).trans (o3.trans o4)
    exact this.mono (by decide)

end Lax185574Proofs.ResolveRam.Glue
