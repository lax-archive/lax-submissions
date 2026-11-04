import Lax185574Proofs.JobMap.Glue
import Lax185574Proofs.JobMap.Bounds
import Lax185574Proofs.Words.GuardedSound
import Lax185574Proofs.LoopScript

/-!
The glue program of the composite at a word length of the loop driver.

`glue_sound_at`: if the input of round `j` has entries below
`2^(v - sI)`, every halting run of the guarded glue program at word
length `v` outputs `gOut js f j`, and the checks of the round hold at
the threshold of `v`. `glue_time_at`: if the checks hold, the program
halts with that output within a time linear in the lengths of the input
word and of the frames of the answers.

`inv_script_sound` (copied from `MC/Asm/InvScript`) is soundness of a
script of the loop driver along an invariant of the rounds.
-/

namespace Lax185574Proofs.JobMap

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.RamSim Lax185574Proofs.Simulate

/-- The glue program on the word RAM. -/
def gProg : Program := guardedProgram glueLay glueCmd

/-- The input shift: the input entries of a round are below `2^(v - sI)`. -/
def sI : ℕ := guardBits glueLay + 2

theorem sI_eq : sI = guardBits glueLay + 2 := rfl

/-! ### Entries of the input of a round -/

theorem mem_gIn {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j ≤ js.length) {y : ℕ}
    (hy : y ∈ gIn js f j) :
    y ≤ (toWord js).length + (fr js f j).length + 2 ∨ y ∈ toWord js ∨ y ∈ fr js f j := by
  have hJx := jobs_length_lt js
  cases j with
  | zero =>
    simp only [gIn, if_true] at hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_append.mp h with h | h
      · simp at h; left; omega
      · right; left; exact h
    · simp at h; left; omega
  | succ j =>
    have hjl : j < js.length := by omega
    rw [gIn_succ hjl] at hy
    have hfr := fr_succ (f := f) hjl
    have hl : (fr js f (j + 1)).length = (fr js f j).length + 1 + (f js[j]).length := by
      rw [hfr]; simp; omega
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hy
    rcases hy with ((((h | h) | h) | h | h) | h) | h | h
    · left; omega
    · left; omega
    · right; left; exact h
    · left; omega
    · left; omega
    · right; right; rw [hfr]; exact List.mem_append_left _ h
    · right; right; rw [hfr, h]; simp
    · right; right; rw [hfr]; simp [h]

theorem gIn_entries {js : List (List ℕ)} {f : List ℕ → List ℕ} {j : ℕ} (hj : j ≤ js.length) {Q : ℕ}
    (h : ∀ y ∈ gIn js f j, y < Q) :
    (toWord js).length + (fr js f j).length + 2 ≤ 3 * Q ∧ (∀ y ∈ toWord js, y < Q) ∧
      ∀ y ∈ fr js f j, y < Q := by
  cases j with
  | zero =>
    have h1 := h (toWord js).length (by simp [gIn])
    refine ⟨by simp [fr_zero]; omega, fun y hy => h y (by simp [gIn, hy]), by simp [fr_zero]⟩
  | succ j =>
    have hjl : j < js.length := by omega
    have hfr := fr_succ (f := f) hjl
    rw [gIn_succ hjl] at h
    have h1 := h ((toWord js).length + 1) (by simp)
    have h2 := h ((fr js f j).length + 2) (by simp)
    have h3 := h (f js[j]).length (by simp)
    refine ⟨by rw [hfr]; simp; omega, fun y hy => h y (by simp [hy]), fun y hy => h y ?_⟩
    rw [hfr] at hy
    simp only [List.mem_append, List.mem_cons] at hy ⊢
    rcases hy with hy | hy | hy
    · exact Or.inl (Or.inr hy)
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)

/-! ### The glue program at a word length -/

theorem glue_sound_at (js : List (List ℕ)) (f : List ℕ → List ℕ) {j : ℕ} (hj : j ≤ js.length)
    {v : ℕ} (hv : sI + 5 ≤ v) (hin : ∀ y ∈ gIn js f j, y < 2 ^ (v - sI)) :
    ∀ o t, RunsTo v gProg (gIn js f j) o t → o = gOut js f j ∧
      Checks js f j (guardW glueLay v / 64) := by
  have hv' : guardBits glueLay + 7 ≤ v := by rw [sI_eq] at hv; omega
  set W := guardW glueLay v with hWd
  have hW1 : W + 1 = 2 ^ (v - guardBits glueLay) := guardW_succ glueLay v
  have hQ : 2 ^ (v - guardBits glueLay) = 4 * 2 ^ (v - sI) := by
    rw [sI_eq, show v - guardBits glueLay = (v - (guardBits glueLay + 2)) + 2 by omega, pow_add]
    ring
  have hQ5 : 2 ^ 5 ≤ 2 ^ (v - sI) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hB, hXv, hFv⟩ := gIn_entries hj hin
  generalize 2 ^ (v - sI) = Q at hQ hQ5 hB hXv hFv hin
  norm_num at hQ5
  obtain ⟨σ', k, hr, hout, -, hov⟩ := glue_run js f hj (W := W) (by omega) (by omega)
    (fun y hy => by have := hXv y hy; omega) (fun y hy => by have := hFv y hy; omega)
  have hs := guarded_sound glueCmd_ok (by decide) (by decide) (w := v) (by omega)
    (fun y hy => by have := hin y hy; omega) hr
  intro o t h
  obtain ⟨h0, ho⟩ := hs.1 o t h
  exact ⟨ho.trans hout, hov.1 h0⟩

theorem glue_time_at (js : List (List ℕ)) (f : List ℕ → List ℕ) {j : ℕ} (hj : j ≤ js.length)
    {v : ℕ} (hv : guardBits glueLay + 2 ≤ v) (hW : 64 ≤ guardW glueLay v)
    (hC : Checks js f j (guardW glueLay v / 64)) :
    (∃ t ≤ 1000 * ((toWord js).length + (fr js f j).length) + 4005,
      RunsTo v gProg (gIn js f j) (gOut js f j) t) ∧
    ∀ o t, RunsTo v gProg (gIn js f j) o t → o = gOut js f j := by
  set W := guardW glueLay v with hWd
  obtain ⟨h1, h2, h3, h4⟩ := hC
  have hT : W / 64 ≤ W := Nat.div_le_self _ _
  obtain ⟨σ', k, hr, hout, hk, hov⟩ := glue_run js f hj (W := W) hW (by omega)
    (fun y hy => by have := h3 y hy; omega) (fun y hy => by have := h4 y hy; omega)
  have hs := guarded_sound glueCmd_ok (by decide) (by decide) (w := v) hv
    (fun y hy => by
      rcases mem_gIn hj hy with h | h | h
      · omega
      · have := h3 y h; omega
      · have := h4 y h; omega) hr
  obtain ⟨t, ht, hrun⟩ := hs.2 (hov.2 ⟨h1, h2, h3, h4⟩)
  refine ⟨⟨t, ?_, by rw [← hout]; exact hrun⟩, fun o t h => (hs.1 o t h).2.trans hout⟩
  simp only [Layout.const] at ht
  omega

/-! ### Scripts with an invariant (as in `MC/Asm/InvScript`) -/

/-- What soundness needs of round `j < R` under the invariant `I`. -/
def InvCall (w : ℕ) (G P : Program) (x : List ℕ) (A B : ℕ → List ℕ) (I : ℕ → Prop) (j : ℕ) :
    Prop :=
  I j → ∀ o t, RunsTo (lpV w (2 * j)) G (lpU x (A j) (B j)) o t →
    o = A (j + 1) ∧ (A (j + 1)).head? ≠ some 0 ∧
      ∀ r t', RunsTo (lpV w (2 * j + 1)) P (lpQ o) r t' → r = B (j + 1) ∧ I (j + 1)

theorem inv_script_back {w : ℕ} {G P : Program} {x : List ℕ} {A B : ℕ → List ℕ}
    {I : ℕ → Prop} {R : ℕ} {z : List ℕ} (hC : ∀ j < R, InvCall w G P x A B I j)
    (hD : I R → ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z) {i : ℕ}
    {a b z' : List ℕ} {T : ℕ} (h : LoopTrace w G P x i a b z' T) :
    ∀ j ≤ R, i = 2 * j → a = A j → b = B j → I j → z' = z := by
  induction h with
  | done hs hG ho =>
    intro j hj hi ha hb hI
    subst hi ha hb
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e1, h0, -⟩ := hC j hlt hI _ _ hG
      rw [← e1] at h0; simp at h0
    · exact (List.cons.inj (hD hI _ _ hG)).2
  | call hs hG hne h0 ho hs' hP hr _ ih =>
    intro j hj hi ha hb hI
    subst hi ha hb
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · obtain ⟨e1, -, hPu⟩ := hC j hlt hI _ _ hG
      obtain ⟨e2, hI'⟩ := hPu _ _ hP
      subst e1 e2
      exact ih (j + 1) (by omega) (by ring) rfl rfl hI'
    · have := hD hI _ _ hG
      rw [this] at h0; simp at h0

/-- **Soundness of a script with an invariant.** -/
theorem inv_script_sound {G P p : Program}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)
    {w : ℕ} {x : List ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1)) {A B : ℕ → List ℕ}
    {I : ℕ → Prop} {R : ℕ} {z : List ℕ} (hA0 : A 0 = lpA0 x) (hB0 : B 0 = []) (hI0 : I 0)
    (hC : ∀ j < R, InvCall w G P x A B I j)
    (hD : I R → ∀ o t, RunsTo (lpV w (2 * R)) G (lpU x (A R) (B R)) o t → o = 0 :: z) :
    ∀ z' t, RunsTo w p x z' t → z' = z := by
  intro z' t h
  obtain ⟨T, hT⟩ := hp w x hw hx z' t h
  exact inv_script_back hC hD hT 0 (Nat.zero_le _) rfl hA0.symm hB0.symm hI0

end Lax185574Proofs.JobMap
