import Lax185574Proofs.MC.Brute.Step
import Lax185574Proofs.Words.ForLoop
import Lax185574Proofs.Legacy

/-!
Skipping the construction sequence, for the brute-force thread.

The word of a script is `n`, the `n` colors, the number `m` of steps
and three entries per step (`seq_word`). `skipSeq` reads past it with
two counting loops, so the evaluator does not need the sequence.
-/

namespace Lax185574Proofs.MC.Brute

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding

theorem flatten_singletons : ∀ l : List ℕ, (l.map (fun c => [c])).flatten = l
  | [] => rfl
  | a :: l => by simp [flatten_singletons l]

theorem seq_word {n : ℕ} (σ : Script n) :
    toWord σ = n :: (List.ofFn σ.colors ++ σ.steps.length :: (σ.steps.map stepCode).flatten) := by
  show (List.ofFn σ.colors).length :: ((List.ofFn σ.colors).map (fun c => [c])).flatten ++
    (σ.steps.length :: (σ.steps.map stepCode).flatten) = _
  rw [flatten_singletons, List.length_ofFn]
  rfl

theorem length_steps (l : List Step) : ((l.map stepCode).flatten).length = 3 * l.length := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons]
    cases s <;> simp [stepCode] <;> ring

/-- `k` reads into `bfy`. -/
def rdK : ℕ → Com
  | 0 => .skip
  | k + 1 => .seq (.read "bfy") (rdK k)

theorem rdK_run {B : ℕ} : ∀ (k : ℕ) (l rest : List ℕ) (σ : Env), l.length = k → σ.inp = l ++ rest →
    ∃ σ', Run B (rdK k) σ σ' (k + 1) ∧ σ'.inp = rest
  | 0, l, rest, σ, hl, hi => by
      rw [List.length_eq_zero_iff] at hl; subst hl
      exact ⟨σ, Run.skip, by simpa using hi⟩
  | k + 1, a :: l, rest, σ, hl, hi => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      obtain ⟨σ', r, h⟩ := rdK_run k l rest _ hl (show ({ σ.setVar "bfy" a with inp := l ++ rest } :
        Env).inp = l ++ rest from rfl)
      refine ⟨σ', ?_, h⟩
      show Run B (.seq (.read "bfy") (rdK k)) σ σ' (k + 1 + 1)
      exact (Run.seq (Run.read (by simpa using hi)) r).mono (by omega)

theorem rdK_wvars : ∀ k, (rdK k).wvars ⊆ ["bfy"]
  | 0 => by simp [rdK, Com.wvars]
  | k + 1 => by
      have := rdK_wvars k
      intro y hy
      simp only [rdK, Com.wvars, List.mem_append] at hy
      rcases hy with h | h
      · exact h
      · exact this h

/-- Skip `N` blocks of `c` entries, `N` in `bfx`. -/
def skipLoop (c : ℕ) : Com := forUp "bfi" (.var "bfx") (rdK c)

theorem skipLoop_run {B c N : ℕ} {l rest : List ℕ} (hl : l.length = c * N) (hN : N < B) {σ : Env}
    (hx : σ.vars "bfx" = N) (hinp : σ.inp = l ++ rest) :
    ∃ σ', Run B (skipLoop c) σ σ' (N * (c + 9) + 6) ∧ σ'.inp = rest := by
  obtain ⟨σ', hr, ⟨-, hI⟩, -⟩ := forUp_run (B := B) (i := "bfi") (e := .var "bfx") (body := rdK c)
    (N := N) (K := c + 1)
    (fun k τ => τ.vars "bfx" = N ∧ τ.inp = l.drop (c * k) ++ rest) (σ := σ) hN
    (fun k _ τ hI _ => by rw [← hI.1]; exact evalB_var (by omega))
    ⟨by simp [hx], by simp [hinp]⟩
    (by
      rintro k hk τ ⟨hx1, hi1⟩ hik
      have hsplit : l.drop (c * k) = (l.drop (c * k)).take c ++ l.drop (c * (k + 1)) := by
        conv_lhs => rw [← List.take_append_drop c (l.drop (c * k))]
        rw [List.drop_drop]; congr 2; try ring
      obtain ⟨τ', r, h⟩ := rdK_run (B := B) c ((l.drop (c * k)).take c) (l.drop (c * (k + 1)) ++ rest)
        τ (by have : c * k + c ≤ l.length := by rw [hl]; nlinarith
              simp only [List.length_take, List.length_drop]; omega)
        (by rw [hi1]; conv_lhs => rw [hsplit]
            rw [List.append_assoc])
      have hw : ∀ y, y ≠ "bfy" → τ'.vars y = τ.vars y := fun y hy =>
        r.frame_var y (fun h => hy (by simpa using rdK_wvars c h))
      have e1 : τ'.vars "bfi" = τ.vars "bfi" := hw "bfi" (by decide)
      have e2 : τ'.vars "bfx" = τ.vars "bfx" := hw "bfx" (by decide)
      refine ⟨τ', r, by rw [e1, hik], ?_, ?_⟩
      · simp [e2, hx1]
      · simp [h])
  refine ⟨σ', hr.mono (by first | simp | (simp; nlinarith)), ?_⟩
  rw [hI, show c * N = l.length by omega, List.drop_length, List.nil_append]

/-- Skip the word of a script. -/
def skipSeq : Com :=
  .seq (.read "bfx") (.seq (skipLoop 1) (.seq (.read "bfx") (skipLoop 3)))

/-- **Skipping the sequence.** -/
theorem skipSeq_run {B n : ℕ} (σs : Script n) {rest : List ℕ} (hB : ∀ v ∈ toWord σs, v < B)
    {σ : Env} (hinp : σ.inp = toWord σs ++ rest) :
    ∃ σ', Run B skipSeq σ σ' (40 * (toWord σs).length + 20) ∧ σ'.inp = rest := by
  have hw := seq_word σs
  rw [hw] at hinp hB
  have hnB : n < B := hB n (by simp)
  have hmB : σs.steps.length < B := hB _ (by simp)
  set σ1 := { σ.setVar "bfx" n with inp := List.ofFn σs.colors ++
    (σs.steps.length :: (σs.steps.map stepCode).flatten ++ rest) }
  obtain ⟨σ2, r2, h2⟩ := skipLoop_run (B := B) (c := 1) (N := n) (l := List.ofFn σs.colors)
    (rest := σs.steps.length :: (σs.steps.map stepCode).flatten ++ rest) (σ := σ1) (by simp) hnB
    (by simp [σ1]) (by simp [σ1])
  set σ3 := { σ2.setVar "bfx" σs.steps.length with inp := (σs.steps.map stepCode).flatten ++ rest }
  obtain ⟨σ4, r4, h4⟩ := skipLoop_run (B := B) (c := 3) (N := σs.steps.length)
    (l := (σs.steps.map stepCode).flatten) (rest := rest) (σ := σ3)
    (length_steps _) hmB (by simp [σ3]) (by simp [σ3])
  refine ⟨σ4, ?_, h4⟩
  unfold skipSeq
  refine (Run.seq (Run.read (by rw [hinp]; simp)) (Run.seq r2 (Run.seq (Run.read (by rw [h2]; simp))
    r4))).mono ?_
  rw [hw]
  simp only [List.length_cons, List.length_append, List.length_ofFn, length_steps]
  omega

end Lax185574Proofs.MC.Brute
