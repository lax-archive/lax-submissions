import Lax185574Proofs.ResolveRam.Glue.Head
import Lax185574Proofs.MC.Glue.Out

/-!
Reading the state and the answer in a later round of the glue program
of lem:resolve-lift.

The state is the list of scalars `scW c` followed by the word of the
list of words `(swAt c).ws`. `readVars xs` reads one scalar into each of
the names `xs` (`readVars_run`), `rdState` reads the seventeen scalars
into `scR` and the words into the arrays `a`, `st`, `ln` of the word
library (`rdState_run`, with `WordsAt`). `rdAns` reads the length `bl`
of the answer of the switch and the answer into the array `y`
(`rdAns_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- Read one scalar into each name. -/
def readVars : List String → Com
  | [] => .skip
  | x :: xs => .seq (.read x) (readVars xs)

theorem readVars_run {B : ℕ} : ∀ (xs : List String) (vs rest : List ℕ) (σ : Env),
    xs.Nodup → vs.length = xs.length → σ.inp = vs ++ rest →
    ∃ σ', Run B (readVars xs) σ σ' (xs.length + 1) ∧ σ'.inp = rest ∧
      (∀ i (h : i < xs.length), σ'.vars xs[i] = vs.getD i 0) ∧
      (∀ y, y ∉ xs → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out
  | [], vs, rest, σ, _, hl, hinp => by
    have : vs = [] := List.length_eq_zero_iff.1 (by simpa using hl)
    subst this
    exact ⟨σ, Run.skip, by simpa using hinp, fun i h => absurd h (by simp), fun _ _ => rfl, rfl, rfl⟩
  | x :: xs, vs, rest, σ, hnd, hl, hinp => by
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons v vs' => exact ⟨v, vs', rfl⟩
    set σ1 : Env := { σ.setVar x v with inp := vs' ++ rest }
    have r1 : Run B (.read x) σ σ1 1 := Run.read (by rw [hinp]; rfl)
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨σ', r, hi, hv, hf, ha, ho⟩ := readVars_run xs vs' rest σ1 hnd'.2 (by simpa using hl) rfl
    refine ⟨σ', (Run.seq r1 r).mono (by simp; omega), hi, fun i h => ?_, fun y hy => ?_, by rw [ha]; rfl,
      by rw [ho]; rfl⟩
    · cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.getD_cons_zero]
        rw [hf x hnd'.1]; simp [σ1]
      | succ i =>
        simp only [List.getElem_cons_succ, List.getD_cons_succ]
        exact hv i (by simpa using h)
    · simp only [List.mem_cons, not_or] at hy
      rw [hf y hy.2]; simp [σ1, hy.1]

/-- The names of the scalars of the state. -/
def scR : List String :=
  ["z0", "gX", "nx", "gn", "gP", "gQ", "gS", "gK", "gq", "ph", "dd", "ii", "mm", "nSG", "nFA", "nCO",
    "nLV"]

theorem scR_nodup : scR.Nodup := by decide

/-- Read the state. -/
def rdState : Com := .seq (readVars scR) readWords

/-- **Reading the state.** -/
theorem rdState_run {B : ℕ} {sc : List ℕ} {ws : List (List ℕ)} {rest : List ℕ} {σ : Env}
    (hsc : sc.length = 17) (hinp : σ.inp = sc ++ toWord ws ++ rest)
    (hoa : total ws ≤ (σ.arrs "a").length) (host : ws.length ≤ (σ.arrs "st").length)
    (holn : ws.length ≤ (σ.arrs "ln").length) (hB : (toWord ws).length < B)
    (hv : ∀ v ∈ toWord ws, v < B) :
    ∃ σ', Run B rdState σ σ' (21 * (toWord ws).length + 27) ∧ σ'.inp = rest ∧
      (∀ i (h : i < 17), σ'.vars (scR[i]'(by simp [scR]; omega)) = sc.getD i 0) ∧
      σ'.vars "m" = ws.length ∧ WordsAt ws σ' ∧ σ'.out = σ.out ∧
      (∀ y, y ∉ scR → y ∉ readWords.wvars → σ'.vars y = σ.vars y) ∧
      (∀ a, a ∉ ["a", "st", "ln"] → σ'.arrs a = σ.arrs a) := by
  obtain ⟨σ1, r1, i1, v1, f1, a1, o1⟩ := readVars_run (B := B) scR sc (toWord ws ++ rest) σ scR_nodup
    (by simp [scR, hsc]) (by rw [hinp, List.append_assoc])
  obtain ⟨σ2, r2, m2, i2, w2⟩ := readWords_wordsAt (B := B) (ws := ws) (rest := rest) (σ := σ1) i1
    (by rw [a1]; exact hoa) (by rw [a1]; exact host) (by rw [a1]; exact holn) hB hv
  refine ⟨σ2, (Run.seq r1 r2).mono (by simp [scR]; omega), i2, fun i h => ?_, m2, w2, ?_,
    fun y h1 h2 => by rw [r2.frame_var y h2, f1 y h1], fun a ha => ?_⟩
  · rw [r2.frame_var _ (by
      have : scR[i]'(by simp [scR]; omega) ∈ scR := List.getElem_mem _
      revert this
      generalize scR[i]'(by simp [scR]; omega) = z
      intro hz
      simp only [scR, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> decide)]
    exact v1 i (by simp [scR]; omega)
  · rw [r2.out_eq (by decide), o1]
  · rw [r2.frame_arr a (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
      simp [readWords, readWord, readEntries, readEntry, Com.warrs]; tauto), a1]

/-- Read the answer of the switch into `y`. -/
def rdAns : Com :=
  .seq (.read "bl") (forUp "ci" (.var "bl") (.seq (.read "v") (.store "y" (.var "ci") (.var "v"))))

/-- **Reading the answer.** -/
theorem rdAns_run {B : ℕ} {b : List ℕ} {σ : Env} (hinp : σ.inp = b.length :: b)
    (hlen : b.length ≤ (σ.arrs "y").length) (hB : b.length + 1 < B) (hv : ∀ v ∈ b, v < B) :
    ∃ σ', Run B rdAns σ σ' (b.length * 12 + 8) ∧ σ'.vars "bl" = b.length ∧
      (∀ i (h : i < b.length), (σ'.arrs "y")[i]? = some b[i]) ∧ σ'.inp = [] ∧ σ'.out = σ.out ∧
      (∀ y, y ∉ ["bl", "ci", "v"] → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "y" → σ'.arrs a = σ.arrs a) := by
  set L := (σ.arrs "y").length
  set σ1 : Env := { σ.setVar "bl" b.length with inp := b }
  have r1 : Run B (.read "bl") σ σ1 1 := Run.read hinp
  let I : ℕ → Env → Prop := fun k τ => τ.inp = b.drop k ∧ τ.vars "bl" = b.length ∧
    (∀ i (h : i < k) (h' : i < b.length), (τ.arrs "y")[i]? = some b[i]) ∧ (τ.arrs "y").length = L
  obtain ⟨σ', hr, ⟨hin, hbl, hy, hL⟩, -⟩ := forUp_run (B := B) (i := "ci") (e := .var "bl")
    (body := .seq (.read "v") (.store "y" (.var "ci") (.var "v"))) (N := b.length) (K := 4) I
    (σ := σ1) (by omega) (fun k _ τ hI _ => ev_var hI.2.1 (by omega))
    ⟨by simp [σ1], by simp [σ1], fun i h => absurd h (by omega), by simp [σ1, L]⟩
    (by
      rintro k hk τ ⟨hin, hbl, hy, hL⟩ hci
      set τ1 : Env := { τ.setVar "v" b[k] with inp := b.drop (k + 1) }
      have r1 : Run B (.read "v") τ τ1 1 := Run.read (by rw [hin, List.drop_eq_getElem_cons hk])
      have r2 : Run B (.store "y" (.var "ci") (.var "v")) τ1 (τ1.setArr "y" k b[k]) 3 :=
        Run.store (ev_var (by simp [τ1, hci]) (by omega)) (ev_var (by simp [τ1]) (hv _ (List.getElem_mem hk)))
          (by simp [τ1, hL]; omega)
      refine ⟨_, (Run.seq r1 r2).mono (by omega), by simp [τ1, hci], by simp [τ1], by simp [τ1, hbl],
        fun i h h' => ?_, by simp [τ1, hL]⟩
      simp only [τ1, arrs_setArr, ↓reduceIte, arrs_setVar, List.getElem?_set]
      rcases Nat.lt_or_ge i k with hik | hik
      · rw [if_neg (by omega)]; exact hy i hik h'
      · obtain rfl : i = k := by omega
        rw [if_pos rfl, if_pos (by rw [hL]; omega)])
  have hrun : Run B rdAns σ σ' (b.length * 12 + 8) := by
    unfold rdAns
    exact (Run.seq r1 hr).mono (by simp only [Expr.size]; omega)
  refine ⟨σ', hrun, hbl, fun i h => hy i h h, by simpa using hin, hrun.out_eq (by decide),
    fun y hy' => hrun.frame_var y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
      simp [rdAns, forUp, Com.wvars]; tauto),
    fun a ha => hrun.frame_arr a (by simp [rdAns, forUp, Com.warrs]; exact ha)⟩

end Lax185574Proofs.ResolveRam.Glue
