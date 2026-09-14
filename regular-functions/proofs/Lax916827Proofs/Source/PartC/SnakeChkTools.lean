/-
Elementary tools for the *checking automaton* of stage 1 of the induction step
of the book's snake lemma (`RequestProject/PartC/SnakeStage1.lean`).

Three unrelated things are collected here.

* `Transducers.exists_threshold`: a bit sequence which, once it is `true`, stays
  `true` is the indicator function of a final segment.  This is what turns the
  *local* monotonicity conditions that the checking automaton verifies into the
  numerical cutting points that the soundness proof needs.
* `Transducers.exists_uniform_dfa`: a finite family of regular languages is
  recognised by a *single* deterministic automaton whose accepting set depends
  on the index.  The checking automaton stores one state of that automaton per
  piece slot, which is how it verifies the window conditions of the pieces
  letter by letter.
* `Transducers.TwoWay.runOut_of_chain_halt`: the variant of
  `TwoWay.runOut_of_chain` in which the chain of pieces halts before its last
  index, the remaining pieces producing no output.
-/
import Lax916827Proofs.Source.PartC.SnakeChain
import Lax916827Proofs.Source.PartC.RegAut
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## Thresholds of monotone bit sequences -/

/-- A bit sequence which never falls back from `true` to `false` is the
indicator function of a final segment of `[0, n)`. -/
lemma exists_threshold (g : ℕ → Bool) (n : ℕ)
    (hmono : ∀ i, i + 1 < n → g i = true → g (i + 1) = true) :
    ∃ D, D ≤ n ∧ ∀ i < n, g i = decide (D ≤ i) := by
  classical
  have hmono' : ∀ j i, i ≤ j → j < n → g i = true → g j = true := by
    intro j
    induction j with
    | zero => intro i hi _ hg; rw [show (0 : ℕ) = i from by omega]; exact hg
    | succ j ih =>
        intro i hi hj hg
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · exact hmono j (by omega) (ih i (by omega) (by omega) hg)
        · have : i = j + 1 := by omega
          exact this ▸ hg
  by_cases h : ∃ i, i < n ∧ g i = true
  · refine ⟨Nat.find h, le_of_lt (Nat.find_spec h).1, ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i (Nat.find h) with hlt | hge
    · have : g i ≠ true := fun hg => Nat.find_min h hlt ⟨hi, hg⟩
      simp only [Bool.not_eq_true] at this
      rw [this, eq_comm, decide_eq_false_iff_not]
      omega
    · rw [hmono' i (Nat.find h) hge hi (Nat.find_spec h).2, eq_comm, decide_eq_true_eq]
      exact hge
  · push_neg at h
    refine ⟨n, le_refl _, ?_⟩
    intro i hi
    rw [show g i = false from by
      have := h i hi
      simpa using this, eq_comm, decide_eq_false_iff_not]
    omega

/-! ## A single automaton for a finite family of regular languages -/

/-- **A finite family of regular languages is recognised by one automaton.**
The state space is the product of the state spaces of the members of the
family, and the accepting set depends on the index. -/
lemma exists_uniform_dfa {Γ ι : Type} [Finite ι] (L : ι → Language Γ)
    (hL : ∀ i, (L i).IsRegular) :
    ∃ (S : Type) (_ : Finite S) (step : S → Γ → S) (init : S) (acc : ι → S → Prop),
      ∀ (i : ι) (u : List Γ), u ∈ L i ↔ acc i (u.foldl step init) := by
  classical
  choose σ hσ D hD using hL
  haveI : ∀ i, Finite (σ i) := fun i => @Finite.of_fintype _ (hσ i)
  refine ⟨∀ i, σ i, inferInstance, fun s c i => (D i).step (s i) c, fun i => (D i).start,
    fun i s => s i ∈ (D i).accept, ?_⟩
  have key : ∀ (u : List Γ) (s : ∀ i, σ i) (i : ι),
      (u.foldl (fun s c i => (D i).step (s i) c) s) i = u.foldl (D i).step (s i) := by
    intro u
    induction u with
    | nil => intro s i; rfl
    | cons c u ih => intro s i; exact ih _ i
  intro i u
  show u ∈ L i ↔ (u.foldl (fun s c i => (D i).step (s i) c) (fun i => (D i).start)) i
    ∈ (D i).accept
  rw [key, ← hD i]
  rfl

/-! ## A chain of pieces that halts early -/

/-- Dropping the empty tail of a bounded concatenation. -/
lemma flatMap_range_trunc {C : Type} (g : ℕ → List C) {m n : ℕ} (hmn : m ≤ n)
    (h : ∀ j, m ≤ j → j < n → g j = []) :
    (List.range n).flatMap g = (List.range m).flatMap g := by
  induction n with
  | zero =>
      have : m = 0 := by omega
      subst this; rfl
  | succ n ih =>
      rcases Nat.lt_or_ge n m with hlt | hge
      · have : m = n + 1 := by omega
        subst this; rfl
      · rw [List.range_succ, List.flatMap_append, ih hge (fun j hj hjn => h j hj (by omega))]
        simp [h n hge (by omega)]

namespace TwoWay

variable {A B Q : Type}

/-- **The output of the run is the concatenation of the outputs of a chain of
pieces which halts at the index `h`**, the pieces after `h` producing no
output. -/
theorem runOut_of_chain_halt (M : TwoWay A B Q) (w : List A) (n h : ℕ) (hh : h < n)
    (g : ℕ → List B) (c : ℕ → ℕ) (st : ℕ → Q) (hc0 : c 0 = 0) (hst0 : st 0 = M.init)
    (hnil : ∀ j, h < j → j < n → g j = [])
    (hchain : ∀ j ≤ h, ∀ t, cfgAt M w t = some (Cfg.conf (w.take (c j)) (st j) (w.drop (c j))) →
      ∃ d, outRange M w t (t + d) = g j ∧
        (if j = h then cfgAt M w (t + d) = some Cfg.halt
          else cfgAt M w (t + d)
            = some (Cfg.conf (w.take (c (j + 1))) (st (j + 1)) (w.drop (c (j + 1)))))) :
    runOut M w = (List.range n).flatMap g := by
  rw [flatMap_range_trunc g (by omega : h + 1 ≤ n) (fun j hj hjn => hnil j (by omega) hjn)]
  refine runOut_of_chain M w (h + 1) (by omega) g c st hc0 hst0 ?_
  intro j hj t ht
  obtain ⟨d, hout, hnext⟩ := hchain j (by omega) t ht
  refine ⟨d, hout, ?_⟩
  by_cases hje : j = h
  · rw [if_pos (by omega)]
    rw [if_pos hje] at hnext
    exact hnext
  · rw [if_neg (by omega)]
    rw [if_neg hje] at hnext
    exact hnext

end TwoWay

end Lax916827Proofs.Transducers
