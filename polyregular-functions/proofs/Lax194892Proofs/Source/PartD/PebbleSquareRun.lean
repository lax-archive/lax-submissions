/-
The run of the simulating machine of `RequestProject/PartD/PebbleSquareDef.lean`.

This file contains the walking lemmas -- what the five auxiliary phases of the simulating machine
do -- and the step-by-step correspondence between a run of a `(k+1)`-pebble transducer `M` on `w`
and a run of the `k`-pebble transducer `sim M` on the marked square of the padded input.
-/
import Lax194892Proofs.Source.PartD.PebbleSquareDef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebSq

/-! ## Generalities on runs of pebble transducers -/

section Generic

variable {C D R : Type} {kk : ℕ} {M : Pebble C D R kk} {s : List C}

lemma rch_trans {c c' c'' : PebbleCfg R} {v v' : List D}
    (h : M.Reaches s c v c') (h' : M.Reaches s c' v' c'') : M.Reaches s c (v ++ v') c'' := by
  induction h with
  | refl c => simpa using h'
  | step hs _ ih => exact (List.append_assoc _ _ _ ▸ Pebble.Reaches.step hs (ih h'))

lemma rch_one {c c' : PebbleCfg R} {v : List D} (h : M.stepCfg s c = some (v, c')) :
    M.Reaches s c v c' := by
  simpa using Pebble.Reaches.step h (Pebble.Reaches.refl c')

/-- A chain of steps that produce no output. -/
lemma rch_chain (c : ℕ → PebbleCfg R) :
    ∀ n : ℕ, (∀ e, e < n → M.stepCfg s (c e) = some ([], c (e + 1))) →
      M.Reaches s (c 0) [] (c n) := by
  intro n
  induction n with
  | zero => intro _; exact Pebble.Reaches.refl _
  | succ n ih =>
      intro h
      have h1 : M.Reaches s (c 0) [] (c n) := ih (fun e he => h e (by omega))
      have h2 : M.Reaches s (c n) [] (c (n + 1)) := rch_one (h n (by omega))
      simpa using rch_trans h1 h2

/-- Two configurations with the same step behave the same, as long as the one that is known to
reach the halting vertex is not itself the halting vertex. -/
lemma rch_shift {c₁ c₂ : PebbleCfg R} {v : List D} (h : M.stepCfg s c₁ = M.stepCfg s c₂)
    (hne : c₂ ≠ PebbleCfg.halt) (hr : M.Reaches s c₂ v PebbleCfg.halt) :
    M.Reaches s c₁ v PebbleCfg.halt := by
  cases hr with
  | refl c => exact absurd rfl hne
  | step hs hr' => exact Pebble.Reaches.step (h.trans hs) hr'

/-! ### The one-step lemmas -/

variable {q q' : R} {st : List C}

lemma stepCfg_out' {q q' : R} {st : List ℕ} {b : D}
    (h : M.step q (viewOf s st) = (q', PebbleAction.out b)) :
    M.stepCfg s (PebbleCfg.conf q st) = some ([b], PebbleCfg.conf q' st) := by
  simp only [Pebble.stepCfg, h]

lemma stepCfg_terminate' {q q' : R} {st : List ℕ}
    (h : M.step q (viewOf s st) = (q', PebbleAction.terminate)) :
    M.stepCfg s (PebbleCfg.conf q st) = some ([], PebbleCfg.halt) := by
  simp only [Pebble.stepCfg, h]

lemma stepCfg_push' {q q' : R} {st : List ℕ}
    (h : M.step q (viewOf s st) = (q', PebbleAction.push)) (hlt : st.length < kk) :
    M.stepCfg s (PebbleCfg.conf q st) = some ([], PebbleCfg.conf q' (st ++ [0])) := by
  simp only [Pebble.stepCfg, h]
  rw [if_pos hlt]

lemma stepCfg_pop' {q q' : R} {pre : List ℕ} {p : ℕ}
    (h : M.step q (viewOf s (pre ++ [p])) = (q', PebbleAction.pop)) :
    M.stepCfg s (PebbleCfg.conf q (pre ++ [p])) = some ([], PebbleCfg.conf q' pre) := by
  simp only [Pebble.stepCfg, h]
  rw [if_neg (by simp)]
  simp

lemma stepCfg_congr {q₁ q₂ : R} {st : List ℕ}
    (h : M.step q₁ (viewOf s st) = M.step q₂ (viewOf s st)) :
    M.stepCfg s (PebbleCfg.conf q₁ st) = M.stepCfg s (PebbleCfg.conf q₂ st) := by
  simp only [Pebble.stepCfg, h]

lemma stepCfg_right' {q q' : R} {pre : List ℕ} {p : ℕ}
    (h : M.step q (viewOf s (pre ++ [p])) = (q', PebbleAction.move true))
    (hp : p < s.length) :
    M.stepCfg s (PebbleCfg.conf q (pre ++ [p])) = some ([], PebbleCfg.conf q' (pre ++ [p + 1])) := by
  simp only [Pebble.stepCfg, h, List.getLast?_concat, List.dropLast_concat]
  simp [hp]

lemma stepCfg_left' {q q' : R} {pre : List ℕ} {p : ℕ}
    (h : M.step q (viewOf s (pre ++ [p])) = (q', PebbleAction.move false))
    (hp : 0 < p) :
    M.stepCfg s (PebbleCfg.conf q (pre ++ [p])) = some ([], PebbleCfg.conf q' (pre ++ [p - 1])) := by
  simp only [Pebble.stepCfg, h, List.getLast?_concat, List.dropLast_concat]
  simp [hp]

end Generic

/-! ## The three tests on the marked square of the padded input -/

section Tests

variable {A : Type} {w : List A} {base : List ℕ} {x : ℕ}

lemma topMark_sq (hx : x ≤ (w.length + 2) * (w.length + 2)) :
    topMark (viewOf (sqOf w) (base ++ [x])) = true ↔ IsMark (w.length + 2) x := by
  have h := topMark_iff (u := pad w) (base := base) (x := x) (by rw [pad_len]; exact hx)
  rw [pad_len] at h
  exact h

lemma topStart_sq (hx : x ≤ (w.length + 2) * (w.length + 2)) :
    topStart (viewOf (sqOf w) (base ++ [x])) = true ↔ IsStart (w.length + 2) x := by
  have h := topStart_iff (u := pad w) (base := base) (x := x) (by rw [pad_len]; omega)
    (by rw [pad_len]; exact hx)
  rw [pad_len] at h
  exact h

lemma topCoin_sq : topCoin (viewOf (sqOf w) (base ++ [x])) = true ↔ x ∈ base :=
  topCoin_append _ _ _

end Tests

/-! ## The walking phases -/

section Walk

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q (k + 1)} {w : List A}
  {q : Q} {dp : Bool} {ct : Option A × Option A} {base : List ℕ} {x : ℕ}

lemma step_mR_move (hx : x < (w.length + 2) * (w.length + 2))
    (hnm : ¬ IsMark (w.length + 2) x) :
    (sim M).stepCfg (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [x]))
      = some ([], PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [x + 1])) := by
  have hts : topMark (viewOf (sqOf w) (base ++ [x])) = false := by
    rw [Bool.eq_false_iff, ne_eq, topMark_sq (le_of_lt hx)]
    exact hnm
  refine stepCfg_right' ?_ (by rw [sqOf_length]; exact hx)
  simp [sim, runStep, hts]

lemma step_mL_move (hx0 : 0 < x) (hx : x ≤ (w.length + 2) * (w.length + 2))
    (hnm : ¬ IsMark (w.length + 2) x) :
    (sim M).stepCfg (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.mL) (base ++ [x]))
      = some ([], PebbleCfg.conf (q, dp, ct, Ph.mL) (base ++ [x - 1])) := by
  have hts : topMark (viewOf (sqOf w) (base ++ [x])) = false := by
    rw [Bool.eq_false_iff, ne_eq, topMark_sq hx]
    exact hnm
  refine stepCfg_left' ?_ hx0
  simp [sim, runStep, hts]

lemma step_s1_move (hx0 : 0 < x) (hx : x ≤ (w.length + 2) * (w.length + 2))
    (hns : ¬ IsStart (w.length + 2) x) :
    (sim M).stepCfg (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.s1) (base ++ [x]))
      = some ([], PebbleCfg.conf (q, dp, ct, Ph.s1) (base ++ [x - 1])) := by
  have hts : topStart (viewOf (sqOf w) (base ++ [x])) = false := by
    rw [Bool.eq_false_iff, ne_eq, topStart_sq hx]
    exact hns
  refine stepCfg_left' ?_ hx0
  simp [sim, runStep, hts]

lemma step_s1_hit (hx : x < (w.length + 2) * (w.length + 2))
    (hs : IsStart (w.length + 2) x) :
    (sim M).stepCfg (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.s1) (base ++ [x]))
      = some ([], PebbleCfg.conf (q, dp, ct, Ph.run) (base ++ [x + 1])) := by
  have hts : topStart (viewOf (sqOf w) (base ++ [x])) = true :=
    (topStart_sq (le_of_lt hx)).mpr hs
  refine stepCfg_right' ?_ (by rw [sqOf_length]; exact hx)
  simp [sim, runStep, hts]

lemma step_sM_move (hx0 : 0 < x) (hx : x ≤ (w.length + 2) * (w.length + 2))
    (hns : ¬ IsStart (w.length + 2) x) :
    (sim M).stepCfg (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.sM) (base ++ [x]))
      = some ([], PebbleCfg.conf (q, dp, ct, Ph.sM) (base ++ [x - 1])) := by
  have hts : topStart (viewOf (sqOf w) (base ++ [x])) = false := by
    rw [Bool.eq_false_iff, ne_eq, topStart_sq hx]
    exact hns
  refine stepCfg_left' ?_ hx0
  simp [sim, runStep, hts]

lemma step_sM_hit (hx : x < (w.length + 2) * (w.length + 2))
    (hs : IsStart (w.length + 2) x) :
    (sim M).stepCfg (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.sM) (base ++ [x]))
      = some ([], PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [x + 1])) := by
  have hts : topStart (viewOf (sqOf w) (base ++ [x])) = true :=
    (topStart_sq (le_of_lt hx)).mpr hs
  refine stepCfg_right' ?_ (by rw [sqOf_length]; exact hx)
  simp [sim, runStep, hts]

lemma step_coin_move (hx : x < (w.length + 2) * (w.length + 2)) (hnb : x ∉ base) :
    (sim M).stepCfg (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.coin) (base ++ [x]))
      = some ([], PebbleCfg.conf (q, dp, ct, Ph.coin) (base ++ [x + 1])) := by
  have hts : topCoin (viewOf (sqOf w) (base ++ [x])) = false := by
    rw [Bool.eq_false_iff, ne_eq, topCoin_sq]
    exact hnb
  refine stepCfg_right' ?_ (by rw [sqOf_length]; exact hx)
  simp [sim, runStep, hts]

lemma step_coin_hit (hx0 : 0 < x) (hb : x ∈ base) :
    (sim M).stepCfg (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.coin) (base ++ [x]))
      = some ([], PebbleCfg.conf (q, dp, ct, Ph.s1) (base ++ [x - 1])) := by
  have hts : topCoin (viewOf (sqOf w) (base ++ [x])) = true := topCoin_sq.mpr hb
  refine stepCfg_left' ?_ hx0
  simp [sim, runStep, hts]

/-- Walking to the right in the phase `mR`. -/
lemma walk_mR (dist g : ℕ) (hg : g + dist ≤ (w.length + 2) * (w.length + 2))
    (hnm : ∀ e, e < dist → ¬ IsMark (w.length + 2) (g + e)) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [g])) []
      (PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [g + dist])) := by
  have h := rch_chain (M := sim M) (s := sqOf w)
    (fun e => PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [g + e])) dist ?_
  · simpa using h
  · intro e he
    exact step_mR_move (by omega) (hnm e he)

/-- Walking to the left in the phase `mL`. -/
lemma walk_mL (dist g : ℕ) (hd : dist ≤ g) (hg : g ≤ (w.length + 2) * (w.length + 2))
    (hnm : ∀ e, e < dist → ¬ IsMark (w.length + 2) (g - e)) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.mL) (base ++ [g])) []
      (PebbleCfg.conf (q, dp, ct, Ph.mL) (base ++ [g - dist])) := by
  have h := rch_chain (M := sim M) (s := sqOf w)
    (fun e => PebbleCfg.conf (q, dp, ct, Ph.mL) (base ++ [g - e])) dist ?_
  · simpa using h
  · intro e he
    exact step_mL_move (by omega) (by omega) (hnm e he)

/-- Walking to the left in the phase `s1`. -/
lemma walk_s1 (dist g : ℕ) (hd : dist ≤ g) (hg : g ≤ (w.length + 2) * (w.length + 2))
    (hns : ∀ e, e < dist → ¬ IsStart (w.length + 2) (g - e)) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.s1) (base ++ [g])) []
      (PebbleCfg.conf (q, dp, ct, Ph.s1) (base ++ [g - dist])) := by
  have h := rch_chain (M := sim M) (s := sqOf w)
    (fun e => PebbleCfg.conf (q, dp, ct, Ph.s1) (base ++ [g - e])) dist ?_
  · simpa using h
  · intro e he
    exact step_s1_move (by omega) (by omega) (hns e he)

/-- Walking to the left in the phase `sM`. -/
lemma walk_sM (dist g : ℕ) (hd : dist ≤ g) (hg : g ≤ (w.length + 2) * (w.length + 2))
    (hns : ∀ e, e < dist → ¬ IsStart (w.length + 2) (g - e)) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.sM) (base ++ [g])) []
      (PebbleCfg.conf (q, dp, ct, Ph.sM) (base ++ [g - dist])) := by
  have h := rch_chain (M := sim M) (s := sqOf w)
    (fun e => PebbleCfg.conf (q, dp, ct, Ph.sM) (base ++ [g - e])) dist ?_
  · simpa using h
  · intro e he
    exact step_sM_move (by omega) (by omega) (hns e he)

/-- Walking to the right in the phase `coin`. -/
lemma walk_coin (dist g : ℕ) (hg : g + dist ≤ (w.length + 2) * (w.length + 2))
    (hnb : ∀ e, e < dist → (g + e) ∉ base) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.coin) (base ++ [g])) []
      (PebbleCfg.conf (q, dp, ct, Ph.coin) (base ++ [g + dist])) := by
  have h := rch_chain (M := sim M) (s := sqOf w)
    (fun e => PebbleCfg.conf (q, dp, ct, Ph.coin) (base ++ [g + e])) dist ?_
  · simpa using h
  · intro e he
    exact step_coin_move (by omega) (hnb e he)

end Walk

/-- The first gap of a list that is met when walking to the right from `g`. -/
lemma exists_first_hit (base : List ℕ) (g : ℕ) (h : ∃ y ∈ base, g ≤ y) :
    ∃ d, (g + d) ∈ base ∧ ∀ e, e < d → (g + e) ∉ base := by
  classical
  have hex : ∃ n, (g + n) ∈ base := by
    obtain ⟨y, hy, hgy⟩ := h
    exact ⟨y - g, by rwa [show g + (y - g) = y by omega]⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro e he
  exact Nat.find_min hex he

/-! ## The gaps of the marked square that the encoding uses -/

section Arith

variable {A : Type} (w : List A)

lemma gp_lt {i j : ℕ} (hi : i ≤ w.length) (hj : j ≤ w.length + 1) :
    gp w i j < (w.length + 2) * (w.length + 2) := by
  have h1 : i * (w.length + 2) ≤ w.length * (w.length + 2) := Nat.mul_le_mul hi le_rfl
  have h2 : w.length * (w.length + 2) + (w.length + 2) + (w.length + 2)
      = (w.length + 2) * (w.length + 2) := by ring
  simp only [gp]
  omega

lemma gp_pos {i j : ℕ} (hj : 0 < j) : 0 < gp w i j := by
  simp only [gp]; omega

lemma gp_succ_mul {p : ℕ} (hp : 0 < p) :
    p * (w.length + 2) = (p - 1) * (w.length + 2) + (w.length + 2) := by
  cases p with
  | zero => omega
  | succ n => simp [Nat.succ_mul]

lemma mark_gp {i : ℕ} (hi : i ≤ w.length) : IsMark (w.length + 2) (gp w i (i + 1)) :=
  ⟨i, by omega, rfl⟩

lemma start_gp {i : ℕ} (hi : i ≤ w.length) : IsStart (w.length + 2) (gp w i 0) :=
  ⟨i, by omega, by simp [gp]⟩

lemma not_mark_gp {i j : ℕ} (hj : j < w.length + 2) (hne : j ≠ i + 1) :
    ¬ IsMark (w.length + 2) (gp w i j) := by
  rintro ⟨i', hi', hEq⟩
  simp only [gp] at hEq
  obtain ⟨h1, h2⟩ := coord_unique hj (show i' + 1 < w.length + 2 by omega) hEq
  exact hne (by omega)

lemma not_start_gp {i j : ℕ} (hj0 : 0 < j) (hj : j < w.length + 2) :
    ¬ IsStart (w.length + 2) (gp w i j) := by
  rintro ⟨i', hi', hEq⟩
  simp only [gp] at hEq
  obtain ⟨h1, h2⟩ := coord_unique (N := w.length + 2) hj
    (show (0 : ℕ) < w.length + 2 by omega)
    (show i * (w.length + 2) + j = i' * (w.length + 2) + 0 by omega)
  omega

lemma not_mark_after {p f : ℕ} (hf1 : 1 ≤ f) (hf2 : f ≤ w.length + 2) :
    ¬ IsMark (w.length + 2) (gp w p (p + 1) + f) := by
  rintro ⟨i, hi, hEq⟩
  simp only [gp] at hEq
  exact mark_spacing hEq.symm hf1 hf2

lemma not_mark_before {p f x : ℕ} (hf1 : 1 ≤ f) (hf2 : f ≤ w.length + 2)
    (hx : x + f = gp w p (p + 1)) : ¬ IsMark (w.length + 2) x := by
  rintro ⟨i, hi, rfl⟩
  simp only [gp] at hx
  exact mark_spacing (N := w.length + 2) (i := p) (p := i) (f := f) (by omega) hf1 hf2

end Arith

/-! ## The composite walks -/

section Composite

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q (k + 1)} {w : List A}
  {q : Q} {dp : Bool} {ct : Option A × Option A} {base : List ℕ}

/-- At a marked gap the phase `mR` behaves like the phase `run`. -/
lemma reaches_of_mark_mR {x : ℕ} (hmark : IsMark (w.length + 2) x)
    (hx : x ≤ (w.length + 2) * (w.length + 2)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.run) (base ++ [x])) v
      PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [x])) v
      PebbleCfg.halt := by
  refine rch_shift ?_ (by simp) hcont
  refine stepCfg_congr ?_
  have h : topMark (viewOf (sqOf w) (base ++ [x])) = true := (topMark_sq hx).mpr hmark
  simp [sim, runStep, h]

/-- At a marked gap the phase `mL` behaves like the phase `run`. -/
lemma reaches_of_mark_mL {x : ℕ} (hmark : IsMark (w.length + 2) x)
    (hx : x ≤ (w.length + 2) * (w.length + 2)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.run) (base ++ [x])) v
      PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.mL) (base ++ [x])) v
      PebbleCfg.halt := by
  refine rch_shift ?_ (by simp) hcont
  refine stepCfg_congr ?_
  have h : topMark (viewOf (sqOf w) (base ++ [x])) = true := (topMark_sq hx).mpr hmark
  simp [sim, runStep, h]

/-- Walking from just after the marked gap of the block `p` to the marked gap of the block
`p + 1`. -/
lemma to_mark_right {p : ℕ} (hp : p + 1 ≤ w.length) :
    (sim M).Reaches (sqOf w)
      (PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [gp w p (p + 1) + 1])) []
      (PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [gp w (p + 1) (p + 2)])) := by
  have heq : gp w p (p + 1) + 1 + (w.length + 2) = gp w (p + 1) (p + 2) := by
    simp only [gp]; ring
  have h := walk_mR (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
    (w.length + 2) (gp w p (p + 1) + 1)
    (by rw [heq]; exact le_of_lt (gp_lt w (by omega) (by omega))) ?_
  · rwa [heq] at h
  · intro e he
    have hx : gp w p (p + 1) + 1 + e = gp w p (p + 1) + (1 + e) := by omega
    rw [hx]
    exact not_mark_after w (by omega) (by omega)

/-- Walking from just before the marked gap of the block `p` to the marked gap of the block
`p - 1`. -/
lemma to_mark_left {p : ℕ} (hp0 : 0 < p) (hp : p ≤ w.length) :
    (sim M).Reaches (sqOf w)
      (PebbleCfg.conf (q, dp, ct, Ph.mL) (base ++ [gp w p (p + 1) - 1])) []
      (PebbleCfg.conf (q, dp, ct, Ph.mL) (base ++ [gp w (p - 1) p])) := by
  have hpm := gp_succ_mul w hp0
  have hsub : gp w p (p + 1) - 1 - (w.length + 2) = gp w (p - 1) p := by
    simp only [gp]; omega
  have hd : w.length + 2 ≤ gp w p (p + 1) - 1 := by
    simp only [gp]; omega
  have h := walk_mL (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
    (w.length + 2) (gp w p (p + 1) - 1) hd
    (le_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (gp_lt w hp (by omega)))) ?_
  · rwa [hsub] at h
  · intro e he
    refine not_mark_before w (p := p) (f := 1 + e) (by omega) (by omega) ?_
    simp only [gp] at hpm ⊢
    omega

/-- Walking left to the start of the block and then one step to the right. -/
lemma to_offset1 {i m : ℕ} (hi : i ≤ w.length) (hm : m ≤ w.length + 1) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.s1) (base ++ [gp w i m])) []
      (PebbleCfg.conf (q, dp, ct, Ph.run) (base ++ [gp w i 1])) := by
  have h0 : gp w i m - m = gp w i 0 := by simp only [gp]; omega
  have hwalk := walk_s1 (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
    m (gp w i m) (by simp only [gp]; omega) (le_of_lt (gp_lt w hi hm)) ?_
  · rw [h0] at hwalk
    have hstep := step_s1_hit (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
      (x := gp w i 0) (gp_lt w hi (by omega)) (start_gp w hi)
    have h1 : gp w i 0 + 1 = gp w i 1 := by simp only [gp]
    rw [h1] at hstep
    simpa using rch_trans hwalk (rch_one hstep)
  · intro e he
    have hx : gp w i m - e = gp w i (m - e) := by simp only [gp]; omega
    rw [hx]
    exact not_start_gp w (by omega) (by omega)

/-- Walking left to the start of the block and then right to its marked gap. -/
lemma to_mark_sM {i m : ℕ} (hi : i ≤ w.length) (hm : m ≤ w.length + 1) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.sM) (base ++ [gp w i m])) []
      (PebbleCfg.conf (q, dp, ct, Ph.mR) (base ++ [gp w i (i + 1)])) := by
  have h0 : gp w i m - m = gp w i 0 := by simp only [gp]; omega
  have hwalk := walk_sM (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
    m (gp w i m) (by simp only [gp]; omega) (le_of_lt (gp_lt w hi hm)) ?_
  · rw [h0] at hwalk
    have hstep := step_sM_hit (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
      (x := gp w i 0) (gp_lt w hi (by omega)) (start_gp w hi)
    have h1 : gp w i 0 + 1 = gp w i 1 := by simp only [gp]
    rw [h1] at hstep
    have hwalk2 := walk_mR (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
      i (gp w i 1) ?_ ?_
    · have h2 : gp w i 1 + i = gp w i (i + 1) := by simp only [gp]; omega
      rw [h2] at hwalk2
      have := rch_trans hwalk (rch_trans (rch_one hstep) hwalk2)
      simpa using this
    · have h2 : gp w i 1 + i = gp w i (i + 1) := by simp only [gp]; omega
      rw [h2]
      exact le_of_lt (gp_lt w hi (by omega))
    · intro e he
      have hx : gp w i 1 + e = gp w i (1 + e) := by simp only [gp]; omega
      rw [hx]
      exact not_mark_gp w (by omega) (by omega)
  · intro e he
    have hx : gp w i m - e = gp w i (m - e) := by simp only [gp]; omega
    rw [hx]
    exact not_start_gp w (by omega) (by omega)

/-- Walking right until the topmost pebble meets a lower one, and then to the offset `1` of the
block in which the lower pebbles sit. -/
lemma coin_to_offset1 {i : ℕ} (hi : i ≤ w.length) (hne : base ≠ [])
    (hb : ∀ x ∈ base, ∃ m, m ≤ w.length ∧ x = gp w i (m + 1)) :
    (sim M).Reaches (sqOf w) (PebbleCfg.conf (q, dp, ct, Ph.coin) (base ++ [0])) []
      (PebbleCfg.conf (q, dp, ct, Ph.run) (base ++ [gp w i 1])) := by
  obtain ⟨y, hy⟩ : ∃ y, y ∈ base := by
    cases base with
    | nil => exact absurd rfl hne
    | cons a l => exact ⟨a, by simp⟩
  obtain ⟨d, hd, hmin⟩ := exists_first_hit base 0 ⟨y, hy, Nat.zero_le _⟩
  rw [Nat.zero_add] at hd
  obtain ⟨m, hm, hdm⟩ := hb d hd
  have hwalk := walk_coin (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base) d 0 ?_ ?_
  · rw [Nat.zero_add] at hwalk
    have hstep := step_coin_hit (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
      (x := d) (by rw [hdm]; exact gp_pos w (by omega)) hd
    have hd1 : d - 1 = gp w i m := by rw [hdm]; simp only [gp]; omega
    rw [hd1] at hstep
    have hfin := to_offset1 (M := M) (w := w) (q := q) (dp := dp) (ct := ct) (base := base)
      (i := i) (m := m) hi (by omega)
    have := rch_trans hwalk (rch_trans (rch_one hstep) hfin)
    simpa using this
  · rw [Nat.zero_add, hdm]
    exact le_of_lt (gp_lt w hi (by omega))
  · intro e he
    simpa using hmin e he

end Composite


/-! ## One step of the simulated machine -/

section Step

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q (k + 1)} {w : List A}

lemma encStack_cons {p₁ : ℕ} {R : List ℕ} (hR : R ≠ []) :
    encStack w (p₁ :: R) = R.map (fun p => gp w p₁ (p + 1)) := by
  cases R with
  | nil => exact absurd rfl hR
  | cons a l => rfl

lemma encSt_deep {q : Q} {p₁ : ℕ} {R : List ℕ} (hR : R ≠ []) :
    encSt w q (p₁ :: R) = (q, true, (padLet w p₁, padLet w (p₁ + 1)), Ph.run) := by
  cases R with
  | nil => exact absurd rfl hR
  | cons a l => rfl

lemma ctxSt_deep {p₁ : ℕ} {R : List ℕ} (hR : R ≠ []) :
    ctxSt w (p₁ :: R) = (padLet w p₁, padLet w (p₁ + 1)) := by
  cases R with
  | nil => exact absurd rfl hR
  | cons a l => rfl

/-- The step of the simulating machine in the phase `run`. -/
lemma sim_step_eq {q q' : Q} {st : List ℕ} {act : PebbleAction B}
    (hval : ∀ p ∈ st, p ≤ w.length) (hact : M.step q (viewOf w st) = (q', act)) :
    (sim M).step (encSt w q st) (viewOf (sqOf w) (encStack w st))
      = transl (decide (2 ≤ st.length)) (ctxSt w st) (viewOf (sqOf w) (encStack w st)) q' act := by
  simp only [sim, encSt, runStep, decView_encSt hval, hact]

/-! ### Outputting a letter and terminating -/

lemma sim_out {q q' : Q} {st : List ℕ} {b : B} (hval : ∀ p ∈ st, p ≤ w.length)
    (hact : M.step q (viewOf w st) = (q', PebbleAction.out b)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q' st)) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q st)) ([b] ++ v) PebbleCfg.halt := by
  refine Pebble.Reaches.step ?_ hcont
  refine stepCfg_out' ?_
  rw [sim_step_eq hval hact]
  rfl

lemma sim_terminate {q q' : Q} {st : List ℕ} (hval : ∀ p ∈ st, p ≤ w.length)
    (hact : M.step q (viewOf w st) = (q', PebbleAction.terminate)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w PebbleCfg.halt) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q st)) ([] ++ v) PebbleCfg.halt := by
  refine Pebble.Reaches.step ?_ hcont
  show (sim M).stepCfg (sqOf w) (PebbleCfg.conf (encSt w q st) (encStack w st))
      = some ([], PebbleCfg.halt)
  refine stepCfg_terminate' (q' := encSt w q' st) ?_
  rw [sim_step_eq hval hact]
  rfl

/-! ### Pushing a pebble -/

lemma sim_push_nil {q q' : Q} (hk : 1 ≤ k)
    (hact : M.step q (viewOf w ([] : List ℕ)) = (q', PebbleAction.push)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q' [0])) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q ([] : List ℕ))) v PebbleCfg.halt := by
  have hstep : (sim M).stepCfg (sqOf w) (encCfg w (PebbleCfg.conf q ([] : List ℕ)))
      = some ([], PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.mR)
        (([] : List ℕ) ++ [0])) := by
    refine stepCfg_push' ?_ (by simpa using hk)
    rw [sim_step_eq (by simp) hact]
    rfl
  have hmark : IsMark (w.length + 2) 1 := by
    have := mark_gp w (i := 0) (Nat.zero_le _)
    simpa [gp] using this
  have hwalk := walk_mR (M := M) (w := w) (q := q') (dp := false)
    (ct := ((none : Option A), (none : Option A))) (base := []) 1 0 (by simp) ?_
  · have htgt : encCfg w (PebbleCfg.conf q' [0])
        = PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.run)
          (([] : List ℕ) ++ [0 + 1]) := by
      simp [encCfg, encSt, ctxSt, encStack, gp]
    rw [htgt] at hcont
    have hend := reaches_of_mark_mR (M := M) (w := w) (q := q') (dp := false)
      (ct := ((none : Option A), (none : Option A))) (base := []) (x := 0 + 1)
      (by simpa using hmark) (by simp) hcont
    have := Pebble.Reaches.step hstep (rch_trans hwalk hend)
    simpa using this
  · intro e he
    have he0 : e = 0 := by omega
    subst he0
    have : (0 : ℕ) + 0 = gp w 0 0 := by simp [gp]
    rw [this]
    exact not_mark_gp w (by omega) (by omega)

lemma sim_push_one {q q' : Q} {p : ℕ} (hp : p ≤ w.length)
    (hact : M.step q (viewOf w [p]) = (q', PebbleAction.push)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q' [p, 0])) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q [p])) v PebbleCfg.halt := by
  have hl := decLet_at (w := w) (i := p) (p := p) hp hp
  have hcfg : encCfg w (PebbleCfg.conf q [p])
      = PebbleCfg.conf (encSt w q [p]) (([] : List ℕ) ++ [gp w p (p + 1)]) := rfl
  have hstep : (sim M).stepCfg (sqOf w)
        (PebbleCfg.conf (encSt w q [p]) (([] : List ℕ) ++ [gp w p (p + 1)]))
      = some ([], PebbleCfg.conf (q', true, (padLet w p, padLet w (p + 1)), Ph.s1)
        (([] : List ℕ) ++ [gp w p (p + 1) - 1])) := by
    refine stepCfg_left' ?_ (gp_pos w (by omega))
    rw [show (([] : List ℕ) ++ [gp w p (p + 1)]) = encStack w [p] from rfl,
      sim_step_eq (by simpa using hp) hact]
    simp [transl, encStack, viewOf, hl.1, hl.2]
  have hsub : gp w p (p + 1) - 1 = gp w p p := by simp only [gp]; omega
  rw [hsub] at hstep
  have htgt : encCfg w (PebbleCfg.conf q' [p, 0])
      = PebbleCfg.conf (q', true, (padLet w p, padLet w (p + 1)), Ph.run)
        (([] : List ℕ) ++ [gp w p 1]) := by
    simp [encCfg, encSt, ctxSt, ctxOf, encStack]
  rw [htgt] at hcont
  have hwalk := to_offset1 (M := M) (w := w) (q := q') (dp := true)
    (ct := (padLet w p, padLet w (p + 1))) (base := []) (i := p) (m := p) hp (by omega)
  rw [hcfg]
  have := Pebble.Reaches.step hstep (rch_trans hwalk hcont)
  simpa using this

lemma sim_push_deep {q q' : Q} {p₁ ptop : ℕ} {mid : List ℕ}
    (hval : ∀ p ∈ p₁ :: (mid ++ [ptop]), p ≤ w.length)
    (hlt : (p₁ :: (mid ++ [ptop])).length < k + 1)
    (hact : M.step q (viewOf w (p₁ :: (mid ++ [ptop]))) = (q', PebbleAction.push)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w)
      (encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop]) ++ [0]))) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))) v
      PebbleCfg.halt := by
  have hp₁ : p₁ ≤ w.length := hval p₁ (by simp)
  have hRne : (mid ++ [ptop]) ≠ [] := by simp
  set base := encStack w (p₁ :: (mid ++ [ptop])) with hbase
  have hbase' : base = (mid ++ [ptop]).map (fun p => gp w p₁ (p + 1)) := by
    rw [hbase, encStack_cons hRne]
  have hbaselen : base.length = mid.length + 1 := by
    rw [hbase']; simp
  have hstep : (sim M).stepCfg (sqOf w) (encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop]))))
      = some ([], PebbleCfg.conf (q', true, (padLet w p₁, padLet w (p₁ + 1)), Ph.coin)
        (base ++ [0])) := by
    refine stepCfg_push' ?_ (by rw [hbaselen]; simp at hlt; omega)
    rw [sim_step_eq hval hact, ctxSt_deep hRne,
      show decide (2 ≤ (p₁ :: (mid ++ [ptop])).length) = true from by simp]
    rfl
  have hne : base ≠ [] := by
    intro h; rw [h] at hbaselen; simp at hbaselen
  have hb : ∀ x ∈ base, ∃ m, m ≤ w.length ∧ x = gp w p₁ (m + 1) := by
    intro x hx
    rw [hbase', List.mem_map] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨m, hval m (by simp [hm]), rfl⟩
  have hwalk := coin_to_offset1 (M := M) (w := w) (q := q') (dp := true)
    (ct := (padLet w p₁, padLet w (p₁ + 1))) (base := base) (i := p₁) hp₁ hne hb
  have htgt : encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop]) ++ [0]))
      = PebbleCfg.conf (q', true, (padLet w p₁, padLet w (p₁ + 1)), Ph.run)
        (base ++ [gp w p₁ 1]) := by
    rw [show encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop]) ++ [0]))
        = PebbleCfg.conf (encSt w q' (p₁ :: ((mid ++ [ptop]) ++ [0])))
          (encStack w (p₁ :: ((mid ++ [ptop]) ++ [0]))) from rfl]
    rw [encSt_deep (by simp), encStack_cons (by simp), hbase', List.map_append]
    simp
  rw [htgt] at hcont
  have := Pebble.Reaches.step hstep (rch_trans hwalk hcont)
  simpa using this

/-! ### Popping a pebble -/

lemma sim_pop_one {q q' : Q} {p : ℕ} (hp : p ≤ w.length)
    (hact : M.step q (viewOf w [p]) = (q', PebbleAction.pop)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q' ([] : List ℕ))) v
      PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q [p])) v PebbleCfg.halt := by
  have hcfg : encCfg w (PebbleCfg.conf q [p])
      = PebbleCfg.conf (encSt w q [p]) (([] : List ℕ) ++ [gp w p (p + 1)]) := rfl
  have hstep : (sim M).stepCfg (sqOf w)
        (PebbleCfg.conf (encSt w q [p]) (([] : List ℕ) ++ [gp w p (p + 1)]))
      = some ([], PebbleCfg.conf
        (q', false, ((none : Option A), (none : Option A)), Ph.run) ([] : List ℕ)) := by
    refine stepCfg_pop' ?_
    rw [show (([] : List ℕ) ++ [gp w p (p + 1)]) = encStack w [p] from rfl,
      sim_step_eq (by simpa using hp) hact]
    rfl
  have htgt : encCfg w (PebbleCfg.conf q' ([] : List ℕ))
      = PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.run)
        ([] : List ℕ) := rfl
  rw [htgt] at hcont
  rw [hcfg]
  simpa using Pebble.Reaches.step hstep hcont

lemma sim_pop_two {q q' : Q} {p₁ p₂ : ℕ} (hp₁ : p₁ ≤ w.length) (hp₂ : p₂ ≤ w.length)
    (hact : M.step q (viewOf w [p₁, p₂]) = (q', PebbleAction.pop)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q' [p₁])) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q [p₁, p₂])) v PebbleCfg.halt := by
  have hcfg : encCfg w (PebbleCfg.conf q [p₁, p₂])
      = PebbleCfg.conf (encSt w q [p₁, p₂]) (([] : List ℕ) ++ [gp w p₁ (p₂ + 1)]) := rfl
  have hstep : (sim M).stepCfg (sqOf w)
        (PebbleCfg.conf (encSt w q [p₁, p₂]) (([] : List ℕ) ++ [gp w p₁ (p₂ + 1)]))
      = some ([], PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.sM)
        (([] : List ℕ) ++ [gp w p₁ (p₂ + 1) - 1])) := by
    refine stepCfg_left' ?_ (gp_pos w (by omega))
    rw [show (([] : List ℕ) ++ [gp w p₁ (p₂ + 1)]) = encStack w [p₁, p₂] from rfl,
      sim_step_eq (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> assumption) hact]
    simp [transl, encStack, viewOf]
  have hsub : gp w p₁ (p₂ + 1) - 1 = gp w p₁ p₂ := by simp only [gp]; omega
  rw [hsub] at hstep
  have hwalk := to_mark_sM (M := M) (w := w) (q := q') (dp := false)
    (ct := ((none : Option A), (none : Option A))) (base := []) (i := p₁) (m := p₂)
    hp₁ (by omega)
  have htgt : encCfg w (PebbleCfg.conf q' [p₁])
      = PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.run)
        (([] : List ℕ) ++ [gp w p₁ (p₁ + 1)]) := rfl
  rw [htgt] at hcont
  have hend := reaches_of_mark_mR (M := M) (w := w) (q := q') (dp := false)
    (ct := ((none : Option A), (none : Option A))) (base := []) (x := gp w p₁ (p₁ + 1))
    (mark_gp w hp₁) (le_of_lt (gp_lt w hp₁ (by omega))) hcont
  rw [hcfg]
  have := Pebble.Reaches.step hstep (rch_trans hwalk hend)
  simpa using this

lemma sim_pop_deep {q q' : Q} {p₁ ptop : ℕ} {mid : List ℕ} (hmid : mid ≠ [])
    (hval : ∀ p ∈ p₁ :: (mid ++ [ptop]), p ≤ w.length)
    (hact : M.step q (viewOf w (p₁ :: (mid ++ [ptop]))) = (q', PebbleAction.pop)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q' (p₁ :: mid))) v
      PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))) v
      PebbleCfg.halt := by
  have hRne : (mid ++ [ptop]) ≠ [] := by simp
  set base := mid.map (fun p => gp w p₁ (p + 1)) with hbase
  have hcfg : encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))
      = PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop]))) (base ++ [gp w p₁ (ptop + 1)]) := by
    rw [show encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))
        = PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop])))
          (encStack w (p₁ :: (mid ++ [ptop]))) from rfl]
    rw [encStack_cons hRne, List.map_append, hbase]
    simp
  have hlen : (viewOf (sqOf w) (encStack w (p₁ :: (mid ++ [ptop])))).length ≠ 1 := by
    rw [encStack_cons hRne]
    simp only [viewOf, List.length_map, List.length_append, List.length_singleton]
    have : mid.length ≠ 0 := by
      intro h; exact hmid (List.eq_nil_of_length_eq_zero h)
    omega
  have hstep : (sim M).stepCfg (sqOf w)
        (PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop]))) (base ++ [gp w p₁ (ptop + 1)]))
      = some ([], PebbleCfg.conf
        (q', true, (padLet w p₁, padLet w (p₁ + 1)), Ph.run) base) := by
    refine stepCfg_pop' ?_
    rw [show (base ++ [gp w p₁ (ptop + 1)]) = encStack w (p₁ :: (mid ++ [ptop])) by
      rw [encStack_cons hRne, List.map_append, hbase]; simp]
    rw [sim_step_eq hval hact, ctxSt_deep hRne]
    simp [transl, hlen]
  have htgt : encCfg w (PebbleCfg.conf q' (p₁ :: mid))
      = PebbleCfg.conf (q', true, (padLet w p₁, padLet w (p₁ + 1)), Ph.run) base := by
    rw [show encCfg w (PebbleCfg.conf q' (p₁ :: mid))
        = PebbleCfg.conf (encSt w q' (p₁ :: mid)) (encStack w (p₁ :: mid)) from rfl]
    rw [encSt_deep hmid, encStack_cons hmid, hbase]
  rw [htgt] at hcont
  rw [hcfg]
  simpa using Pebble.Reaches.step hstep hcont

/-! ### Moving the topmost pebble -/

lemma sim_move_one_right {q q' : Q} {p : ℕ} (hp : p < w.length)
    (hact : M.step q (viewOf w [p]) = (q', PebbleAction.move true)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q' [p + 1])) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q [p])) v PebbleCfg.halt := by
  have hcfg : encCfg w (PebbleCfg.conf q [p])
      = PebbleCfg.conf (encSt w q [p]) (([] : List ℕ) ++ [gp w p (p + 1)]) := rfl
  have hstep : (sim M).stepCfg (sqOf w)
        (PebbleCfg.conf (encSt w q [p]) (([] : List ℕ) ++ [gp w p (p + 1)]))
      = some ([], PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.mR)
        (([] : List ℕ) ++ [gp w p (p + 1) + 1])) := by
    refine stepCfg_right' ?_ (by rw [sqOf_length]; exact gp_lt w (by omega) (by omega))
    rw [show (([] : List ℕ) ++ [gp w p (p + 1)]) = encStack w [p] from rfl,
      sim_step_eq (by simpa using le_of_lt hp) hact]
    rfl
  have hwalk := to_mark_right (M := M) (w := w) (q := q') (dp := false)
    (ct := ((none : Option A), (none : Option A))) (base := []) (p := p) (by omega)
  have htgt : encCfg w (PebbleCfg.conf q' [p + 1])
      = PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.run)
        (([] : List ℕ) ++ [gp w (p + 1) (p + 2)]) := rfl
  rw [htgt] at hcont
  have hend := reaches_of_mark_mR (M := M) (w := w) (q := q') (dp := false)
    (ct := ((none : Option A), (none : Option A))) (base := []) (x := gp w (p + 1) (p + 2))
    (mark_gp w (by omega)) (le_of_lt (gp_lt w (by omega) (by omega))) hcont
  rw [hcfg]
  have := Pebble.Reaches.step hstep (rch_trans hwalk hend)
  simpa using this

lemma sim_move_one_left {q q' : Q} {p : ℕ} (hp0 : 0 < p) (hp : p ≤ w.length)
    (hact : M.step q (viewOf w [p]) = (q', PebbleAction.move false)) {v : List B}
    (hcont : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q' [p - 1])) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q [p])) v PebbleCfg.halt := by
  have hcfg : encCfg w (PebbleCfg.conf q [p])
      = PebbleCfg.conf (encSt w q [p]) (([] : List ℕ) ++ [gp w p (p + 1)]) := rfl
  have hstep : (sim M).stepCfg (sqOf w)
        (PebbleCfg.conf (encSt w q [p]) (([] : List ℕ) ++ [gp w p (p + 1)]))
      = some ([], PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.mL)
        (([] : List ℕ) ++ [gp w p (p + 1) - 1])) := by
    refine stepCfg_left' ?_ (gp_pos w (by omega))
    rw [show (([] : List ℕ) ++ [gp w p (p + 1)]) = encStack w [p] from rfl,
      sim_step_eq (by simpa using hp) hact]
    rfl
  have hwalk := to_mark_left (M := M) (w := w) (q := q') (dp := false)
    (ct := ((none : Option A), (none : Option A))) (base := []) (p := p) hp0 hp
  have htgt : encCfg w (PebbleCfg.conf q' [p - 1])
      = PebbleCfg.conf (q', false, ((none : Option A), (none : Option A)), Ph.run)
        (([] : List ℕ) ++ [gp w (p - 1) p]) := by
    have h1 : p - 1 + 1 = p := by omega
    rw [show encCfg w (PebbleCfg.conf q' [p - 1])
        = PebbleCfg.conf (encSt w q' [p - 1]) (encStack w [p - 1]) from rfl]
    simp [encSt, ctxSt, encStack, h1]
  rw [htgt] at hcont
  have hend := reaches_of_mark_mL (M := M) (w := w) (q := q') (dp := false)
    (ct := ((none : Option A), (none : Option A))) (base := []) (x := gp w (p - 1) p)
    (by have := mark_gp w (i := p - 1) (by omega)
        rwa [show p - 1 + 1 = p by omega] at this)
    (le_of_lt (gp_lt w (by omega) (by omega))) hcont
  rw [hcfg]
  have := Pebble.Reaches.step hstep (rch_trans hwalk hend)
  simpa using this

lemma sim_move_deep_right {q q' : Q} {p₁ ptop : ℕ} {mid : List ℕ}
    (hval : ∀ p ∈ p₁ :: (mid ++ [ptop]), p ≤ w.length) (htop : ptop < w.length)
    (hact : M.step q (viewOf w (p₁ :: (mid ++ [ptop]))) = (q', PebbleAction.move true))
    {v : List B}
    (hcont : (sim M).Reaches (sqOf w)
      (encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop + 1])))) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))) v
      PebbleCfg.halt := by
  have hp₁ : p₁ ≤ w.length := hval p₁ (by simp)
  have hRne : (mid ++ [ptop]) ≠ [] := by simp
  set base := mid.map (fun p => gp w p₁ (p + 1)) with hbase
  have hcfg : encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))
      = PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop]))) (base ++ [gp w p₁ (ptop + 1)]) := by
    rw [show encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))
        = PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop])))
          (encStack w (p₁ :: (mid ++ [ptop]))) from rfl]
    rw [encStack_cons hRne, List.map_append, hbase]
    simp
  have hstep : (sim M).stepCfg (sqOf w)
        (PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop]))) (base ++ [gp w p₁ (ptop + 1)]))
      = some ([], PebbleCfg.conf (q', true, (padLet w p₁, padLet w (p₁ + 1)), Ph.run)
        (base ++ [gp w p₁ (ptop + 1) + 1])) := by
    refine stepCfg_right' ?_
      (by rw [sqOf_length]; exact gp_lt w hp₁ (by omega))
    rw [show (base ++ [gp w p₁ (ptop + 1)]) = encStack w (p₁ :: (mid ++ [ptop])) by
      rw [encStack_cons hRne, List.map_append, hbase]; simp]
    rw [sim_step_eq hval hact, ctxSt_deep hRne,
      show decide (2 ≤ (p₁ :: (mid ++ [ptop])).length) = true from by simp]
    rfl
  have htgt : encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop + 1])))
      = PebbleCfg.conf (q', true, (padLet w p₁, padLet w (p₁ + 1)), Ph.run)
        (base ++ [gp w p₁ (ptop + 1) + 1]) := by
    have hlast : gp w p₁ (ptop + 1 + 1) = gp w p₁ (ptop + 1) + 1 := by
      simp only [gp]
      omega
    rw [show encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop + 1])))
        = PebbleCfg.conf (encSt w q' (p₁ :: (mid ++ [ptop + 1])))
          (encStack w (p₁ :: (mid ++ [ptop + 1]))) from rfl]
    rw [encSt_deep (by simp), encStack_cons (by simp), List.map_append, hbase]
    simp only [List.map_cons, List.map_nil, hlast]
  rw [htgt] at hcont
  rw [hcfg]
  simpa using Pebble.Reaches.step hstep hcont

lemma sim_move_deep_left {q q' : Q} {p₁ ptop : ℕ} {mid : List ℕ}
    (hval : ∀ p ∈ p₁ :: (mid ++ [ptop]), p ≤ w.length) (htop : 0 < ptop)
    (hact : M.step q (viewOf w (p₁ :: (mid ++ [ptop]))) = (q', PebbleAction.move false))
    {v : List B}
    (hcont : (sim M).Reaches (sqOf w)
      (encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop - 1])))) v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))) v
      PebbleCfg.halt := by
  have hRne : (mid ++ [ptop]) ≠ [] := by simp
  set base := mid.map (fun p => gp w p₁ (p + 1)) with hbase
  have hcfg : encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))
      = PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop]))) (base ++ [gp w p₁ (ptop + 1)]) := by
    rw [show encCfg w (PebbleCfg.conf q (p₁ :: (mid ++ [ptop])))
        = PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop])))
          (encStack w (p₁ :: (mid ++ [ptop]))) from rfl]
    rw [encStack_cons hRne, List.map_append, hbase]
    simp
  have hstep : (sim M).stepCfg (sqOf w)
        (PebbleCfg.conf (encSt w q (p₁ :: (mid ++ [ptop]))) (base ++ [gp w p₁ (ptop + 1)]))
      = some ([], PebbleCfg.conf (q', true, (padLet w p₁, padLet w (p₁ + 1)), Ph.run)
        (base ++ [gp w p₁ (ptop + 1) - 1])) := by
    refine stepCfg_left' ?_ (gp_pos w (by omega))
    rw [show (base ++ [gp w p₁ (ptop + 1)]) = encStack w (p₁ :: (mid ++ [ptop])) by
      rw [encStack_cons hRne, List.map_append, hbase]; simp]
    rw [sim_step_eq hval hact, ctxSt_deep hRne,
      show decide (2 ≤ (p₁ :: (mid ++ [ptop])).length) = true from by simp]
    rfl
  have htgt : encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop - 1])))
      = PebbleCfg.conf (q', true, (padLet w p₁, padLet w (p₁ + 1)), Ph.run)
        (base ++ [gp w p₁ (ptop + 1) - 1]) := by
    have hlast : gp w p₁ (ptop - 1 + 1) = gp w p₁ (ptop + 1) - 1 := by
      have h1 : ptop - 1 + 1 = ptop := by omega
      simp only [gp, h1]
      omega
    rw [show encCfg w (PebbleCfg.conf q' (p₁ :: (mid ++ [ptop - 1])))
        = PebbleCfg.conf (encSt w q' (p₁ :: (mid ++ [ptop - 1])))
          (encStack w (p₁ :: (mid ++ [ptop - 1]))) from rfl]
    rw [encSt_deep (by simp), encStack_cons (by simp), List.map_append, hbase]
    simp only [List.map_cons, List.map_nil, hlast]
  rw [htgt] at hcont
  rw [hcfg]
  simpa using Pebble.Reaches.step hstep hcont

end Step

end PebSq

end Lax194892Proofs.Transducers
