/-
The annotation of the input of a two-way transducer by the information needed to
walk backwards along its run.

Fix a two-way transducer `M` over the input alphabet `A` and a deterministic
automaton `D` recognising the language of marked inputs of `TwoWayVisit.lean`.
Every position `j` of the input `w` is annotated with

* the letters `w[j-1]`, `w[j]`, `w[j+1]` (a window of the input),
* the state of `D` after reading the prefix `w[0..j)`,
* the function `s ↦ (D started in s accepts the suffix w[j+1..))`.

From the annotations of the two letters adjacent to a cut one can then decide,
for every state `q` of `M`, whether the run of `M` visits that cut (or either of
the two neighbouring cuts) in the state `q`.  The annotation is computed by a
bimachine -- the prefix automaton is `D`, the suffix automaton computes the
acceptance function of the suffix -- and hence it is a rational function
(Theorem `thm:bimachines`).
-/
import Lax132576Proofs.Source.PartB.Bimachine
import Lax916827Proofs.Source.PartC.TwoWayVisit
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- An annotation letter: a window of three input letters, the state of the
prefix automaton, and the acceptance function of the suffix. -/
abbrev AnnLet (A S : Type) := (Option A × A × Option A) × S × (S → Bool)

namespace AnnLet

variable {A S : Type}

/-- The letter preceding the annotated position. -/
def prev (c : AnnLet A S) : Option A := c.1.1
/-- The annotated letter. -/
def letter (c : AnnLet A S) : A := c.1.2.1
/-- The letter following the annotated position. -/
def next (c : AnnLet A S) : Option A := c.1.2.2
/-- The state of the prefix automaton before the annotated position. -/
def left (c : AnnLet A S) : S := c.2.1
/-- The acceptance function of the suffix after the annotated position. -/
def rho (c : AnnLet A S) : S → Bool := c.2.2

@[simp] lemma prev_mk (p : Option A) (a : A) (n : Option A) (s : S) (f : S → Bool) :
    AnnLet.prev ((p, a, n), s, f) = p := rfl
@[simp] lemma letter_mk (p : Option A) (a : A) (n : Option A) (s : S) (f : S → Bool) :
    AnnLet.letter ((p, a, n), s, f) = a := rfl
@[simp] lemma next_mk (p : Option A) (a : A) (n : Option A) (s : S) (f : S → Bool) :
    AnnLet.next ((p, a, n), s, f) = n := rfl
@[simp] lemma left_mk (p : Option A) (a : A) (n : Option A) (s : S) (f : S → Bool) :
    AnnLet.left ((p, a, n), s, f) = s := rfl
@[simp] lemma rho_mk (p : Option A) (a : A) (n : Option A) (s : S) (f : S → Bool) :
    AnnLet.rho ((p, a, n), s, f) = f := rfl

end AnnLet

namespace TwoWay

open scoped Classical

variable {A B Q S : Type}

/-- The state of `D` after the prefix `x`. -/
def leftSt (D : DFA (Marked A Q) S) (x : List A) : S := D.evalFrom D.start (plainList Q x)

/-- The acceptance function of the suffix `y`. -/
noncomputable def rhoOf (D : DFA (Marked A Q) S) (y : List A) : S → Bool :=
  fun s => decide (D.evalFrom s (plainList Q y) ∈ D.accept)

/-- The annotation of a string, starting from a given state of `D` and a given
preceding letter. -/
noncomputable def annotFrom (D : DFA (Marked A Q) S) (s : S) (p : Option A) :
    List A → List (AnnLet A S)
  | [] => []
  | a :: rest => ((p, a, rest.head?), s, rhoOf D rest) ::
      annotFrom D (D.step s (a, none)) (some a) rest

/-- The annotation of the input string. -/
noncomputable def annot (D : DFA (Marked A Q) S) (w : List A) : List (AnnLet A S) :=
  annotFrom D D.start none w

/-- The letter preceding the position `j`. -/
def prevAt (w : List A) (j : ℕ) : Option A := if j = 0 then none else w[j - 1]?

variable (D : DFA (Marked A Q) S)

lemma annotFrom_length (s : S) (p : Option A) (w : List A) :
    (annotFrom D s p w).length = w.length := by
  induction w generalizing s p with
  | nil => rfl
  | cons a rest ih => simp [annotFrom, ih]

@[simp] lemma annot_length (w : List A) : (annot D w).length = w.length :=
  annotFrom_length D _ _ w

lemma annotFrom_map_letter (s : S) (p : Option A) (w : List A) :
    (annotFrom D s p w).map AnnLet.letter = w := by
  induction w generalizing s p with
  | nil => rfl
  | cons a rest ih => simp [annotFrom, ih]

lemma annot_map_letter (w : List A) : (annot D w).map AnnLet.letter = w :=
  annotFrom_map_letter D _ _ w

lemma annotFrom_getElem (s : S) (p : Option A) (w : List A) {j : ℕ} (hj : j < w.length) :
    (annotFrom D s p w)[j]? = some (((if j = 0 then p else w[j - 1]?), w[j]'hj, w[j + 1]?),
      D.evalFrom s (plainList Q (w.take j)), rhoOf D (w.drop (j + 1))) := by
  induction w generalizing s p j with
  | nil => simp at hj
  | cons a rest ih =>
      cases j with
      | zero =>
          simp [annotFrom, plainList, List.head?_eq_getElem?]
      | succ k =>
          have hk : k < rest.length := by simpa using hj
          have hstep : (annotFrom D s p (a :: rest))[k + 1]? =
              (annotFrom D (D.step s (a, none)) (some a) rest)[k]? := by
            rw [annotFrom]; simp
          rw [hstep, ih (D.step s (a, none)) (some a) hk]
          have h1 : (if k = 0 then some a else rest[k - 1]?) = (a :: rest)[k]? := by
            cases k with
            | zero => simp
            | succ k' => simp
          have h2 : plainList Q ((a :: rest).take (k + 1)) =
              (a, none) :: plainList Q (rest.take k) := by
            simp [plainList]
          simp only [h2, DFA.evalFrom_cons]
          rw [show ((a :: rest)[k + 1 - 1]? : Option A) = (a :: rest)[k]? from rfl, ← h1]
          rfl

lemma annot_getElem (w : List A) {j : ℕ} (hj : j < w.length) :
    (annot D w)[j]? = some ((prevAt w j, w[j]'hj, w[j + 1]?),
      leftSt D (w.take j), rhoOf D (w.drop (j + 1))) := by
  rw [annot, annotFrom_getElem D _ _ w hj]
  rfl

/-! ### Reading off the run from the annotation -/

/-- Whether the run visits, in the state `q`, the cut to the left of the
annotated position. -/
noncomputable def onRunLeft (D : DFA (Marked A Q) S) (c : AnnLet A S) (q : Q) : Bool :=
  c.rho (D.step c.left (c.letter, some (Sum.inl q)))

/-- Whether the run visits, in the state `q`, the cut to the right of the
annotated position. -/
noncomputable def onRunRight (D : DFA (Marked A Q) S) (c : AnnLet A S) (q : Q) : Bool :=
  c.rho (D.step c.left (c.letter, some (Sum.inr q)))

variable (M : TwoWay A B Q)

/-- Evaluating `D` on the input marked at the cut left of the letter `a`. -/
lemma rhoOf_step_inl_iff (hD : D.accepts = {z | (visitAut M).Accepts z})
    (x : List A) (a : A) (y : List A) (q : Q) :
    rhoOf D y (D.step (leftSt D x) (a, some (Sum.inl q))) = true ↔
      Visits M (x ++ a :: y) (Cfg.conf x q (a :: y)) := by
  have hev : D.eval (plainList Q x ++ (a, some (Sum.inl q)) :: plainList Q y)
      = D.evalFrom (D.step (leftSt D x) (a, some (Sum.inl q))) (plainList Q y) := by
    rw [DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_cons]; rfl
  have hr : rhoOf D y (D.step (leftSt D x) (a, some (Sum.inl q)))
      = decide (D.eval (plainList Q x ++ (a, some (Sum.inl q)) :: plainList Q y) ∈ D.accept) := by
    rw [hev]; rfl
  rw [hr, decide_eq_true_iff, ← DFA.mem_accepts, hD,
    visits_iff_accepts_left M x a y q]
  exact Iff.rfl

/-- Evaluating `D` on the input marked at the cut right of the letter `a`. -/
lemma rhoOf_step_inr_iff (hD : D.accepts = {z | (visitAut M).Accepts z})
    (x : List A) (a : A) (y : List A) (q : Q) :
    rhoOf D y (D.step (leftSt D x) (a, some (Sum.inr q))) = true ↔
      Visits M (x ++ a :: y) (Cfg.conf (x ++ [a]) q y) := by
  have hev : D.eval (plainList Q x ++ (a, some (Sum.inr q)) :: plainList Q y)
      = D.evalFrom (D.step (leftSt D x) (a, some (Sum.inr q))) (plainList Q y) := by
    rw [DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_cons]; rfl
  have hr : rhoOf D y (D.step (leftSt D x) (a, some (Sum.inr q)))
      = decide (D.eval (plainList Q x ++ (a, some (Sum.inr q)) :: plainList Q y) ∈ D.accept) := by
    rw [hev]; rfl
  rw [hr, decide_eq_true_iff, ← DFA.mem_accepts, hD,
    visits_iff_accepts_right M x a y q]
  exact Iff.rfl

/-- The annotation letter at position `j`. -/
lemma annot_eq_at (w : List A) {j : ℕ} (hj : j < w.length) {c : AnnLet A S}
    (hc : (annot D w)[j]? = some c) :
    c = ((prevAt w j, w[j]'hj, w[j + 1]?), leftSt D (w.take j), rhoOf D (w.drop (j + 1))) := by
  rw [annot_getElem D w hj] at hc
  exact (Option.some_injective _ hc).symm

/-- The annotation of a position decides which states the run has at the cut to
the left of that position. -/
theorem onRunLeft_iff (hD : D.accepts = {z | (visitAut M).Accepts z}) (w : List A) {j : ℕ}
    (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q : Q) :
    onRunLeft D c q = true ↔ Visits M w (Cfg.conf (w.take j) q (w.drop j)) := by
  rw [annot_eq_at D w hj hc]
  have hdrop : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hj
  show rhoOf D (w.drop (j + 1))
      (D.step (leftSt D (w.take j)) (w[j], some (Sum.inl q))) = true ↔ _
  rw [rhoOf_step_inl_iff D M hD (w.take j) (w[j]'hj) (w.drop (j + 1)) q, ← hdrop,
    List.take_append_drop]

/-- The annotation of a position decides which states the run has at the cut to
the right of that position. -/
theorem onRunRight_iff (hD : D.accepts = {z | (visitAut M).Accepts z}) (w : List A) {j : ℕ}
    (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q : Q) :
    onRunRight D c q = true ↔ Visits M w (Cfg.conf (w.take (j + 1)) q (w.drop (j + 1))) := by
  rw [annot_eq_at D w hj hc]
  have hdrop : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hj
  have htake : w.take (j + 1) = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem hj
  show rhoOf D (w.drop (j + 1))
      (D.step (leftSt D (w.take j)) (w[j], some (Sum.inr q))) = true ↔ _
  rw [rhoOf_step_inr_iff D M hD (w.take j) (w[j]'hj) (w.drop (j + 1)) q, ← htake, ← hdrop,
    List.take_append_drop]

/-! ### Recognising the annotated strings -/

/-- The local consistency condition on two consecutive annotation letters. -/
def LocalOK (D : DFA (Marked A Q) S) : Option (AnnLet A S) → Option (AnnLet A S) → Prop
  | none, none => True
  | none, some c => c.prev = none ∧ c.left = D.start
  | some d, some c => c.prev = some d.letter ∧ d.next = some c.letter ∧
      c.left = D.step d.left (d.letter, none) ∧ ∀ s, d.rho s = c.rho (D.step s (c.letter, none))
  | some d, none => d.next = none ∧ ∀ s, d.rho s = decide (s ∈ D.accept)

/-- The annotation letter preceding a cut. -/
def prevLet (z : List (AnnLet A S)) (i : ℕ) : Option (AnnLet A S) := if i = 0 then none else z[i - 1]?

/-- A string over the annotation alphabet is a correct annotation. -/
def Valid (D : DFA (Marked A Q) S) (z : List (AnnLet A S)) : Prop :=
  ∀ i ≤ z.length, LocalOK D (prevLet z i) z[i]?

lemma leftSt_nil : leftSt D ([] : List A) = D.start := rfl

lemma leftSt_append_one (x : List A) (a : A) :
    leftSt D (x ++ [a]) = D.step (leftSt D x) (a, none) := by
  rw [leftSt, plainList, List.map_append, DFA.evalFrom_of_append]
  rfl

lemma rhoOf_nil (s : S) : rhoOf D ([] : List A) s = decide (s ∈ D.accept) := rfl

lemma rhoOf_cons (a : A) (y : List A) (s : S) :
    rhoOf D (a :: y) s = rhoOf D y (D.step s (a, none)) := rfl

lemma prevLet_zero (z : List (AnnLet A S)) : prevLet z 0 = none := rfl

lemma prevLet_pos {z : List (AnnLet A S)} {i : ℕ} (hi : i ≠ 0) :
    prevLet z i = z[i - 1]? := if_neg hi

theorem valid_annot (w : List A) : Valid D (annot D w) := by
  intro i hi
  rw [annot_length] at hi
  rcases Nat.lt_or_ge i w.length with hlt | hge
  · rw [annot_getElem D w hlt]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [prevLet_zero]
      exact ⟨rfl, rfl⟩
    · have him : i - 1 + 1 = i := by omega
      have hi1 : i - 1 < w.length := by omega
      rw [prevLet_pos (by omega), annot_getElem D w hi1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · show prevAt w i = some (w[i - 1]'hi1)
        rw [prevAt, if_neg (by omega)]
        exact (List.getElem?_eq_getElem hi1)
      · show w[i - 1 + 1]? = some (w[i]'hlt)
        rw [him]
        exact (List.getElem?_eq_getElem hlt)
      · show leftSt D (w.take i) = D.step (leftSt D (w.take (i - 1))) (w[i - 1]'hi1, none)
        rw [← leftSt_append_one, ← List.take_succ_eq_append_getElem hi1, him]
      · intro s
        show rhoOf D (w.drop (i - 1 + 1)) s
            = rhoOf D (w.drop (i + 1)) (D.step s (w[i]'hlt, none))
        rw [him, ← rhoOf_cons, List.drop_eq_getElem_cons hlt]
  · have hieq : i = w.length := le_antisymm hi hge
    subst hieq
    have hnone : (annot D w)[w.length]? = none := by
      apply List.getElem?_eq_none
      rw [annot_length]
    rw [hnone]
    rcases Nat.eq_zero_or_pos w.length with h0 | hpos
    · rw [h0, prevLet_zero]
      trivial
    · have him : w.length - 1 + 1 = w.length := by omega
      have hi1 : w.length - 1 < w.length := by omega
      rw [prevLet_pos (by omega), annot_getElem D w hi1]
      refine ⟨?_, ?_⟩
      · show w[w.length - 1 + 1]? = none
        rw [him]
        exact List.getElem?_eq_none (le_refl _)
      · intro s
        show rhoOf D (w.drop (w.length - 1 + 1)) s = decide (s ∈ D.accept)
        rw [him, List.drop_length]
        rfl

theorem annot_of_valid {z : List (AnnLet A S)} (h : Valid D z) :
    z = annot D (z.map AnnLet.letter) := by
  set w := z.map AnnLet.letter with hw
  have hlen : w.length = z.length := by simp [hw]
  have hlet : ∀ (i : ℕ) (hi : i < z.length), (z[i]'hi).letter = w[i]'(by omega) := by
    intro i hi
    simp [hw]
  -- the `prev` component
  have hprev : ∀ (i : ℕ) (hi : i < z.length), (z[i]'hi).prev = prevAt w i := by
    intro i hi
    have hL := h i (le_of_lt hi)
    rw [List.getElem?_eq_getElem hi] at hL
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [prevLet_zero] at hL
      rw [hL.1, prevAt, if_pos rfl]
    · have hi1 : i - 1 < z.length := by omega
      rw [prevLet_pos (by omega), List.getElem?_eq_getElem hi1] at hL
      rw [hL.1, prevAt, if_neg (by omega), List.getElem?_eq_getElem (by omega : i - 1 < w.length),
        hlet (i - 1) hi1]
  -- the `next` component
  have hnext : ∀ (i : ℕ) (hi : i < z.length), (z[i]'hi).next = w[i + 1]? := by
    intro i hi
    have hL := h (i + 1) (by omega)
    rw [prevLet_pos (by omega)] at hL
    simp only [Nat.add_sub_cancel] at hL
    rw [List.getElem?_eq_getElem hi] at hL
    rcases Nat.lt_or_ge (i + 1) z.length with hlt | hge
    · rw [List.getElem?_eq_getElem hlt] at hL
      rw [hL.2.1, List.getElem?_eq_getElem (by omega : i + 1 < w.length), hlet (i + 1) hlt]
    · have : z[i + 1]? = none := List.getElem?_eq_none hge
      rw [this] at hL
      rw [hL.1, List.getElem?_eq_none (by omega)]
  -- the `left` component, by induction from the left
  have hleft : ∀ (i : ℕ) (hi : i < z.length), (z[i]'hi).left = leftSt D (w.take i) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hL := h 0 (le_of_lt hi)
        rw [prevLet_zero, List.getElem?_eq_getElem hi] at hL
        rw [hL.2, List.take_zero, leftSt_nil]
    | succ k ih =>
        intro hi
        have hk : k < z.length := by omega
        have hL := h (k + 1) (le_of_lt hi)
        rw [prevLet_pos (by omega)] at hL
        simp only [Nat.add_sub_cancel] at hL
        rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hi] at hL
        rw [hL.2.2.1, ih hk, hlet k hk,
          List.take_succ_eq_append_getElem (by omega : k < w.length), leftSt_append_one]
  -- the `rho` component, by induction from the right
  have hrho : ∀ (n i : ℕ) (hi : i < z.length), z.length - i ≤ n →
      (z[i]'hi).rho = rhoOf D (w.drop (i + 1)) := by
    intro n
    induction n with
    | zero => intro i hi hn; omega
    | succ n ih =>
        intro i hi hn
        have hL := h (i + 1) (by omega)
        rw [prevLet_pos (by omega)] at hL
        simp only [Nat.add_sub_cancel] at hL
        rw [List.getElem?_eq_getElem hi] at hL
        rcases Nat.lt_or_ge (i + 1) z.length with hlt | hge
        · rw [List.getElem?_eq_getElem hlt] at hL
          funext s
          rw [hL.2.2.2 s, ih (i + 1) hlt (by omega), hlet (i + 1) hlt, ← rhoOf_cons,
            ← List.drop_eq_getElem_cons (by omega : i + 1 < w.length)]
        · have hz : z[i + 1]? = none := List.getElem?_eq_none hge
          rw [hz] at hL
          funext s
          rw [hL.2 s, List.drop_eq_nil_of_le (by omega), rhoOf_nil]
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i z.length with hlt | hge
  · rw [List.getElem?_eq_getElem hlt, annot_getElem D w (by omega)]
    have : (z[i]'hlt) = ((prevAt w i, w[i]'(by omega), w[i + 1]?),
        leftSt D (w.take i), rhoOf D (w.drop (i + 1))) := by
      apply Prod.ext
      · apply Prod.ext
        · exact hprev i hlt
        · apply Prod.ext
          · exact hlet i hlt
          · exact hnext i hlt
      · apply Prod.ext
        · exact hleft i hlt
        · exact hrho z.length i hlt (by omega)
    rw [this]
  · rw [List.getElem?_eq_none hge, List.getElem?_eq_none (by rw [annot_length]; omega)]

end TwoWay

end Lax916827Proofs.Transducers
