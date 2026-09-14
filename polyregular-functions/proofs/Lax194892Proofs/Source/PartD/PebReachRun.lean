/-
**The run of the checking automaton** of `RequestProject/PartD/PebReachAut.lean`.

The four phases of the automaton are analysed one after the other, and the analysis is put together
in `PebReach.reachAut_answers_iff`: on the string representation of a pair of configurations, the
automaton answers `true` exactly when the source reaches the target by a run that never pops below
the floor `ℓ`.
-/
import Lax194892Proofs.Source.PartD.PebReachAut
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebbleAut

variable {A R O : Type} {k : ℕ}

/-- Answering is invariant along the run. -/
lemma answers_iterate_eq {N : PebbleAut A R O k} {w : List A} {c c' : PebAutCfg R O} {m : ℕ}
    (h : (N.next w)^[m] c = c') {o : O} : N.Answers w c o ↔ N.Answers w c' o := by
  rw [← h]
  exact (answers_iterate m).symm

end PebbleAut

namespace PebReach

open PebEnc

variable {A B Q : Type} {k : ℕ}

/-! ## The states of the four phases -/

/-- The state of the sweeping phase. -/
def sweepSt (S T : Fin k → Bool) (q : Q) : RSt Q k :=
  { phase := Phase.sweep, S := S, T := T, q := q }

/-- The state of the returning phase. -/
def backSt (S T : Fin k → Bool) (q : Q) : RSt Q k :=
  { phase := Phase.back, S := S, T := T, q := q }

/-- The state of the placing phase. -/
def placeSt (S T : Fin k → Bool) (q : Q) (i : Fin (k + 1)) : RSt Q k :=
  { phase := Phase.place i, S := S, T := T, q := q }

/-- A dead state. -/
def deadSt (S T : Fin k → Bool) (q : Q) : RSt Q k :=
  { phase := Phase.dead, S := S, T := T, q := q }

/-! ## Reading the view of a stack -/

variable {Γ : Type}

lemma rightLet_viewOf_gen (u : List Γ) (st : List ℕ) :
    rightLet (viewOf u st) = (st.getLast?).bind fun p => u[p]? := by
  simp only [rightLet, viewOf, List.getLast?_map]
  cases st.getLast? <;> rfl

lemma rightLet_viewOf (u : List Γ) (base : List ℕ) (p : ℕ) :
    rightLet (viewOf u (base ++ [p])) = u[p]? := by
  simp [rightLet, viewOf, List.getLast?_map]

lemma leftLet_viewOf (u : List Γ) (base : List ℕ) (p : ℕ) :
    leftLet (viewOf u (base ++ [p])) = if p = 0 then none else u[p - 1]? := by
  simp only [leftLet, viewOf, List.getLast?_map]
  cases p <;> simp

lemma entryRight_viewOf (u : List Γ) (st : List ℕ) (j : ℕ) :
    entryRight (viewOf u st) j = (st[j]?).bind fun p => u[p]? := by
  simp only [entryRight, viewOf, List.getElem?_map]
  cases st[j]? <;> rfl

@[simp] lemma viewOf_length (u : List Γ) (st : List ℕ) : (viewOf u st).length = st.length := by
  simp [viewOf]

/-! ## The pebble indices occurring in a range of gaps -/

/-- The pebble indices of `st` that sit in one of the `d` gaps starting at `p`. -/
def annFrom (k : ℕ) (st : List ℕ) : ℕ → ℕ → Fin k → Bool
  | 0, _ => fun _ => false
  | d + 1, p => fun i => ann k st p i || annFrom k st d (p + 1) i

@[simp] lemma annFrom_zero (st : List ℕ) (p : ℕ) : annFrom k st 0 p = fun _ => false := rfl

lemma annFrom_succ (st : List ℕ) (d p : ℕ) (i : Fin k) :
    annFrom k st (d + 1) p i = (ann k st p i || annFrom k st d (p + 1) i) := rfl

lemma annFrom_spec (st : List ℕ) : ∀ (d p : ℕ) (i : Fin k),
    annFrom k st d p i = true ↔ ∃ j, p ≤ j ∧ j < p + d ∧ st[(i : ℕ)]? = some j := by
  intro d
  induction d with
  | zero =>
      intro p i
      simp only [annFrom_zero, Bool.false_eq_true, false_iff, not_exists]
      intro j
      omega
  | succ d ih =>
      intro p i
      rw [annFrom_succ, Bool.or_eq_true, ih]
      constructor
      · rintro (h | ⟨j, hj1, hj2, hj3⟩)
        · exact ⟨p, le_rfl, by omega, by simpa [ann] using h⟩
        · exact ⟨j, by omega, by omega, hj3⟩
      · rintro ⟨j, hj1, hj2, hj3⟩
        rcases eq_or_lt_of_le hj1 with rfl | hlt
        · exact Or.inl (by simp [ann, hj3])
        · exact Or.inr ⟨j, hlt, by omega, hj3⟩

/-- After the sweep, the collected indices are exactly the indices of the stack. -/
lemma annFrom_full (st : List ℕ) (n : ℕ) (h : ∀ p ∈ st, p ≤ n) (i : Fin k) :
    annFrom k st (n + 1) 0 i = decide ((i : ℕ) < st.length) := by
  rw [Bool.eq_iff_iff, annFrom_spec, decide_eq_true_eq]
  constructor
  · rintro ⟨j, -, -, hj⟩
    exact (List.getElem?_eq_some_iff.1 hj).1
  · intro hlt
    exact ⟨st[(i : ℕ)], Nat.zero_le _, by
      have := h _ (List.getElem_mem hlt); omega, by simp [List.getElem?_eq_getElem hlt]⟩

/-! ## The four phases of the run -/

lemma iter_trans {α : Type} {f : α → α} {a b c : α} {m n : ℕ}
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[n + m] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

section Run

variable (M : Pebble A B Q k) (ℓ : ℕ) (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A)

lemma rightLet_enc {p : ℕ} (hp : p ≤ w.length) :
    rightLet (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) [p])
      = some (q₁, q₂, w[p]?, ann k sts p, ann k stt p) := by
  have h := rightLet_viewOf (pairEnc (k := k) q₁ q₂ sts stt w) [] p
  simp only [List.nil_append] at h
  rw [h, pairEnc_getElem? q₁ q₂ sts stt w hp]

lemma rightLet_enc_gen {base : List ℕ} {p : ℕ} (hp : p ≤ w.length) :
    rightLet (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) (base ++ [p]))
      = some (q₁, q₂, w[p]?, ann k sts p, ann k stt p) := by
  rw [rightLet_viewOf, pairEnc_getElem? q₁ q₂ sts stt w hp]

lemma rightLet_enc_none {p : ℕ} (hp : w.length < p) :
    rightLet (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) [p]) = none := by
  have h := rightLet_viewOf (pairEnc (k := k) q₁ q₂ sts stt w) [] p
  simp only [List.nil_append] at h
  rw [h, pairEnc_getElem?_of_gt q₁ q₂ sts stt w hp]

/-- The first step: the pebble used by the preliminary phases is pushed. -/
lemma next_start :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (startSt q₁, []))
      = Sum.inl (sweepSt (fun _ => false) (fun _ => false) q₁, [0]) := by
  simp [PebbleAut.next, reachAut, rstep, startSt, sweepSt]

/-- A step of the sweep, at a gap of the input string. -/
lemma next_sweep_step (S T : Fin k → Bool) {p : ℕ} (hp : p ≤ w.length) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (sweepSt S T q₁, [p]))
      = Sum.inl (sweepSt (fun i => S i || ann k sts p i) (fun i => T i || ann k stt p i) q₁,
          [p + 1]) := by
  simp [PebbleAut.next, reachAut, rstep, sweepSt, rightLet_enc q₁ q₂ sts stt w hp]
  omega

/-- The last step of the sweep: the head has left the encoded string. -/
lemma next_sweep_end (S T : Fin k → Bool) {p : ℕ} (hp : w.length < p) (hp0 : 0 < p) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (sweepSt S T q₁, [p]))
      = Sum.inl (backSt S T q₁, [p - 1]) := by
  simp [PebbleAut.next, reachAut, rstep, sweepSt, backSt,
    rightLet_enc_none q₁ q₂ sts stt w hp, hp0]

/-- **The sweeping phase.** -/
lemma sweep_run : ∀ (d p : ℕ) (S T : Fin k → Bool), p + d = w.length + 1 →
    ∃ m, ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[m]
        (Sum.inl (sweepSt S T q₁, [p]))
      = Sum.inl (backSt (fun i => S i || annFrom k sts d p i)
          (fun i => T i || annFrom k stt d p i) q₁, [w.length]) := by
  intro d
  induction d with
  | zero =>
      intro p S T hpd
      refine ⟨1, ?_⟩
      rw [Function.iterate_one,
        next_sweep_end M ℓ q₁ q₂ sts stt w S T (by omega) (by omega)]
      have h1 : (fun i => S i || annFrom k sts 0 p i) = S := by funext i; simp
      have h2 : (fun i => T i || annFrom k stt 0 p i) = T := by funext i; simp
      rw [h1, h2, show p - 1 = w.length by omega]
  | succ d ih =>
      intro p S T hpd
      obtain ⟨m, hm⟩ := ih (p + 1) (fun i => S i || ann k sts p i)
        (fun i => T i || ann k stt p i) (by omega)
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply,
        next_sweep_step M ℓ q₁ q₂ sts stt w S T (by omega), hm]
      have hgen : ∀ (X : Fin k → Bool) (st : List ℕ),
          (fun i => (X i || ann k st p i) || annFrom k st d (p + 1) i)
            = fun i => X i || annFrom k st (d + 1) p i := by
        intro X st
        funext i
        rw [annFrom_succ, Bool.or_assoc]
      rw [hgen, hgen]

/-- A step of the return to the first gap. -/
lemma next_back_step (S T : Fin k → Bool) {p : ℕ} (hp0 : 0 < p) (hp : p ≤ w.length + 1) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (backSt S T q₁, [p]))
      = Sum.inl (backSt S T q₁, [p - 1]) := by
  have hl : leftLet (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) [p])
      = some (q₁, q₂, w[p - 1]?, ann k sts (p - 1), ann k stt (p - 1)) := by
    have h := leftLet_viewOf (pairEnc (k := k) q₁ q₂ sts stt w) [] p
    simp only [List.nil_append] at h
    rw [h, if_neg (by omega), pairEnc_getElem? q₁ q₂ sts stt w (by omega)]
  simp [PebbleAut.next, reachAut, rstep, backSt, hl, hp0]

/-- **The returning phase.** -/
lemma back_run (S T : Fin k → Bool) :
    ∀ p : ℕ, p ≤ w.length + 1 →
      ∃ m, ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[m]
          (Sum.inl (backSt S T q₁, [p])) = Sum.inl (backSt S T q₁, [0]) := by
  intro p
  induction p with
  | zero => intro _; exact ⟨0, rfl⟩
  | succ p ih =>
      intro hp
      obtain ⟨m, hm⟩ := ih (by omega)
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply,
        next_back_step M ℓ q₁ q₂ sts stt w S T (by omega) hp]
      simpa using hm

/-! ### The placing phase -/

lemma bidx_hmark (st : List ℕ) (j : ℕ) (hk : st.length ≤ k) :
    bidx (hmark k st) j = decide (j < st.length) := by
  unfold bidx hmark
  split_ifs with h
  · simp
  · symm
    simp only [decide_eq_false_iff_not]
    omega

lemma bidx_ann (st : List ℕ) (p j : ℕ) (hj : j < k) :
    bidx (ann k st p) j = decide (st[j]? = some p) := by
  simp [bidx, ann, hj]

/-- A step of the placing phase: the marker has not been found yet. -/
lemma next_place_move (S T : Fin k → Bool) (i : Fin (k + 1)) (base : List ℕ) {p : ℕ}
    (hp : p ≤ w.length) (hne : bidx (ann k sts p) (i : ℕ) = false) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (placeSt S T q₁ i, base ++ [p]))
      = Sum.inl (placeSt S T q₁ i, base ++ [p + 1]) := by
  simp [PebbleAut.next, reachAut, rstep, placeSt,
    rightLet_enc_gen q₁ q₂ sts stt w hp, hne]
  omega

/-- A step of the placing phase: the marker has been found and there is a further pebble. -/
lemma next_place_push (S T : Fin k → Bool) (i : Fin (k + 1)) (base : List ℕ) {p : ℕ}
    (hp : p ≤ w.length) (heq : bidx (ann k sts p) (i : ℕ) = true)
    (hS : bidx S ((i : ℕ) + 1) = true) (hlen : base.length + 1 < k + 1) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (placeSt S T q₁ i, base ++ [p]))
      = Sum.inl (placeSt S T q₁ (succIdx i), base ++ [p, 0]) := by
  simp [PebbleAut.next, reachAut, rstep, placeSt,
    rightLet_enc_gen q₁ q₂ sts stt w hp, heq, hS, hlen]

/-- The last step of the placing phase: the whole source stack has been placed. -/
lemma next_place_done (S T : Fin k → Bool) (i : Fin (k + 1)) (base : List ℕ) {p : ℕ}
    (hp : p ≤ w.length) (heq : bidx (ann k sts p) (i : ℕ) = true)
    (hS : bidx S ((i : ℕ) + 1) = false) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (placeSt S T q₁ i, base ++ [p]))
      = Sum.inl (simSt S T q₁, base ++ [p]) := by
  simp [PebbleAut.next, reachAut, rstep, placeSt, simSt,
    rightLet_enc_gen q₁ q₂ sts stt w hp, heq, hS]

/-- Walking right to the gap that carries the marker of the pebble being placed. -/
lemma place_walk (S T : Fin k → Bool) (i : Fin (k + 1)) (base : List ℕ) {P : ℕ}
    (hP : P ≤ w.length) (hik : (i : ℕ) < k) (hget : sts[(i : ℕ)]? = some P) :
    ∀ (d p : ℕ), p + d = P →
      ∃ m, ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[m]
          (Sum.inl (placeSt S T q₁ i, base ++ [p])) = Sum.inl (placeSt S T q₁ i, base ++ [P]) := by
  intro d
  induction d with
  | zero => intro p hpd; exact ⟨0, by simp [show p = P by omega]⟩
  | succ d ih =>
      intro p hpd
      obtain ⟨m, hm⟩ := ih (p + 1) (by omega)
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply,
        next_place_move M ℓ q₁ q₂ sts stt w S T i base (by omega)
          (by rw [bidx_ann sts p _ hik, hget]; simp; omega), hm]

/-- **The placing phase.**  Having placed the pebbles below `i`, the automaton places the pebble
`i` and all the pebbles above it, and enters the simulation with the source stack. -/
lemma place_all (T : Fin k → Bool) (hstsb : ∀ p ∈ sts, p ≤ w.length) (hk : sts.length ≤ k) :
    ∀ (r : ℕ) (i : Fin (k + 1)), (i : ℕ) + r + 1 = sts.length →
      ∃ m, ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[m]
          (Sum.inl (placeSt (hmark k sts) T q₁ i, sts.take (i : ℕ) ++ [0]))
        = Sum.inl (simSt (hmark k sts) T q₁, sts) := by
  intro r
  induction r with
  | zero =>
      intro i hi
      have hik : (i : ℕ) < sts.length := by omega
      have hget : sts[(i : ℕ)]? = some sts[(i : ℕ)] := List.getElem?_eq_getElem hik
      have hP : sts[(i : ℕ)] ≤ w.length := hstsb _ (List.getElem_mem hik)
      obtain ⟨m, hm⟩ := place_walk M ℓ q₁ q₂ sts stt w (hmark k sts) T i (sts.take (i : ℕ))
        hP (by omega) hget sts[(i : ℕ)] 0 (by omega)
      refine ⟨1 + m, iter_trans hm ?_⟩
      rw [Function.iterate_one,
        next_place_done M ℓ q₁ q₂ sts stt w (hmark k sts) T i (sts.take (i : ℕ)) hP
          (by rw [bidx_ann sts _ _ (by omega), hget]; simp)
          (by rw [bidx_hmark sts _ hk]; simp; omega)]
      have : sts.take (i : ℕ) ++ [sts[(i : ℕ)]] = sts := by
        rw [show ([sts[(i : ℕ)]] : List ℕ) = (sts[(i : ℕ)]?).toList by rw [hget]; rfl,
          ← List.take_add_one, show (i : ℕ) + 1 = sts.length by omega, List.take_length]
      rw [this]
  | succ r ih =>
      intro i hi
      have hik : (i : ℕ) < sts.length := by omega
      have hget : sts[(i : ℕ)]? = some sts[(i : ℕ)] := List.getElem?_eq_getElem hik
      have hP : sts[(i : ℕ)] ≤ w.length := hstsb _ (List.getElem_mem hik)
      obtain ⟨m, hm⟩ := place_walk M ℓ q₁ q₂ sts stt w (hmark k sts) T i (sts.take (i : ℕ))
        hP (by omega) hget sts[(i : ℕ)] 0 (by omega)
      have hsucc : ((succIdx i : Fin (k + 1)) : ℕ) = (i : ℕ) + 1 := by
        simp only [succIdx]
        omega
      obtain ⟨m', hm'⟩ := ih (succIdx i) (by rw [hsucc]; omega)
      have hbase : sts.take (i : ℕ) ++ [sts[(i : ℕ)], 0]
          = sts.take ((succIdx i : Fin (k + 1)) : ℕ) ++ [0] := by
        rw [hsucc, show ([sts[(i : ℕ)], 0] : List ℕ) = [sts[(i : ℕ)]] ++ [0] from rfl,
          ← List.append_assoc,
          show sts.take (i : ℕ) ++ [sts[(i : ℕ)]] = sts.take ((i : ℕ) + 1) by
            rw [show ([sts[(i : ℕ)]] : List ℕ) = (sts[(i : ℕ)]?).toList by rw [hget]; rfl,
              ← List.take_add_one]]
      have hstep : ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[1]
          (Sum.inl (placeSt (hmark k sts) T q₁ i, sts.take (i : ℕ) ++ [sts[(i : ℕ)]]))
          = Sum.inl (placeSt (hmark k sts) T q₁ (succIdx i),
              sts.take ((succIdx i : Fin (k + 1)) : ℕ) ++ [0]) := by
        rw [Function.iterate_one,
          next_place_push M ℓ q₁ q₂ sts stt w (hmark k sts) T i (sts.take (i : ℕ)) hP
            (by rw [bidx_ann sts _ _ (by omega), hget]; simp)
            (by rw [bidx_hmark sts _ hk]; simp; omega)
            (by rw [List.length_take]; omega), hbase]
      exact ⟨m' + 1 + m, iter_trans hm (iter_trans hstep hm')⟩

/-! ### Putting the preliminary phases together -/

lemma leftLet_enc_zero :
    leftLet (viewOf (pairEnc (k := k) q₁ q₂ sts stt w) [0]) = none := by
  have h := leftLet_viewOf (pairEnc (k := k) q₁ q₂ sts stt w) [] 0
  simp only [List.nil_append] at h
  rw [h]
  simp

/-- At the first gap with no source pebble left to place, the auxiliary pebble is popped and the
simulation starts with the empty stack. -/
lemma next_back_zero_pop (S T : Fin k → Bool) (hS : bidx S 0 = false) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (backSt S T q₁, [0]))
      = Sum.inl (simSt S T q₁, []) := by
  simp [PebbleAut.next, reachAut, rstep, backSt, simSt,
    leftLet_enc_zero q₁ q₂ sts stt w, hS]

/-- At the first gap, the auxiliary pebble becomes the bottom pebble of the source stack. -/
lemma next_back_zero_place (S T : Fin k → Bool) (hS : bidx S 0 = true) :
    (reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w) (Sum.inl (backSt S T q₁, [0]))
      = Sum.inl (placeSt S T q₁ ⟨0, Nat.succ_pos k⟩, [0]) := by
  simp [PebbleAut.next, reachAut, rstep, backSt, placeSt,
    leftLet_enc_zero q₁ q₂ sts stt w, hS]

/-- **The preliminary phases.**  From its initial configuration the automaton reaches the
configuration in which it simulates `M` from the source configuration. -/
lemma pre_run (hstsb : ∀ p ∈ sts, p ≤ w.length) (hsttb : ∀ p ∈ stt, p ≤ w.length)
    (hk : sts.length ≤ k) :
    ∃ m, ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[m] (Sum.inl (startSt q₁, []))
      = Sum.inl (simSt (hmark k sts) (hmark k stt) q₁, sts) := by
  have h0 : ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[1]
      (Sum.inl (startSt q₁, [])) = Sum.inl (sweepSt (fun _ => false) (fun _ => false) q₁, [0]) := by
    rw [Function.iterate_one, next_start]
  obtain ⟨m1, hm1⟩ := sweep_run M ℓ q₁ q₂ sts stt w (w.length + 1) 0
    (fun _ => false) (fun _ => false) (by omega)
  have hS : (fun i => (false || annFrom k sts (w.length + 1) 0 i)) = hmark k sts := by
    funext i
    rw [Bool.false_or, annFrom_full sts w.length hstsb i]
    rfl
  have hT : (fun i => (false || annFrom k stt (w.length + 1) 0 i)) = hmark k stt := by
    funext i
    rw [Bool.false_or, annFrom_full stt w.length hsttb i]
    rfl
  rw [hS, hT] at hm1
  obtain ⟨m2, hm2⟩ := back_run M ℓ q₁ q₂ sts stt w (hmark k sts) (hmark k stt) w.length (by omega)
  by_cases hnil : sts = []
  · subst hnil
    refine ⟨1 + m2 + m1 + 1, iter_trans h0 (iter_trans hm1 (iter_trans hm2 ?_))⟩
    rw [Function.iterate_one,
      next_back_zero_pop M ℓ q₁ q₂ [] stt w (hmark k []) (hmark k stt)
        (by rw [bidx_hmark [] 0 (by simp)]; simp)]
  · have hpos : 0 < sts.length := List.length_pos_iff.2 hnil
    obtain ⟨m3, hm3⟩ := place_all M ℓ q₁ q₂ sts stt w (hmark k stt) hstsb hk
      (sts.length - 1) ⟨0, Nat.succ_pos k⟩ (by simp; omega)
    have hm3' : ((reachAut M ℓ q₁ q₂).next (pairEnc q₁ q₂ sts stt w))^[m3]
        (Sum.inl (placeSt (hmark k sts) (hmark k stt) q₁ ⟨0, Nat.succ_pos k⟩, [0]))
        = Sum.inl (simSt (hmark k sts) (hmark k stt) q₁, sts) := by simpa using hm3
    refine ⟨m3 + 1 + m2 + m1 + 1, iter_trans h0 (iter_trans hm1 (iter_trans hm2
      (iter_trans (m := 1) ?_ hm3')))⟩
    rw [Function.iterate_one,
      next_back_zero_place M ℓ q₁ q₂ sts stt w (hmark k sts) (hmark k stt)
        (by rw [bidx_hmark sts 0 hk]; simp; omega)]

/-! ### The simulation phase -/

/-- A dead run stays dead. -/
lemma next_dead (u : List (PairLetter A Q k)) (s : RSt Q k) (hs : s.phase = Phase.dead)
    (st : List ℕ) : (reachAut M ℓ q₁ q₂).next u (Sum.inl (s, st)) = Sum.inl (s, st) := by
  simp [PebbleAut.next, reachAut, rstep, hs]

lemma not_answers_dead (u : List (PairLetter A Q k)) (s : RSt Q k) (hs : s.phase = Phase.dead)
    (st : List ℕ) (o : Bool) : ¬ (reachAut M ℓ q₁ q₂).Answers u (Sum.inl (s, st)) o := by
  have hiter : ∀ n, ((reachAut M ℓ q₁ q₂).next u)^[n] (Sum.inl (s, st)) = Sum.inl (s, st) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply, next_dead M ℓ q₁ q₂ u s hs, ih]
  rintro ⟨n, hn⟩
  rw [hiter n] at hn
  exact absurd hn (by simp)

/-- The step of the transducer keeps the pebbles inside the input string and the stack inside its
bound. -/
lemma stepCfg_inv {q q' : Q} {st st' : List ℕ} {o : List B} (hst : ∀ p ∈ st, p ≤ w.length)
    (hstk : st.length ≤ k)
    (hs : M.stepCfg w (PebbleCfg.conf q st) = some (o, PebbleCfg.conf q' st')) :
    (∀ p ∈ st', p ≤ w.length) ∧ st'.length ≤ k := by
  cases hact : (M.step q (viewOf w st)).2 with
  | out b =>
      rw [Pebble.stepCfg, hact] at hs
      simp only [Option.some.injEq, Prod.mk.injEq, PebbleCfg.conf.injEq] at hs
      obtain ⟨-, -, rfl⟩ := hs
      exact ⟨hst, hstk⟩
  | terminate =>
      rw [Pebble.stepCfg, hact] at hs
      simp at hs
  | push =>
      rw [Pebble.stepCfg, hact] at hs
      by_cases hlt : st.length < k
      · rw [if_pos hlt] at hs
        simp only [Option.some.injEq, Prod.mk.injEq, PebbleCfg.conf.injEq] at hs
        obtain ⟨-, -, rfl⟩ := hs
        refine ⟨?_, by simp; omega⟩
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hst p hp
        · simp at hp; omega
      · rw [if_neg hlt] at hs; simp at hs
  | pop =>
      rw [Pebble.stepCfg, hact] at hs
      by_cases hnil : st = []
      · rw [if_pos hnil] at hs; simp at hs
      · rw [if_neg hnil] at hs
        simp only [Option.some.injEq, Prod.mk.injEq, PebbleCfg.conf.injEq] at hs
        obtain ⟨-, -, rfl⟩ := hs
        exact ⟨fun p hp => hst p (List.dropLast_subset _ hp), le_trans (by simp) hstk⟩
  | move d =>
      rw [Pebble.stepCfg, hact] at hs
      cases hlast : st.getLast? with
      | none => simp [hlast] at hs
      | some p =>
          have hpst : p ∈ st := List.mem_of_getLast? hlast
          have hne : st ≠ [] := by
            intro h; rw [h] at hlast; simp at hlast
          have hlen : st.dropLast.length + 1 = st.length := by
            rw [List.length_dropLast]
            have : 0 < st.length := List.length_pos_iff.2 hne
            omega
          cases d with
          | true =>
              by_cases hp : p < w.length
              · simp only [hlast, hp, if_true, Option.some.injEq, Prod.mk.injEq,
                  PebbleCfg.conf.injEq] at hs
                obtain ⟨-, -, rfl⟩ := hs
                refine ⟨?_, by simp; omega⟩
                intro x hx
                rcases List.mem_append.1 hx with hx | hx
                · exact hst x (List.dropLast_subset _ hx)
                · simp at hx; omega
              · simp [hlast, hp] at hs
          | false =>
              by_cases hp : 0 < p
              · simp only [hlast, hp, if_true] at hs
                obtain ⟨-, -, rfl⟩ := hs
                refine ⟨?_, by simp; omega⟩
                intro x hx
                rcases List.mem_append.1 hx with hx | hx
                · exact hst x (List.dropLast_subset _ hx)
                · simp at hx
                  have := hst p hpst
                  omega
              · simp [hlast, hp] at hs

end Run

end PebReach

end Lax194892Proofs.Transducers
