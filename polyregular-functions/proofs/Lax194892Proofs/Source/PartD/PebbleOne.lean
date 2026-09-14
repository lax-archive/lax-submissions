/-
One-pebble automata recognise regular languages.

A one-pebble automaton has two levels: with an empty stack it cannot see the input at all, and
with one pebble on the stack it is a two-way head.  Both levels are collapsed into a single
deterministic two-way automaton:

* the level-0 behaviour is a fixed iteration `lev0Step` on the states, which either loops for
  ever, or terminates the run, or pushes the pebble on the first position of the input;
* at a position of the input, the level-1 behaviour is an iteration `loc1Step` which either loops
  for ever, or terminates the run, or moves the head, or -- after popping and pushing again --
  restarts the head at the first position.

The last outcome is the only one that a two-way automaton cannot perform in one step: it walks
back to the left end of the input in an auxiliary state.  Shepherdson's Theorem
(`TwoDFA.accepts_isRegular`) then gives regularity.
-/
import Lax194892Proofs.Source.PartD.PebbleBisim
import Lax916827Proofs.Source.PartC.TwoDFA
import Lax916827Proofs.Source.PartC.RegAut
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace OnePebble

variable {B R O : Type}

/-- The outcome of the part of a run of a one-pebble automaton that does not move the head. -/
inductive LocOut (O R : Type) : Type
  /-- The run has terminated, with an answer or by dying. -/
  | term : Option O → LocOut O R
  /-- The run will never terminate. -/
  | diverge : LocOut O R
  /-- The head moves, in the given direction and state. -/
  | mv : Bool → R → LocOut O R
  /-- The pebble was popped and pushed again: the head restarts at the left end. -/
  | rew : R → LocOut O R

/-! ## Level 0: the empty stack -/

/-- One step of a run with an empty stack.  This does not depend on the input. -/
def lev0Step (M : PebbleAut B R O 1) : R → (Option O ⊕ R) ⊕ R := fun r =>
  match (M.step r []).2 with
  | PebAutAction.stay => Sum.inr (M.step r []).1
  | PebAutAction.move _ => Sum.inl (Sum.inl none)
  | PebAutAction.push => Sum.inl (Sum.inr (M.step r []).1)
  | PebAutAction.pop => Sum.inl (Sum.inl none)
  | PebAutAction.halt o => Sum.inl (Sum.inl (some o))

/-- The configuration reached when the level-0 iteration terminates. -/
def lev0Lift : (Option O ⊕ R) → PebAutCfg R O
  | Sum.inl x => Sum.inr x
  | Sum.inr r => Sum.inl (r, [0])

open Classical in
/-- The outcome of the level-0 iteration, if there is one. -/
noncomputable def lev0Out (M : PebbleAut B R O 1) : R → Option (Option O ⊕ R) :=
  resolve (lev0Step M)

lemma lev0_next (M : PebbleAut B R O 1) (v : List B) (r : R) :
    M.next v (Sum.inl (r, [])) =
      match lev0Step M r with
      | Sum.inl x => lev0Lift x
      | Sum.inr r' => Sum.inl (r', []) := by
  have hv : viewOf v ([] : List ℕ) = [] := rfl
  simp only [PebbleAut.next, lev0Step, hv]
  cases (M.step r []).2 <;> rfl

lemma lev0_chain (M : PebbleAut B R O 1) (v : List B) (r : R) : ∀ n : ℕ,
    (∃ r', (stayStep (lev0Step M))^[n] (Sum.inr r) = Sum.inr r' ∧
        (M.next v)^[n] (Sum.inl (r, [])) = Sum.inl (r', []))
      ∨ (∃ m x, 1 ≤ m ∧ (stayStep (lev0Step M))^[n] (Sum.inr r) = Sum.inl x ∧
        (M.next v)^[m] (Sum.inl (r, [])) = lev0Lift x) := by
  intro n
  induction n with
  | zero => exact Or.inl ⟨r, rfl, rfl⟩
  | succ n ih =>
      rcases ih with ⟨r', hs, hM⟩ | ⟨m, x, hm, hs, hM⟩
      · have hstep : (stayStep (lev0Step M))^[n + 1] (Sum.inr r) = lev0Step M r' := by
          rw [Function.iterate_succ_apply', hs]
          rfl
        have hMstep : (M.next v)^[n + 1] (Sum.inl (r, [])) = M.next v (Sum.inl (r', [])) := by
          rw [Function.iterate_succ_apply', hM]
        rw [lev0_next] at hMstep
        cases hc : lev0Step M r' with
        | inl x => exact Or.inr ⟨n + 1, x, by omega, by rw [hstep, hc], by rw [hMstep, hc]⟩
        | inr r'' => exact Or.inl ⟨r'', by rw [hstep, hc], by rw [hMstep, hc]⟩
      · exact Or.inr ⟨m, x, hm, by rw [Function.iterate_succ_apply', hs, stayStep_inl], hM⟩

lemma lev0Out_some (M : PebbleAut B R O 1) (v : List B) {r : R} {x : Option O ⊕ R}
    (h : lev0Out M r = some x) :
    ∃ m, 1 ≤ m ∧ (M.next v)^[m] (Sum.inl (r, [])) = lev0Lift x := by
  obtain ⟨n, hn⟩ := resolve_eq_some_iff.1 h
  rcases lev0_chain M v r n with ⟨r', hs, -⟩ | ⟨m, y, hm, hs, hM⟩
  · rw [hn] at hs; exact absurd hs (by simp)
  · rw [hn] at hs
    obtain rfl : x = y := Sum.inl_injective hs
    exact ⟨m, hm, hM⟩

lemma lev0Out_none (M : PebbleAut B R O 1) (v : List B) {r : R} (h : lev0Out M r = none)
    (o : O) : ¬ M.Answers v (Sum.inl (r, [])) o := by
  rintro ⟨n, hn⟩
  rcases lev0_chain M v r n with ⟨r', -, hM⟩ | ⟨m, x, -, hs, -⟩
  · rw [hM] at hn; exact absurd hn (by simp)
  · exact absurd (resolve_eq_some_iff.2 ⟨n, hs⟩) (by rw [← lev0Out, h]; simp)

/-! ## Level 1: one pebble on the stack -/

/-- The letter to the left of the gap `q`. -/
def leftLet (v : List B) (q : ℕ) : Option B := if q = 0 then none else v[q - 1]?

lemma viewOf_singleton (v : List B) (q : ℕ) :
    viewOf v [q] = [((leftLet v q, v[q]?), [true])] := by
  simp [viewOf, leftLet]

lemma leftLet_isSome (v : List B) {q : ℕ} (hq : q ≤ v.length) :
    (leftLet v q).isSome = true ↔ 0 < q := by
  unfold leftLet
  by_cases h : q = 0
  · subst h; simp
  · rw [if_neg h, List.getElem?_eq_getElem (show q - 1 < v.length by omega)]
    simp
    omega

lemma getElem?_isSome (v : List B) {q : ℕ} (hq : q ≤ v.length) :
    (v[q]?).isSome = true ↔ q < v.length := by
  by_cases h : q < v.length
  · rw [List.getElem?_eq_getElem h]; simp [h]
  · rw [List.getElem?_eq_none (by omega)]; simp; omega

lemma next_singleton (M : PebbleAut B R O 1) (v : List B) (q : ℕ) (r : R) :
    M.next v (Sum.inl (r, [q])) =
      (match (M.step r [((leftLet v q, v[q]?), [true])]).2 with
       | PebAutAction.stay => Sum.inl ((M.step r [((leftLet v q, v[q]?), [true])]).1, [q])
       | PebAutAction.halt o => Sum.inr (some o)
       | PebAutAction.push => Sum.inr none
       | PebAutAction.pop => Sum.inl ((M.step r [((leftLet v q, v[q]?), [true])]).1, [])
       | PebAutAction.move d =>
           if d then
             (if q < v.length
              then Sum.inl ((M.step r [((leftLet v q, v[q]?), [true])]).1, [q + 1])
              else Sum.inr none)
           else
             (if 0 < q
              then Sum.inl ((M.step r [((leftLet v q, v[q]?), [true])]).1, [q - 1])
              else Sum.inr none)) := by
  simp only [PebbleAut.next, viewOf_singleton]
  cases (M.step r [((leftLet v q, v[q]?), [true])]).2 with
  | stay => rfl
  | halt o => rfl
  | push => simp
  | pop => simp
  | move d => cases d <;> simp

open Classical in
/-- One step of a run that keeps the pebble at one position. -/
noncomputable def loc1Step (M : PebbleAut B R O 1) (L Rt : Option B) : R → LocOut O R ⊕ R :=
  fun r =>
  match (M.step r [((L, Rt), [true])]).2 with
  | PebAutAction.stay => Sum.inr (M.step r [((L, Rt), [true])]).1
  | PebAutAction.halt o => Sum.inl (LocOut.term (some o))
  | PebAutAction.push => Sum.inl (LocOut.term none)
  | PebAutAction.move d =>
      if d then
        (if Rt.isSome then Sum.inl (LocOut.mv true (M.step r [((L, Rt), [true])]).1)
         else Sum.inl (LocOut.term none))
      else
        (if L.isSome then Sum.inl (LocOut.mv false (M.step r [((L, Rt), [true])]).1)
         else Sum.inl (LocOut.term none))
  | PebAutAction.pop =>
      match lev0Out M (M.step r [((L, Rt), [true])]).1 with
      | none => Sum.inl LocOut.diverge
      | some (Sum.inl x) => Sum.inl (LocOut.term x)
      | some (Sum.inr r'') => if L.isSome then Sum.inl (LocOut.rew r'') else Sum.inr r''

open Classical in
/-- The outcome of the level-1 iteration at one position, if there is one. -/
noncomputable def loc1Res (M : PebbleAut B R O 1) (L Rt : Option B) : R → Option (LocOut O R) :=
  resolve (loc1Step M L Rt)

/-- What an outcome of the level-1 iteration says about the run of the machine. -/
def LocOk (M : PebbleAut B R O 1) (v : List B) (q : ℕ) (r : R) : LocOut O R → Prop
  | LocOut.term x => ∃ m, 1 ≤ m ∧ (M.next v)^[m] (Sum.inl (r, [q])) = Sum.inr x
  | LocOut.diverge => ∀ o, ¬ M.Answers v (Sum.inl (r, [q])) o
  | LocOut.mv d r' => (if d then q < v.length else 0 < q) ∧
      ∃ m, 1 ≤ m ∧ (M.next v)^[m] (Sum.inl (r, [q]))
        = Sum.inl (r', [if d then q + 1 else q - 1])
  | LocOut.rew r' => 0 < q ∧
      ∃ m, 1 ≤ m ∧ (M.next v)^[m] (Sum.inl (r, [q])) = Sum.inl (r', [0])

lemma LocOk_of_prefix (M : PebbleAut B R O 1) (v : List B) (q : ℕ) {r r' : R} {m : ℕ}
    (hm : (M.next v)^[m] (Sum.inl (r, [q])) = Sum.inl (r', [q])) {out : LocOut O R}
    (h : LocOk M v q r' out) : LocOk M v q r out := by
  cases out with
  | term x =>
      obtain ⟨m', hm', h'⟩ := h
      exact ⟨m' + m, by omega, by rw [Function.iterate_add_apply, hm, h']⟩
  | diverge =>
      intro o ho
      have hit := (PebbleAut.answers_iterate m).2 ho
      rw [hm] at hit
      exact h o hit
  | mv d r'' =>
      obtain ⟨hb, m', hm', h'⟩ := h
      exact ⟨hb, m' + m, by omega, by rw [Function.iterate_add_apply, hm, h']⟩
  | rew r'' =>
      obtain ⟨hb, m', hm', h'⟩ := h
      exact ⟨hb, m' + m, by omega, by rw [Function.iterate_add_apply, hm, h']⟩

lemma loc1_step_ok (M : PebbleAut B R O 1) (v : List B) {q : ℕ} (hq : q ≤ v.length) (r : R) :
    (∀ out, loc1Step M (leftLet v q) (v[q]?) r = Sum.inl out → LocOk M v q r out) ∧
      (∀ r'', loc1Step M (leftLet v q) (v[q]?) r = Sum.inr r'' →
        ∃ m, 1 ≤ m ∧ (M.next v)^[m] (Sum.inl (r, [q])) = Sum.inl (r'', [q])) := by
  have hnext := next_singleton M v q r
  rcases hstep : M.step r [((leftLet v q, v[q]?), [true])] with ⟨r1, act⟩
  rw [hstep] at hnext
  simp only [loc1Step, hstep]
  cases act with
  | stay =>
      simp only at hnext ⊢
      refine ⟨fun out hout => absurd hout (by simp), fun r'' hr'' => ?_⟩
      simp only [Sum.inr.injEq] at hr''
      subst hr''
      exact ⟨1, le_refl 1, by rw [Function.iterate_one, hnext]⟩
  | halt o =>
      simp only at hnext ⊢
      refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
      simp only [Sum.inl.injEq] at hout
      subst hout
      exact ⟨1, le_refl 1, by rw [Function.iterate_one, hnext]⟩
  | push =>
      simp only at hnext ⊢
      refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
      simp only [Sum.inl.injEq] at hout
      subst hout
      exact ⟨1, le_refl 1, by rw [Function.iterate_one, hnext]⟩
  | move d =>
      cases d with
      | false =>
          simp only [Bool.false_eq_true, if_false] at hnext ⊢
          by_cases hL : (leftLet v q).isSome = true
          · have hqpos : 0 < q := (leftLet_isSome v hq).1 hL
            rw [if_pos hL]
            rw [if_pos hqpos] at hnext
            refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
            simp only [Sum.inl.injEq] at hout
            subst hout
            refine ⟨by simpa using hqpos, 1, le_refl 1, ?_⟩
            simpa using hnext
          · have hq0 : ¬ 0 < q := fun h => hL ((leftLet_isSome v hq).2 h)
            rw [if_neg hL]
            rw [if_neg hq0] at hnext
            refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
            simp only [Sum.inl.injEq] at hout
            subst hout
            exact ⟨1, le_refl 1, by rw [Function.iterate_one, hnext]⟩
      | true =>
          simp only [if_true] at hnext ⊢
          by_cases hL : (v[q]?).isSome = true
          · have hqlt : q < v.length := (getElem?_isSome v hq).1 hL
            rw [if_pos hL]
            rw [if_pos hqlt] at hnext
            refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
            simp only [Sum.inl.injEq] at hout
            subst hout
            refine ⟨by simpa using hqlt, 1, le_refl 1, ?_⟩
            simpa using hnext
          · have hqlt : ¬ q < v.length := fun h => hL ((getElem?_isSome v hq).2 h)
            rw [if_neg hL]
            rw [if_neg hqlt] at hnext
            refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
            simp only [Sum.inl.injEq] at hout
            subst hout
            exact ⟨1, le_refl 1, by rw [Function.iterate_one, hnext]⟩
  | pop =>
      simp only at hnext ⊢
      cases hl : lev0Out M r1 with
      | none =>
          refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
          simp only [Sum.inl.injEq] at hout
          subst hout
          intro o ho
          rw [PebbleAut.answers_iff_next, hnext] at ho
          exact lev0Out_none M v hl o ho
      | some y =>
          obtain ⟨m', hm', h'⟩ := lev0Out_some M v hl
          cases y with
          | inl x =>
              refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
              simp only [Sum.inl.injEq] at hout
              subst hout
              refine ⟨m' + 1, by omega, ?_⟩
              rw [Function.iterate_succ_apply, hnext]
              exact h'
          | inr r0 =>
              dsimp only
              by_cases hL : (leftLet v q).isSome = true
              · have hqpos : 0 < q := (leftLet_isSome v hq).1 hL
                rw [if_pos hL]
                refine ⟨fun out hout => ?_, fun r'' hr'' => absurd hr'' (by simp)⟩
                simp only [Sum.inl.injEq] at hout
                subst hout
                refine ⟨hqpos, m' + 1, by omega, ?_⟩
                rw [Function.iterate_succ_apply, hnext]
                exact h'
              · have hq0 : q = 0 := by
                  by_contra hc
                  exact hL ((leftLet_isSome v hq).2 (Nat.pos_of_ne_zero hc))
                rw [if_neg hL]
                refine ⟨fun out hout => absurd hout (by simp), fun r'' hr'' => ?_⟩
                simp only [Sum.inr.injEq] at hr''
                subst hr''
                refine ⟨m' + 1, by omega, ?_⟩
                rw [Function.iterate_succ_apply, hnext, hq0]
                exact h'

/-- The whole chain of level-1 steps at one position, matched with the run of the machine. -/
lemma loc1_chain (M : PebbleAut B R O 1) (v : List B) {q : ℕ} (hq : q ≤ v.length) (r : R) :
    ∀ n : ℕ,
      (∃ m r', n ≤ m ∧
          (stayStep (loc1Step M (leftLet v q) (v[q]?)))^[n] (Sum.inr r) = Sum.inr r' ∧
          (M.next v)^[m] (Sum.inl (r, [q])) = Sum.inl (r', [q]))
        ∨ (∃ out, (stayStep (loc1Step M (leftLet v q) (v[q]?)))^[n] (Sum.inr r) = Sum.inl out ∧
          LocOk M v q r out) := by
  intro n
  induction n with
  | zero => exact Or.inl ⟨0, r, le_refl 0, rfl, rfl⟩
  | succ n ih =>
      rcases ih with ⟨m, r', hnm, hs, hM⟩ | ⟨out, hs, hok⟩
      · have hstep : (stayStep (loc1Step M (leftLet v q) (v[q]?)))^[n + 1] (Sum.inr r)
            = loc1Step M (leftLet v q) (v[q]?) r' := by
          rw [Function.iterate_succ_apply', hs]; rfl
        obtain ⟨hinl, hinr⟩ := loc1_step_ok M v hq r'
        cases hc : loc1Step M (leftLet v q) (v[q]?) r' with
        | inl out =>
            exact Or.inr ⟨out, by rw [hstep, hc], LocOk_of_prefix M v q hM (hinl out hc)⟩
        | inr r'' =>
            obtain ⟨m2, hm2, h2⟩ := hinr r'' hc
            refine Or.inl ⟨m2 + m, r'', by omega, by rw [hstep, hc], ?_⟩
            rw [Function.iterate_add_apply, hM, h2]
      · exact Or.inr ⟨out, by rw [Function.iterate_succ_apply', hs, stayStep_inl], hok⟩

lemma loc1Res_some (M : PebbleAut B R O 1) (v : List B) {q : ℕ} (hq : q ≤ v.length) {r : R}
    {out : LocOut O R} (h : loc1Res M (leftLet v q) (v[q]?) r = some out) :
    LocOk M v q r out := by
  obtain ⟨n, hn⟩ := resolve_eq_some_iff.1 h
  rcases loc1_chain M v hq r n with ⟨m, r', -, hs, -⟩ | ⟨out', hs, hok⟩
  · rw [hn] at hs; exact absurd hs (by simp)
  · rw [hn] at hs
    obtain rfl : out = out' := Sum.inl_injective hs
    exact hok

lemma loc1Res_none (M : PebbleAut B R O 1) (v : List B) {q : ℕ} (hq : q ≤ v.length) {r : R}
    (h : loc1Res M (leftLet v q) (v[q]?) r = none) (o : O) :
    ¬ M.Answers v (Sum.inl (r, [q])) o := by
  rintro ⟨n, hn⟩
  rcases loc1_chain M v hq r n with ⟨m, r', hnm, -, hM⟩ | ⟨out, hs, -⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [show n + d = d + n by omega, Function.iterate_add_apply, hn,
      PebbleAut.iterate_next_inr] at hM
    exact absurd hM (by simp)
  · exact absurd (resolve_eq_some_iff.2 ⟨n, hs⟩) (by rw [show resolve (loc1Step M (leftLet v q)
      (v[q]?)) r = loc1Res M (leftLet v q) (v[q]?) r from rfl, h]; simp)

/-! ## The two-way automaton -/

open Classical in
/-- How the two-way automaton reacts to an outcome of the level-1 iteration. -/
noncomputable def handle (o₀ : O) : Option (LocOut O R) → Bool ⊕ ((R ⊕ R) × Bool)
  | none => Sum.inl false
  | some LocOut.diverge => Sum.inl false
  | some (LocOut.term x) => Sum.inl (decide (x = some o₀))
  | some (LocOut.mv d r') => Sum.inr (Sum.inl r', d)
  | some (LocOut.rew r'') => Sum.inr (Sum.inr r'', false)

open Classical in
/-- The two-way automaton simulating a one-pebble automaton.  The states `Sum.inr r` are used to
walk back to the left end of the input after the pebble has been popped and pushed again. -/
noncomputable def twoOf (M : PebbleAut B R O 1) (o₀ : O) (r₀ : R) : TwoDFA B (R ⊕ R) where
  init := Sum.inl r₀
  step L s Rt :=
    match s with
    | Sum.inl r => handle o₀ (loc1Res M L Rt r)
    | Sum.inr r => if L.isSome then Sum.inr (Sum.inr r, false) else handle o₀ (loc1Res M L Rt r)

lemma twoOf_step_eq (M : PebbleAut B R O 1) (o₀ : O) (r₀ : R) (v : List B) {q : ℕ} {s : R ⊕ R}
    {r : R} (hs : s = Sum.inl r ∨ (s = Sum.inr r ∧ q = 0)) :
    (twoOf M o₀ r₀).step (if q = 0 then none else v[q - 1]?) s (v[q]?)
      = handle o₀ (loc1Res M (leftLet v q) (v[q]?) r) := by
  rw [show (if q = 0 then none else v[q - 1]?) = leftLet v q from rfl]
  rcases hs with rfl | ⟨rfl, rfl⟩
  · rfl
  · simp only [twoOf, show leftLet v 0 = (none : Option B) from rfl, Option.isSome_none,
      Bool.false_eq_true, if_false]

/-- Walking back to the left end of the input. -/
lemma twoOf_rewind (M : PebbleAut B R O 1) (o₀ : O) (r₀ : R) (v : List B) (r : R) :
    ∀ p : ℕ, p ≤ v.length →
      ((twoOf M o₀ r₀).next v)^[p] (Sum.inl (p, Sum.inr r)) = Sum.inl (0, Sum.inr r) := by
  intro p
  induction p with
  | zero => intro _; rfl
  | succ p ih =>
      intro hp
      have hL : ((leftLet v (p + 1)).isSome = true) := (leftLet_isSome v hp).2 (by omega)
      have hstep : (twoOf M o₀ r₀).next v (Sum.inl (p + 1, Sum.inr r))
          = Sum.inl (p, Sum.inr r) := by
        have : (twoOf M o₀ r₀).step (if p + 1 = 0 then none else v[p + 1 - 1]?) (Sum.inr r)
            (v[p + 1]?) = Sum.inr (Sum.inr r, false) := by
          rw [show (if p + 1 = 0 then none else v[p + 1 - 1]?) = leftLet v (p + 1) from rfl]
          simp only [twoOf]
          rw [if_pos hL]
        simp only [TwoDFA.next, this]
        rw [if_pos (show 0 < p + 1 by omega)]
        simp
      rw [Function.iterate_succ_apply, hstep]
      exact ih (by omega)

/-! ## The bisimulation -/

private def RelOne (v : List B) :
    TwoCfg (R ⊕ R) → PebAutCfg R O → Prop := fun c d =>
  ∃ (q : ℕ) (r : R) (s : R ⊕ R), q ≤ v.length ∧ d = Sum.inl (r, [q]) ∧ c = Sum.inl (q, s) ∧
    (s = Sum.inl r ∨ (s = Sum.inr r ∧ q = 0))

private lemma two_acc_iff_of_halt {S : Type} {N : TwoDFA B S} {v : List B} {p : ℕ} {s : S}
    {b : Bool} (h : N.next v (Sum.inl (p, s)) = Sum.inr b) :
    (∃ n, (N.next v)^[n] (Sum.inl (p, s)) = Sum.inr true) ↔ b = true := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp at hn
    | succ n =>
        rw [Function.iterate_succ_apply, h, TwoDFA.iterate_next_inr] at hn
        exact Sum.inr_injective hn
  · rintro rfl
    exact ⟨1, by rw [Function.iterate_one, h]⟩

private lemma peb_ans_iff_of_halt {M : PebbleAut B R O 1} {v : List B} {c : PebAutCfg R O}
    {z : Option O} {m : ℕ} (hm : (M.next v)^[m] c = Sum.inr z) (o₀ : O) :
    (∃ n, (M.next v)^[n] c = Sum.inr (some o₀)) ↔ z = some o₀ := by
  constructor
  · rintro ⟨n, hn⟩
    rcases le_total m n with hle | hle
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [show m + d = d + m by omega, Function.iterate_add_apply, hm,
        PebbleAut.iterate_next_inr] at hn
      exact Sum.inr_injective hn
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [show n + d = d + n by omega, Function.iterate_add_apply, hn,
        PebbleAut.iterate_next_inr] at hm
      exact (Sum.inr_injective hm).symm
  · rintro rfl
    exact ⟨m, hm⟩

private lemma twoOf_bisim_step (M : PebbleAut B R O 1) (o₀ : O) (r₀ : R) (v : List B)
    (x : TwoCfg (R ⊕ R)) (y : PebAutCfg R O) (hxy : RelOne v x y) :
    ∃ j m, 1 ≤ j ∧ 1 ≤ m ∧
      (RelOne v (((twoOf M o₀ r₀).next v)^[j] x) ((M.next v)^[m] y) ∨
        ((∃ n, ((twoOf M o₀ r₀).next v)^[n] x = Sum.inr true)
          ↔ (∃ n, (M.next v)^[n] y = Sum.inr (some o₀)))) := by
  classical
  obtain ⟨q, r, s, hq, rfl, rfl, hs⟩ := hxy
  rcases hres : loc1Res M (leftLet v q) (v[q]?) r with _ | out
  · have hnx : (twoOf M o₀ r₀).next v (Sum.inl (q, s)) = Sum.inr false := by
      simp only [TwoDFA.next, twoOf_step_eq M o₀ r₀ v hs, hres, handle]
    refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
    rw [two_acc_iff_of_halt hnx]
    simp only [Bool.false_eq_true, false_iff]
    exact fun h => loc1Res_none M v hq hres o₀ h
  · have hok := loc1Res_some M v hq hres
    cases out with
    | term z =>
        have hnx : (twoOf M o₀ r₀).next v (Sum.inl (q, s)) = Sum.inr (decide (z = some o₀)) := by
          simp only [TwoDFA.next, twoOf_step_eq M o₀ r₀ v hs, hres, handle]
        obtain ⟨m, hm1, hm⟩ := hok
        refine ⟨1, m, le_refl 1, hm1, Or.inr ?_⟩
        rw [two_acc_iff_of_halt hnx, peb_ans_iff_of_halt hm o₀]
        simp
    | diverge =>
        have hnx : (twoOf M o₀ r₀).next v (Sum.inl (q, s)) = Sum.inr false := by
          simp only [TwoDFA.next, twoOf_step_eq M o₀ r₀ v hs, hres, handle]
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
        rw [two_acc_iff_of_halt hnx]
        simp only [Bool.false_eq_true, false_iff]
        exact fun h => hok o₀ h
    | mv d r' =>
        obtain ⟨hguard, m, hm1, hm⟩ := hok
        cases d with
        | true =>
            have hlt : q < v.length := hguard
            have hnx : (twoOf M o₀ r₀).next v (Sum.inl (q, s))
                = Sum.inl (q + 1, Sum.inl r') := by
              simp only [TwoDFA.next, twoOf_step_eq M o₀ r₀ v hs, hres, handle]
              rw [if_pos hlt]
            refine ⟨1, m, le_refl 1, hm1, Or.inl ?_⟩
            rw [Function.iterate_one, hnx]
            exact ⟨q + 1, r', Sum.inl r', by omega, hm, rfl, Or.inl rfl⟩
        | false =>
            have hlt : 0 < q := hguard
            have hnx : (twoOf M o₀ r₀).next v (Sum.inl (q, s))
                = Sum.inl (q - 1, Sum.inl r') := by
              simp only [TwoDFA.next, twoOf_step_eq M o₀ r₀ v hs, hres, handle]
              rw [if_pos hlt]
            refine ⟨1, m, le_refl 1, hm1, Or.inl ?_⟩
            rw [Function.iterate_one, hnx]
            exact ⟨q - 1, r', Sum.inl r', by omega, hm, rfl, Or.inl rfl⟩
    | rew r'' =>
        obtain ⟨hqpos, m, hm1, hm⟩ := hok
        have hnx : (twoOf M o₀ r₀).next v (Sum.inl (q, s))
            = Sum.inl (q - 1, Sum.inr r'') := by
          simp only [TwoDFA.next, twoOf_step_eq M o₀ r₀ v hs, hres, handle]
          rw [if_pos hqpos]
        have hj : ((twoOf M o₀ r₀).next v)^[q] (Sum.inl (q, s)) = Sum.inl (0, Sum.inr r'') := by
          obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
          rw [Function.iterate_succ_apply, hnx]
          simpa using twoOf_rewind M o₀ r₀ v r'' p (by omega)
        refine ⟨q, m, hqpos, hm1, Or.inl ?_⟩
        rw [hj, hm]
        exact ⟨0, r'', Sum.inr r'', Nat.zero_le _, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

/-- The two-way automaton accepts exactly the inputs on which the one-pebble automaton, started
with its pebble on the first position, answers `o₀`. -/
lemma twoOf_accepts_iff (M : PebbleAut B R O 1) (o₀ : O) (r₀ : R) (v : List B) :
    (twoOf M o₀ r₀).Accepts v ↔ M.Answers v (Sum.inl (r₀, [0])) o₀ := by
  refine bisim_acc_iff ((twoOf M o₀ r₀).next v) (M.next v)
    (fun c => c = Sum.inr true) (fun d => d = Sum.inr (some o₀)) ?_ ?_ (RelOne v) ?_ ?_
    (twoOf_bisim_step M o₀ r₀ v) (Sum.inl (0, Sum.inl r₀)) (Sum.inl (r₀, [0]))
    ⟨0, r₀, Sum.inl r₀, Nat.zero_le _, rfl, rfl, Or.inl rfl⟩
  · rintro x rfl; rfl
  · rintro y rfl; rfl
  · rintro x y ⟨q, r, t, -, -, rfl, -⟩; simp
  · rintro x y ⟨q, r, t, -, rfl, -, -⟩; simp

/-! ## Regularity -/

/-- A one-pebble automaton recognises a regular language. -/
theorem onePebble_isRegular [Finite B] [Finite R] [Finite O] (M : PebbleAut B R O 1)
    (r₀ : R) (o₀ : O) :
    Language.IsRegular {v : List B | M.Answers v (Sum.inl (r₀, [])) o₀} := by
  classical
  have hempty : Language.IsRegular (∅ : Set (List B)) := by
    have h := RegAut.isRegular_foldl (Γ := B) (fun (_ : Unit) _ => ()) () ∅
    simpa using h
  rcases hl : lev0Out M r₀ with _ | y
  · have hset : {v : List B | M.Answers v (Sum.inl (r₀, [])) o₀} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact lev0Out_none M v hl o₀
    rw [hset]; exact hempty
  · cases y with
    | inl z =>
        by_cases hz : z = some o₀
        · have hset : {v : List B | M.Answers v (Sum.inl (r₀, [])) o₀} = Set.univ := by
            ext v
            simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
            obtain ⟨m, -, hm⟩ := lev0Out_some M v hl
            exact (peb_ans_iff_of_halt (show (M.next v)^[m] (Sum.inl (r₀, [])) = Sum.inr z
              from hm) o₀).2 hz
          rw [hset]; exact RegAut.isRegular_univ
        · have hset : {v : List B | M.Answers v (Sum.inl (r₀, [])) o₀} = ∅ := by
            ext v
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            intro h
            obtain ⟨m, -, hm⟩ := lev0Out_some M v hl
            exact hz ((peb_ans_iff_of_halt (show (M.next v)^[m] (Sum.inl (r₀, [])) = Sum.inr z
              from hm) o₀).1 h)
          rw [hset]; exact hempty
    | inr r'' =>
        have hset : {v : List B | M.Answers v (Sum.inl (r₀, [])) o₀}
            = {v : List B | (twoOf M o₀ r'').Accepts v} := by
          ext v
          simp only [Set.mem_setOf_eq]
          rw [twoOf_accepts_iff]
          obtain ⟨m, -, hm⟩ := lev0Out_some M v hl
          have hm' : (M.next v)^[m] (Sum.inl (r₀, [])) = Sum.inl (r'', [0]) := hm
          rw [← hm']
          exact (PebbleAut.answers_iterate m).symm
        rw [hset]
        exact TwoDFA.accepts_isRegular _


end OnePebble

end Lax194892Proofs.Transducers
