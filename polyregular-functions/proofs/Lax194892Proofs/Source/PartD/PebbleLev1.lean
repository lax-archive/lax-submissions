/-
Pebble automata recognise regular languages.

The proof is an induction on the number `k` of pebbles.

* With no pebble at all the machine cannot see the input, so its language is empty or full.
* A `(k + 1)`-pebble automaton `N` is simulated by a *one-pebble* automaton `lev1 N` running on
  the input annotated, at every gap, with the gap data of `RequestProject/PartD/PebbleAnn.lean`:
  the only step of `N` that `lev1 N` cannot mirror is the one that covers the bottom pebble with
  a second pebble, and the outcome of the run above the bottom pebble is exactly what the gap
  data records.  By the induction hypothesis the gap data is computed by a bimachine, so the
  annotation is continuous, and one-pebble automata recognise regular languages by
  `RequestProject/PartD/PebbleOne.lean`.
-/
import Lax194892Proofs.Source.PartD.PebbleOne
import Lax194892Proofs.Source.PartD.PebbleAnn
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

variable {A R O : Type} {k : ℕ}

/-! ## No pebble at all -/

/-- With an empty stack the run of a `0`-pebble automaton does not depend on the input. -/
lemma pebbleAut_zero_iterate (N : PebbleAut A R O 0) (w w' : List A) :
    ∀ (n : ℕ) (r : R),
      (N.next w)^[n] (Sum.inl (r, [])) = (N.next w')^[n] (Sum.inl (r, [])) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro r
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        PebbleAut.next_nil N w r, PebbleAut.next_nil N w' r]
      cases hact : (N.step r []).2 with
      | stay => exact ih (N.step r []).1
      | halt o => simp
      | push => simp
      | pop => simp
      | move d => simp

/-- A `0`-pebble automaton recognises a regular language (indeed the empty or the full one). -/
theorem pebbleAut_zero_isRegular (N : PebbleAut A R O 0) (r : R) (o : O) :
    Language.IsRegular {w : List A | N.Answers w (Sum.inl (r, [])) o} := by
  classical
  by_cases h : N.Answers ([] : List A) (Sum.inl (r, [])) o
  · have hset : {w : List A | N.Answers w (Sum.inl (r, [])) o} = Set.univ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by rw [pebbleAut_zero_iterate N w [] n r]; exact hn⟩
    rw [hset]; exact RegAut.isRegular_univ
  · have hset : {w : List A | N.Answers w (Sum.inl (r, [])) o} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨n, hn⟩
      exact h ⟨n, by rw [pebbleAut_zero_iterate N [] w n r]; exact hn⟩
    rw [hset]
    have hz := RegAut.isRegular_foldl (Γ := A) (fun (_ : Unit) _ => ()) () ∅
    simpa using hz

/-! ## The one-pebble automaton over the annotated alphabet -/

/-- The two letters of the original input that are adjacent to a gap, read off the two annotated
letters that are adjacent to the corresponding position. -/
def annC (L Rt : Option (Option A × GapData A R O)) : Option A × Option A :=
  (L.bind Prod.fst, Rt.bind Prod.fst)

/-- The gap data carried by the annotated letter to the right of the head. -/
def gdOf : Option (Option A × GapData A R O) → GapData A R O
  | none => fun _ _ => none
  | some (_, gd) => gd

/-- The action of the simulating one-pebble automaton at level 1.  All the actions of the
simulated machine are mirrored, except that

* a move to the right is refused when the original input has no letter there (the annotated word
  is one letter longer than the input), and
* covering the bottom pebble is replaced by consulting the gap data. -/
def lev1Act (r' : R) (a : PebAutAction O) (c : Option A × Option A) (g : GapData A R O) :
    R × PebAutAction O :=
  match a with
  | PebAutAction.stay => (r', PebAutAction.stay)
  | PebAutAction.halt o => (r', PebAutAction.halt o)
  | PebAutAction.pop => (r', PebAutAction.pop)
  | PebAutAction.move d =>
      if d then
        (if c.2.isSome then (r', PebAutAction.move true) else (r', PebAutAction.push))
      else (r', PebAutAction.move false)
  | PebAutAction.push =>
      match g c r' with
      | none => (r', PebAutAction.push)
      | some (Sum.inl o) => (r', PebAutAction.halt o)
      | some (Sum.inr r₂) => (r₂, PebAutAction.stay)

/-- The one-pebble automaton over the annotated alphabet that simulates a `(k+1)`-pebble
automaton. -/
def lev1 (N : PebbleAut A R O (k + 1)) : PebbleAut (Option A × GapData A R O) R O 1 where
  step r view :=
    match view with
    | [] => N.step r []
    | [((L, Rt), _)] =>
        lev1Act (N.step r [(annC L Rt, [true])]).1 (N.step r [(annC L Rt, [true])]).2
          (annC L Rt) (gdOf Rt)
    | _ => (r, PebAutAction.push)

/-! ## The simulation -/

/-- The configurations of the simulating and the simulated machine agree, and the stack is a
legal one. -/
private def RelL (w : List A) : PebAutCfg R O → PebAutCfg R O → Prop := fun x y =>
  (∃ r, x = Sum.inl (r, []) ∧ y = Sum.inl (r, []))
    ∨ (∃ r p, p ≤ w.length ∧ x = Sum.inl (r, [p]) ∧ y = Sum.inl (r, [p]))

private lemma halt1 {A' R' O' : Type} {k' : ℕ} {N : PebbleAut A' R' O' k'} {w : List A'}
    {c : PebAutCfg R' O'} {z : Option O'} (h : N.next w c = Sum.inr z) (o₀ : O') :
    (∃ n, (N.next w)^[n] c = Sum.inr (some o₀)) ↔ z = some o₀ :=
  PebbleAut.exists_iterate_iff_of_halt (m := 1) (by rw [Function.iterate_one]; exact h) o₀

private lemma lev1_bisim_step (N : PebbleAut A R O (k + 1)) (w : List A)
    (ann : List (Option A × GapData A R O))
    (hget : ∀ i, i ≤ w.length → ann[i]? = some (w[i]?, gapVal N (markSplit w i)))
    (hlen : ann.length = w.length + 1) (o₀ : O)
    (x y : PebAutCfg R O) (hxy : RelL w x y) :
    ∃ j m, 1 ≤ j ∧ 1 ≤ m ∧
      (RelL w (((lev1 N).next ann)^[j] x) ((N.next w)^[m] y) ∨
        ((∃ n, ((lev1 N).next ann)^[n] x = Sum.inr (some o₀))
          ↔ (∃ n, (N.next w)^[n] y = Sum.inr (some o₀)))) := by
  rcases hxy with ⟨r, rfl, rfl⟩ | ⟨r, p, hp, rfl, rfl⟩
  · -- the stack is empty: the two machines have the same behaviour
    have hA := PebbleAut.next_nil (lev1 N) ann r
    have hB := PebbleAut.next_nil N w r
    rw [show (lev1 N).step r [] = N.step r [] from rfl] at hA
    cases hact : (N.step r []).2 with
    | stay =>
        rw [hact] at hA hB
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inl ?_⟩
        rw [Function.iterate_one, Function.iterate_one, hA, hB]
        exact Or.inl ⟨(N.step r []).1, rfl, rfl⟩
    | halt o =>
        rw [hact] at hA hB
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
        rw [halt1 hA o₀, halt1 hB o₀]
    | push =>
        rw [hact] at hA hB
        rw [if_pos (show (0 : ℕ) < 1 by omega)] at hA
        rw [if_pos (show (0 : ℕ) < k + 1 by omega)] at hB
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inl ?_⟩
        rw [Function.iterate_one, Function.iterate_one, hA, hB]
        exact Or.inr ⟨(N.step r []).1, 0, Nat.zero_le _, rfl, rfl⟩
    | pop =>
        rw [hact] at hA hB
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
        rw [halt1 hA o₀, halt1 hB o₀]
    | move d =>
        rw [hact] at hA hB
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
        rw [halt1 hA o₀, halt1 hB o₀]
  · -- one pebble on the stack, at the gap `p` of the input
    have hRt : ann[p]? = some (w[p]?, gapVal N (markSplit w p)) := hget p hp
    have hview : viewOf ann [p]
        = [(((if p = 0 then none else ann[p - 1]?), ann[p]?), [true])] := by
      simp only [viewOf, List.map_cons, List.map_nil, decide_true]
    have hc : annC (if p = 0 then none else ann[p - 1]?) (ann[p]?) = cOf w p := by
      rw [hRt]
      by_cases h0 : p = 0
      · subst h0; simp [annC, cOf]
      · rw [if_neg h0, hget (p - 1) (by omega)]
        simp [annC, cOf, h0]
    have hg : gdOf (ann[p]?) = gapVal N (markSplit w p) := by rw [hRt]; rfl
    have hvw : viewOf w [p] = [(cOf w p, [true])] := by
      simp only [viewOf, cOf, List.map_cons, List.map_nil, decide_true]
    have hstep1 : (lev1 N).step r (viewOf ann [p])
        = lev1Act (N.step r [(cOf w p, [true])]).1 (N.step r [(cOf w p, [true])]).2
            (cOf w p) (gapVal N (markSplit w p)) := by
      rw [hview, ← hc, ← hg]
      rfl
    have hA := PebbleAut.next_single (lev1 N) ann p r
    have hB := PebbleAut.next_single N w p r
    rw [hstep1] at hA
    rw [hvw] at hB
    cases hact : (N.step r [(cOf w p, [true])]).2 with
    | stay =>
        rw [hact] at hB
        simp only [hact, lev1Act] at hA
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inl ?_⟩
        rw [Function.iterate_one, Function.iterate_one, hA, hB]
        exact Or.inr ⟨(N.step r [(cOf w p, [true])]).1, p, hp, rfl, rfl⟩
    | halt o =>
        rw [hact] at hB
        simp only [hact, lev1Act] at hA
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
        rw [halt1 hA o₀, halt1 hB o₀]
    | pop =>
        rw [hact] at hB
        simp only [hact, lev1Act] at hA
        refine ⟨1, 1, le_refl 1, le_refl 1, Or.inl ?_⟩
        rw [Function.iterate_one, Function.iterate_one, hA, hB]
        exact Or.inl ⟨(N.step r [(cOf w p, [true])]).1, rfl, rfl⟩
    | move d =>
        rw [hact] at hB
        simp only [hact, lev1Act] at hA
        cases d with
        | false =>
            simp only [Bool.false_eq_true, if_false] at hA hB
            by_cases hpos : 0 < p
            · rw [if_pos hpos] at hA hB
              refine ⟨1, 1, le_refl 1, le_refl 1, Or.inl ?_⟩
              rw [Function.iterate_one, Function.iterate_one, hA, hB]
              exact Or.inr ⟨(N.step r [(cOf w p, [true])]).1, p - 1, by omega, rfl, rfl⟩
            · rw [if_neg hpos] at hA hB
              refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
              rw [halt1 hA o₀, halt1 hB o₀]
        | true =>
            simp only [if_true] at hA hB
            have hiff : ((cOf w p).2).isSome = true ↔ p < w.length := by
              simp only [cOf]
              by_cases hlt : p < w.length
              · rw [List.getElem?_eq_getElem hlt]; simp [hlt]
              · rw [List.getElem?_eq_none (by omega)]; simp; omega
            by_cases hlt : p < w.length
            · rw [if_pos (hiff.2 hlt)] at hA
              rw [if_pos (show p < ann.length by omega)] at hA
              rw [if_pos hlt] at hB
              refine ⟨1, 1, le_refl 1, le_refl 1, Or.inl ?_⟩
              rw [Function.iterate_one, Function.iterate_one, hA, hB]
              exact Or.inr ⟨(N.step r [(cOf w p, [true])]).1, p + 1, by omega, rfl, rfl⟩
            · rw [if_neg (fun hh => hlt (hiff.1 hh))] at hA
              rw [if_neg (show ¬ (1 < 1) by omega)] at hA
              rw [if_neg hlt] at hB
              refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
              rw [halt1 hA o₀, halt1 hB o₀]
    | push =>
        have hpush : N.step r (viewOf w [p]) = ((N.step r [(cOf w p, [true])]).1,
            PebAutAction.push) := by
          rw [hvw, ← hact]
        set r₁ := (N.step r [(cOf w p, [true])]).1 with hr₁
        simp only [hact, lev1Act] at hA
        rcases hgap : gapVal N (markSplit w p) (cOf w p) r₁ with _ | z
        · -- the sub-machine has no answer: both machines fail
          rw [hgap] at hA
          rw [if_neg (show ¬ (1 < 1) by omega)] at hA
          refine ⟨1, 1, le_refl 1, le_refl 1, Or.inr ?_⟩
          rw [halt1 hA o₀]
          simp only [reduceCtorEq, false_iff]
          refine sub_no_answer N hp hpush ?_ o₀
          intro xx hxx
          have := PebbleAut.answerOf_eq_none_iff.1 hgap xx
          exact this hxx
        · have hans : (subAut N (cOf w p) r₁).Answers (markSplit w p) (Sum.inl (none, [])) z :=
            PebbleAut.answerOf_eq_some_iff.1 hgap
          cases z with
          | inl o =>
              rw [hgap] at hA
              obtain ⟨m, hm1, hm⟩ := sub_answers_inl N hp hpush hans
              refine ⟨1, m, le_refl 1, hm1, Or.inr ?_⟩
              rw [halt1 hA o₀, PebbleAut.exists_iterate_iff_of_halt hm o₀]
          | inr r₂ =>
              rw [hgap] at hA
              obtain ⟨m, hm1, hm⟩ := sub_answers_inr N hp hpush hans
              refine ⟨1, m, le_refl 1, hm1, Or.inl ?_⟩
              rw [Function.iterate_one, hA, hm]
              exact Or.inr ⟨r₂, p, hp, rfl, rfl⟩

/-- The simulating one-pebble automaton answers exactly as the simulated machine. -/
lemma lev1_answers_iff (N : PebbleAut A R O (k + 1)) (w : List A)
    (ann : List (Option A × GapData A R O))
    (hget : ∀ i, i ≤ w.length → ann[i]? = some (w[i]?, gapVal N (markSplit w i)))
    (hlen : ann.length = w.length + 1) (r₀ : R) (o₀ : O) :
    (lev1 N).Answers ann (Sum.inl (r₀, [])) o₀ ↔ N.Answers w (Sum.inl (r₀, [])) o₀ := by
  refine bisim_acc_iff ((lev1 N).next ann) (N.next w)
    (fun c => c = Sum.inr (some o₀)) (fun d => d = Sum.inr (some o₀)) ?_ ?_ (RelL w) ?_ ?_
    (lev1_bisim_step N w ann hget hlen o₀) (Sum.inl (r₀, [])) (Sum.inl (r₀, []))
    (Or.inl ⟨r₀, rfl, rfl⟩)
  · rintro x rfl; rfl
  · rintro y rfl; rfl
  · rintro x y (⟨r, rfl, -⟩ | ⟨r, p, -, rfl, -⟩) <;> simp
  · rintro x y (⟨r, -, rfl⟩ | ⟨r, p, -, -, rfl⟩) <;> simp

/-! ## The induction -/

/-- The inductive step: if the languages of `k`-pebble automata are regular, then so are the
languages of `(k+1)`-pebble automata. -/
theorem pebbleAut_succ_isRegular {k : ℕ}
    (ih : ∀ {A' R' O' : Type} [Finite A'] [Finite R'] [Finite O'] (N : PebbleAut A' R' O' k)
      (r : R') (o : O'), Language.IsRegular {w : List A' | N.Answers w (Sum.inl (r, [])) o})
    {A R O : Type} [Finite A] [Finite R] [Finite O] (N : PebbleAut A R O (k + 1))
    (r₀ : R) (o₀ : O) :
    Language.IsRegular {w : List A | N.Answers w (Sum.inl (r₀, [])) o₀} := by
  classical
  have hreg : ∀ (c : Option A × Option A) (r₁ : R) (x : O ⊕ R),
      Language.IsRegular
        {u : List (A ⊕ A) | (subAut N c r₁).Answers u (Sum.inl (none, [])) x} :=
    fun c r₁ x => ih (subAut N c r₁) none x
  obtain ⟨ann, hcont, hann⟩ := exists_annotation N hreg
  have hlen : ∀ w : List A, (ann w).length = w.length + 1 := by
    intro w; rw [hann w]; simp
  have hget : ∀ (w : List A) (i : ℕ), i ≤ w.length →
      (ann w)[i]? = some (w[i]?, gapVal N (markSplit w i)) := by
    intro w i hi
    rw [hann w, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  haveI : Finite (Option A × GapData A R O) := inferInstance
  have hone : Language.IsRegular
      {v : List (Option A × GapData A R O) | (lev1 N).Answers v (Sum.inl (r₀, [])) o₀} :=
    OnePebble.onePebble_isRegular (lev1 N) r₀ o₀
  have hpre := hcont _ hone
  have hset : {w : List A | N.Answers w (Sum.inl (r₀, [])) o₀}
      = {w : List A | ann w ∈
          {v : List (Option A × GapData A R O) | (lev1 N).Answers v (Sum.inl (r₀, [])) o₀}} := by
    ext w
    simp only [Set.mem_setOf_eq]
    exact (lev1_answers_iff N w (ann w) (hget w) (hlen w) r₀ o₀).symm
  rw [hset]
  exact hpre

/-- **Pebble automata recognise regular languages.** -/
theorem pebbleAut_answers_isRegular : ∀ (k : ℕ) {A R O : Type} [Finite A] [Finite R] [Finite O]
    (N : PebbleAut A R O k) (r : R) (o : O),
    Language.IsRegular {w : List A | N.Answers w (Sum.inl (r, [])) o} := by
  intro k
  induction k with
  | zero => intro A R O _ _ _ N r o; exact pebbleAut_zero_isRegular N r o
  | succ k ih => intro A R O _ _ _ N r o; exact pebbleAut_succ_isRegular ih N r o

end Lax194892Proofs.Transducers
