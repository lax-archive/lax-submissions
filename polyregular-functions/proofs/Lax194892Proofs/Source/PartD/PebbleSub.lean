/-
The sub-machine of a pebble automaton: what happens above the bottom pebble.

Fix a `(k+1)`-pebble automaton `N` over `A`.  While the bottom pebble sits at the gap `p` of the
input `w`, the machine only ever moves the pebbles above it, and what it sees is determined by

* the two letters adjacent to `p` (a constant `c` of the run), and
* the input string with the gap `p` marked.

The marked string is the string `markSplit w p` over the alphabet `A ⊕ A`, in which the letters
before the gap are tagged `Sum.inl` and the letters after it are tagged `Sum.inr`; a pebble sits at
the marked gap exactly when its left neighbour is tagged `Sum.inl` (or missing) and its right
neighbour is tagged `Sum.inr` (or missing).  Consequently the part of a run of `N` that lies above
the bottom pebble is a run of a `k`-pebble automaton `subAut N c r₁` over `A ⊕ A`, which answers

* `Sum.inl o` if `N` halts with the answer `o`, and
* `Sum.inr r` if the bottom pebble is uncovered again, in the state `r`.

This file constructs that automaton and proves the step-by-step correspondence.
-/
import Lax194892Proofs.Source.PartD.PebbleAut
import Lax916827Proofs.Source.PartC.TwoDFA
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-! ## Marking a gap of the input -/

/-- Forget the mark. -/
def unmark {A : Type} : A ⊕ A → A := Sum.elim id id

/-- The input string with the gap `p` marked: the letters before the gap are tagged `Sum.inl`,
those after it are tagged `Sum.inr`. -/
def markSplit {A : Type} (w : List A) (p : ℕ) : List (A ⊕ A) :=
  (w.take p).map Sum.inl ++ (w.drop p).map Sum.inr

/-- The pair of letters adjacent to the gap `p` of `w`. -/
def cOf {A : Type} (w : List A) (p : ℕ) : Option A × Option A :=
  ((if p = 0 then none else w[p - 1]?), w[p]?)

variable {A : Type}

@[simp] lemma markSplit_length (w : List A) (p : ℕ) : (markSplit w p).length = w.length := by
  simp only [markSplit, List.length_append, List.length_map, List.length_take, List.length_drop]
  omega

lemma markSplit_getElem? {w : List A} {p : ℕ} (hp : p ≤ w.length) (q : ℕ) :
    (markSplit w p)[q]? = if q < p then (w[q]?).map Sum.inl else (w[q]?).map Sum.inr := by
  have hlen : ((w.take p).map (Sum.inl : A → A ⊕ A)).length = p := by
    rw [List.length_map, List.length_take]; omega
  unfold markSplit
  split_ifs with h
  · rw [List.getElem?_append_left (by omega)]
    simp [List.getElem?_take_of_lt h]
  · rw [List.getElem?_append_right (by omega), hlen]
    simp only [List.getElem?_map, List.getElem?_drop]
    congr 2
    omega

lemma markSplit_map_unmark {w : List A} {p : ℕ} (hp : p ≤ w.length) (q : ℕ) :
    ((markSplit w p)[q]?).map unmark = w[q]? := by
  rw [markSplit_getElem? hp]
  split_ifs <;> cases w[q]? <;> simp [unmark]

/-- Is the left neighbour of a pebble on the left-hand side of the marked gap? -/
def leftOk : Option (A ⊕ A) → Bool
  | none => true
  | some (Sum.inl _) => true
  | some (Sum.inr _) => false

/-- Is the right neighbour of a pebble on the right-hand side of the marked gap? -/
def rightOk : Option (A ⊕ A) → Bool
  | none => true
  | some (Sum.inr _) => true
  | some (Sum.inl _) => false

/-- Is a pebble at the marked gap?  This is visible from its two adjacent letters. -/
def atMark (e : Option (A ⊕ A) × Option (A ⊕ A)) : Bool := leftOk e.1 && rightOk e.2

lemma atMark_eq {w : List A} {p : ℕ} (hp : p ≤ w.length) {q : ℕ} (hq : q ≤ w.length) :
    atMark ((if q = 0 then none else (markSplit w p)[q - 1]?), (markSplit w p)[q]?)
      = decide (q = p) := by
  have hleft : leftOk (if q = 0 then none else (markSplit w p)[q - 1]?) = decide (q ≤ p) := by
    by_cases hq0 : q = 0
    · subst hq0; simp [leftOk]
    · rw [if_neg hq0, markSplit_getElem? hp,
        List.getElem?_eq_getElem (show q - 1 < w.length by omega)]
      by_cases hlt : q - 1 < p
      · rw [if_pos hlt]
        show true = _
        rw [eq_comm, decide_eq_true_eq]
        omega
      · rw [if_neg hlt]
        show false = _
        rw [eq_comm, decide_eq_false_iff_not, not_le]
        omega
  have hright : rightOk ((markSplit w p)[q]?) = decide (p ≤ q) := by
    rw [markSplit_getElem? hp]
    by_cases hqn : q < w.length
    · rw [List.getElem?_eq_getElem hqn]
      by_cases hlt : q < p
      · rw [if_pos hlt]
        show false = _
        rw [eq_comm, decide_eq_false_iff_not, not_le]
        omega
      · rw [if_neg hlt]
        show true = _
        rw [eq_comm, decide_eq_true_eq]
        omega
    · rw [List.getElem?_eq_none (show w.length ≤ q by omega),
        decide_eq_true (show p ≤ q by omega)]
      split_ifs <;> rfl
  rw [atMark, hleft, hright]
  by_cases hqp : q = p
  · subst hqp; simp
  · rw [decide_eq_false hqp]
    rcases Nat.lt_or_ge q p with h | h
    · rw [decide_eq_false (show ¬ (p ≤ q) by omega)]; simp
    · rw [decide_eq_false (show ¬ (q ≤ p) by omega)]; simp

/-! ## The sub-machine -/

variable {R O : Type} {k : ℕ}

/-- The action of the sub-machine that corresponds to an action of the whole machine. -/
def subAct {O R : Type} : PebAutAction O → PebAutAction (O ⊕ R)
  | PebAutAction.stay => PebAutAction.stay
  | PebAutAction.move d => PebAutAction.move d
  | PebAutAction.push => PebAutAction.push
  | PebAutAction.pop => PebAutAction.pop
  | PebAutAction.halt o => PebAutAction.halt (Sum.inl o)

/-- The view of the whole machine, reconstructed from the view of the pebbles above the bottom
one: the bottom pebble is prepended, with its (constant) adjacent letters `c`, and the marks are
stripped from the letters. -/
def liftView (c : Option A × Option A) (v : PebbleView (A ⊕ A)) : PebbleView A :=
  (c, true :: v.map (fun e => atMark e.1)) ::
    v.map (fun e => (((e.1.1).map unmark, (e.1.2).map unmark), atMark e.1 :: e.2))

lemma liftView_viewOf {w : List A} {p : ℕ} (hp : p ≤ w.length) {st : List ℕ}
    (hst : ∀ q ∈ st, q ≤ w.length) :
    liftView (cOf w p) (viewOf (markSplit w p) st) = viewOf w (p :: st) := by
  have key : ∀ q ∈ st, atMark ((if q = 0 then none else (markSplit w p)[q - 1]?),
      (markSplit w p)[q]?) = decide (q = p) := fun q hq => atMark_eq hp (hst q hq)
  have hhead : (List.map (fun e => atMark e.1) (viewOf (markSplit w p) st))
      = st.map (fun q => decide (q = p)) := by
    simp only [viewOf, List.map_map, Function.comp_def]
    exact List.map_congr_left key
  simp only [liftView, viewOf, List.map_map, List.map_cons, Function.comp_def, cOf] at *
  refine congrArg₂ List.cons ?_ ?_
  · exact congrArg (fun l => ((if p = 0 then none else w[p - 1]?, w[p]?), true :: l)) hhead
  · refine List.map_congr_left ?_
    intro q hq
    have h1 := markSplit_map_unmark hp q
    have h2 := markSplit_map_unmark (w := w) (p := p) hp (q - 1)
    have h3 := key q hq
    by_cases hq0 : q = 0
    · subst hq0
      rw [h1, h3]
      simp [eq_comm]
    · rw [if_neg hq0, if_neg hq0] at *
      rw [h1, h2, h3]
      simp [eq_comm]

/-- The `k`-pebble automaton over `A ⊕ A` describing what a `(k+1)`-pebble automaton does above
its bottom pebble, entered in the state `r₁`.  It answers `Sum.inl o` if the whole machine halts
with the answer `o`, and `Sum.inr r` if the bottom pebble is uncovered again in the state `r`. -/
def subAut (N : PebbleAut A R O (k + 1)) (c : Option A × Option A) (r₁ : R) :
    PebbleAut (A ⊕ A) (Option R) (O ⊕ R) k where
  step := fun s v =>
    match s, v with
    | none, _ => (some r₁, PebAutAction.push)
    | some r, [] => (some r, PebAutAction.halt (Sum.inr r))
    | some r, e :: v' =>
        (some (N.step r (liftView c (e :: v'))).1, subAct (N.step r (liftView c (e :: v'))).2)

/-- The configuration of the whole machine described by a configuration of the sub-machine. -/
def subLift (p : ℕ) : PebAutCfg (Option R) (O ⊕ R) → PebAutCfg R O
  | Sum.inl (some r, st) => Sum.inl (r, p :: st)
  | Sum.inl (none, _) => Sum.inr none
  | Sum.inr none => Sum.inr none
  | Sum.inr (some (Sum.inl o)) => Sum.inr (some o)
  | Sum.inr (some (Sum.inr r)) => Sum.inl (r, [p])

lemma subAut_step_of_ne_nil (N : PebbleAut A R O (k + 1)) (c : Option A × Option A) (r₁ r : R)
    {v : PebbleView (A ⊕ A)} (hv : v ≠ []) :
    (subAut N c r₁).step (some r) v =
      (some (N.step r (liftView c v)).1, subAct (N.step r (liftView c v)).2) := by
  cases v with
  | nil => exact absurd rfl hv
  | cons e v' => rfl

/-- One step of the sub-machine above the bottom pebble is one step of the whole machine. -/
lemma subLift_next (N : PebbleAut A R O (k + 1)) {w : List A} {p : ℕ} (hp : p ≤ w.length)
    (r₁ : R) {r : R} {st : List ℕ} (hst : ∀ q ∈ st, q ≤ w.length) (hne : st ≠ []) :
    subLift p ((subAut N (cOf w p) r₁).next (markSplit w p) (Sum.inl (some r, st)))
      = N.next w (subLift p (Sum.inl (some r, st))) := by
  obtain ⟨q, st', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hvne : viewOf (markSplit w p) (q :: st') ≠ [] := by
    simp [viewOf]
  have hlv : liftView (cOf w p) (viewOf (markSplit w p) (q :: st')) = viewOf w (p :: q :: st') :=
    liftView_viewOf hp hst
  have hstep := subAut_step_of_ne_nil N (cOf w p) r₁ r hvne
  rw [hlv] at hstep
  show subLift p ((subAut N (cOf w p) r₁).next (markSplit w p) (Sum.inl (some r, q :: st')))
      = N.next w (Sum.inl (r, p :: q :: st'))
  simp only [PebbleAut.next, hstep]
  cases hact : (N.step r (viewOf w (p :: q :: st'))).2 with
  | stay => simp only [subAct]; rfl
  | halt o => simp only [subAct]; rfl
  | push =>
      simp only [subAct]
      have h1 : ((q :: st').length < k) = ((p :: q :: st').length < k + 1) := by
        simp only [List.length_cons, eq_iff_iff]; omega
      by_cases hlt : (q :: st').length < k
      · rw [if_pos hlt, if_pos (by rw [← h1]; exact hlt)]
        rfl
      · rw [if_neg hlt, if_neg (by rw [← h1]; exact hlt)]
        rfl
  | pop =>
      simp only [subAct]
      rw [if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
      rfl
  | move d =>
      simp only [subAct]
      rw [List.getLast?_cons_cons]
      cases hl : (q :: st').getLast? with
      | none => rfl
      | some x =>
          have hlen : (markSplit w p).length = w.length := markSplit_length w p
          simp only [hlen]
          cases d with
          | true =>
              by_cases hx : x < w.length
              · rw [if_pos hx, if_pos hx]; rfl
              · rw [if_neg hx, if_neg hx]; rfl
          | false =>
              by_cases hx : 0 < x
              · rw [if_pos hx, if_pos hx]; rfl
              · rw [if_neg hx, if_neg hx]; rfl

/-- With an empty stack the sub-machine uncovers the bottom pebble. -/
lemma subAut_next_nil (N : PebbleAut A R O (k + 1)) (c : Option A × Option A) (r₁ r : R)
    (u : List (A ⊕ A)) :
    (subAut N c r₁).next u (Sum.inl (some r, [])) = Sum.inr (some (Sum.inr r)) := by
  simp only [PebbleAut.next, viewOf, List.map_nil]
  rfl

/-- The first step of the sub-machine matches the `push` step of the whole machine. -/
lemma sub_after_start (N : PebbleAut A R O (k + 1)) {w : List A} {p : ℕ} {r r₁ : R}
    (hpush : N.step r (viewOf w [p]) = (r₁, PebAutAction.push)) :
    ((subAut N (cOf w p) r₁).next (markSplit w p) (Sum.inl (none, [])) = Sum.inr none
        ∧ N.next w (Sum.inl (r, [p])) = Sum.inr none)
      ∨ ((subAut N (cOf w p) r₁).next (markSplit w p) (Sum.inl (none, []))
            = Sum.inl (some r₁, [0])
          ∧ N.next w (Sum.inl (r, [p])) = Sum.inl (r₁, [p, 0])) := by
  have hleft : (subAut N (cOf w p) r₁).next (markSplit w p) (Sum.inl (none, []))
      = if (0 : ℕ) < k then Sum.inl (some r₁, [0]) else Sum.inr none := by
    simp only [PebbleAut.next, subAut, List.length_nil, List.nil_append]
  have hright : N.next w (Sum.inl (r, [p]))
      = if (0 : ℕ) < k then Sum.inl (r₁, [p, 0]) else Sum.inr none := by
    simp only [PebbleAut.next, hpush]
    by_cases hk : (0 : ℕ) < k
    · rw [if_pos (show [p].length < k + 1 by simp only [List.length_singleton]; omega),
        if_pos hk]
      rfl
    · rw [if_neg (show ¬ ([p].length < k + 1) by simp only [List.length_singleton]; omega),
        if_neg hk]
  by_cases hk : (0 : ℕ) < k
  · exact Or.inr ⟨by rw [hleft, if_pos hk], by rw [hright, if_pos hk]⟩
  · exact Or.inl ⟨by rw [hleft, if_neg hk], by rw [hright, if_neg hk]⟩

/-- The trichotomy that drives the analysis of a run of the sub-machine: at every moment the
run has either terminated, or is strictly above the bottom pebble, or is about to uncover it;
and in each case the corresponding configuration of the whole machine has been reached. -/
lemma sub_run (N : PebbleAut A R O (k + 1)) {w : List A} {p : ℕ} (hp : p ≤ w.length) (r₁ : R)
    (n : ℕ) {r : R} {st : List ℕ} (hne : st ≠ []) (hst : ∀ q ∈ st, q ≤ w.length) :
    (∃ m x, ((subAut N (cOf w p) r₁).next (markSplit w p))^[n] (Sum.inl (some r, st))
            = Sum.inr x ∧
          subLift p (Sum.inr x) = (N.next w)^[m] (Sum.inl (r, p :: st)))
      ∨ (∃ r' st', st' ≠ [] ∧ (∀ q ∈ st', q ≤ w.length) ∧
          ((subAut N (cOf w p) r₁).next (markSplit w p))^[n] (Sum.inl (some r, st))
            = Sum.inl (some r', st') ∧
          (N.next w)^[n] (Sum.inl (r, p :: st)) = Sum.inl (r', p :: st'))
      ∨ (∃ m r', ((subAut N (cOf w p) r₁).next (markSplit w p))^[n] (Sum.inl (some r, st))
            = Sum.inl (some r', []) ∧
          (N.next w)^[m] (Sum.inl (r, p :: st)) = Sum.inl (r', [p])) := by
  induction n with
  | zero => exact Or.inr (Or.inl ⟨r, st, hne, hst, rfl, rfl⟩)
  | succ n ih =>
      rcases ih with ⟨m, x, hF, hG⟩ | ⟨r', st', hne', hst', hF, hG⟩ | ⟨m, r', hF, hG⟩
      · exact Or.inl ⟨m, x, by rw [Function.iterate_succ_apply', hF, PebbleAut.next_inr], hG⟩
      · have hF1 : ((subAut N (cOf w p) r₁).next (markSplit w p))^[n + 1]
              (Sum.inl (some r, st))
            = (subAut N (cOf w p) r₁).next (markSplit w p) (Sum.inl (some r', st')) := by
          rw [Function.iterate_succ_apply', hF]
        have hG1 : (N.next w)^[n + 1] (Sum.inl (r, p :: st))
            = N.next w (Sum.inl (r', p :: st')) := by
          rw [Function.iterate_succ_apply', hG]
        have hstep : subLift p ((subAut N (cOf w p) r₁).next (markSplit w p)
              (Sum.inl (some r', st'))) = N.next w (Sum.inl (r', p :: st')) :=
          subLift_next N hp r₁ (r := r') hst' hne'
        cases hc : (subAut N (cOf w p) r₁).next (markSplit w p) (Sum.inl (some r', st')) with
        | inr x =>
            refine Or.inl ⟨n + 1, x, by rw [hF1, hc], ?_⟩
            rw [hG1, ← hstep, hc]
        | inl y =>
            obtain ⟨s'', st''⟩ := y
            have hstate := PebbleAut.next_state hc
            have hsome : ∃ r'', s'' = some r'' := by
              rcases hv : viewOf (markSplit w p) st' with _ | ⟨e, v'⟩
              · refine ⟨r', ?_⟩
                rw [hstate, hv]
                rfl
              · refine ⟨(N.step r' (liftView (cOf w p) (e :: v'))).1, ?_⟩
                rw [hstate, hv]
                rfl
            obtain ⟨r'', rfl⟩ := hsome
            have hst'' : ∀ q ∈ st'', q ≤ w.length := by
              have := PebbleAut.next_stack_le
                (N := subAut N (cOf w p) r₁) (w := markSplit w p)
                (by simpa only [markSplit_length] using hst') hc
              simpa only [markSplit_length] using this
            by_cases hnil : st'' = []
            · subst hnil
              refine Or.inr (Or.inr ⟨n + 1, r'', by rw [hF1, hc], ?_⟩)
              rw [hG1, ← hstep, hc]
              rfl
            · refine Or.inr (Or.inl ⟨r'', st'', hnil, hst'', by rw [hF1, hc], ?_⟩)
              rw [hG1, ← hstep, hc]
              rfl
      · refine Or.inl ⟨m, some (Sum.inr r'), ?_, hG.symm⟩
        rw [Function.iterate_succ_apply', hF, subAut_next_nil]

/-! ## What the sub-machine tells about the whole machine -/

/-- If the sub-machine reports that the whole machine halts with the answer `o`, then it does. -/
lemma sub_answers_inl (N : PebbleAut A R O (k + 1)) {w : List A} {p : ℕ} (hp : p ≤ w.length)
    {r r₁ : R} (hpush : N.step r (viewOf w [p]) = (r₁, PebAutAction.push)) {o : O}
    (h : (subAut N (cOf w p) r₁).Answers (markSplit w p) (Sum.inl (none, [])) (Sum.inl o)) :
    ∃ m, 1 ≤ m ∧ (N.next w)^[m] (Sum.inl (r, [p])) = Sum.inr (some o) := by
  obtain ⟨n, hn⟩ := h
  rcases sub_after_start N hpush with ⟨hd, -⟩ | ⟨hc, hg⟩
  · cases n with
    | zero => exact absurd hn (by simp)
    | succ n =>
        rw [Function.iterate_succ_apply, hd, PebbleAut.iterate_next_inr] at hn
        exact absurd hn (by simp)
  · cases n with
    | zero => exact absurd hn (by simp)
    | succ n =>
        rw [Function.iterate_succ_apply, hc] at hn
        rcases sub_run N hp r₁ n (st := [0]) (by simp) (by simp) with
          ⟨m, x, hF, hG⟩ | ⟨r', st', -, -, hF, -⟩ | ⟨m, r', hF, -⟩
        · rw [hF] at hn
          obtain rfl : x = some (Sum.inl o) := Sum.inr_injective hn
          refine ⟨m + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply, hg, ← hG]
          rfl
        · rw [hF] at hn; exact absurd hn (by simp)
        · rw [hF] at hn; exact absurd hn (by simp)

/-- If the sub-machine reports that the bottom pebble is uncovered in the state `r₂`, then the
whole machine does come back to the bottom pebble in that state. -/
lemma sub_answers_inr (N : PebbleAut A R O (k + 1)) {w : List A} {p : ℕ} (hp : p ≤ w.length)
    {r r₁ r₂ : R} (hpush : N.step r (viewOf w [p]) = (r₁, PebAutAction.push))
    (h : (subAut N (cOf w p) r₁).Answers (markSplit w p) (Sum.inl (none, [])) (Sum.inr r₂)) :
    ∃ m, 1 ≤ m ∧ (N.next w)^[m] (Sum.inl (r, [p])) = Sum.inl (r₂, [p]) := by
  obtain ⟨n, hn⟩ := h
  rcases sub_after_start N hpush with ⟨hd, -⟩ | ⟨hc, hg⟩
  · cases n with
    | zero => exact absurd hn (by simp)
    | succ n =>
        rw [Function.iterate_succ_apply, hd, PebbleAut.iterate_next_inr] at hn
        exact absurd hn (by simp)
  · cases n with
    | zero => exact absurd hn (by simp)
    | succ n =>
        rw [Function.iterate_succ_apply, hc] at hn
        rcases sub_run N hp r₁ n (st := [0]) (by simp) (by simp) with
          ⟨m, x, hF, hG⟩ | ⟨r', st', -, -, hF, -⟩ | ⟨m, r', hF, -⟩
        · rw [hF] at hn
          obtain rfl : x = some (Sum.inr r₂) := Sum.inr_injective hn
          refine ⟨m + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply, hg, ← hG]
          rfl
        · rw [hF] at hn; exact absurd hn (by simp)
        · rw [hF] at hn; exact absurd hn (by simp)

/-- If the sub-machine never answers, then neither does the whole machine. -/
lemma sub_no_answer (N : PebbleAut A R O (k + 1)) {w : List A} {p : ℕ} (hp : p ≤ w.length)
    {r r₁ : R} (hpush : N.step r (viewOf w [p]) = (r₁, PebAutAction.push))
    (h : ∀ x, ¬ (subAut N (cOf w p) r₁).Answers (markSplit w p) (Sum.inl (none, [])) x)
    (o : O) : ¬ N.Answers w (Sum.inl (r, [p])) o := by
  rcases sub_after_start N hpush with ⟨-, hd⟩ | ⟨hc, hg⟩
  · exact PebbleAut.not_answers_of_dead (m := 1) (by rw [Function.iterate_one]; exact hd) o
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact absurd hn (by simp)
    | succ j =>
        rw [Function.iterate_succ_apply, hg] at hn
        rcases sub_run N hp r₁ j (st := [0]) (by simp) (by simp) with
          ⟨m, x, hF, hG⟩ | ⟨r', st', -, -, -, hG⟩ | ⟨m, r', hF, -⟩
        · cases x with
          | none =>
              exact PebbleAut.not_answers_of_dead hG.symm o ⟨j, hn⟩
          | some y =>
              refine h y ⟨j + 1, ?_⟩
              rw [Function.iterate_succ_apply, hc, hF]
        · rw [hG] at hn; exact absurd hn (by simp)
        · refine h (Sum.inr r') ⟨j + 2, ?_⟩
          rw [Function.iterate_succ_apply, hc, Function.iterate_succ_apply', hF,
            subAut_next_nil]

end Lax194892Proofs.Transducers
