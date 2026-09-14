/- The *walking* two-way transducer: the machine of the hard half of Theorem
`thm:logic-regular-functions` of *Transducers* (M. Bojańczyk).

After the precomputation of Lemma `lem:logic-precomputation` the input string carries, in each of
its letters, the answers to all the unary questions about the mso transduction,
and the answers to the binary questions are read off by finite automata running
on infixes.  The two-way transducer then simply *walks* along the output order:

* it scans the input from left to right until it meets the first element of the
  output order;
* in an element it outputs the corresponding letter, and then asks whether it is
  the last element, whether its successor sits in the same position, or whether
  the successor is to the right or to the left;
* in the last two cases it walks in that direction, running the automaton for
  the "is the successor of" language on the infix between the two positions, and
  stops at the first position where that automaton accepts.

This file contains the machine and its correctness proof in a purely abstract
form: the data are a family of letter-indexed answers together with a single
deterministic automaton with a family of acceptance conditions, and the
specification is given by the sorted list of the elements of the output order.
Nothing about mso logic appears here.
-/
import Lax916827Proofs.Source.PartC.TwoWayPrecomp
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace WalkAut

open TwoWay

variable {C B I S : Type}

/-! ## Choosing an index -/

open scoped Classical in
/-- Choose an index satisfying a predicate, if there is one. -/
noncomputable def pick (P : I → Prop) : Option I :=
  if h : ∃ i, P i then some h.choose else none

lemma pick_spec {P : I → Prop} {i : I} (h : pick P = some i) : P i := by
  classical
  rw [pick] at h
  split at h
  · rename_i he
    rw [Option.some_inj] at h
    subst h
    exact he.choose_spec
  · exact absurd h (by simp)

lemma pick_eq_none {P : I → Prop} (h : ¬ ∃ i, P i) : pick P = none := by
  classical
  rw [pick, dif_neg h]

lemma pick_eq_some_of_unique {P : I → Prop} {i : I} (hi : P i) (hu : ∀ j, P j → j = i) :
    pick P = some i := by
  classical
  rw [pick, dif_pos ⟨i, hi⟩, Option.some_inj]
  exact hu _ (Exists.choose_spec _)

/-! ## The data of a walk -/

/-- The data from which the walking transducer is built: the letter-indexed
answers to the unary questions, one deterministic automaton with a family of
acceptance conditions for the binary questions, and the output on the empty
input. -/
structure Data (C B I S : Type) where
  /-- The letter produced by an element with the given tag in a given letter. -/
  lb : I → C → B
  /-- Is the element the last one of the output order? -/
  isMax : I → C → Prop
  /-- Does the successor of the element sit in the same position, with the
  given tag? -/
  succH : I → I → C → Prop
  /-- Does the successor of the element sit in a position further right? -/
  succR : I → C → Prop
  /-- The transition function of the automaton. -/
  Dstep : S → C → S
  /-- The initial state of the automaton. -/
  Dstart : S
  /-- Acceptance for the rightward walks: `none` is the search for the first
  element of the output order, `some i` is the search for the successor of an
  element with tag `i`. -/
  accR : Option I → I → S → Prop
  /-- Acceptance for the leftward walks. -/
  accL : I → I → S → Prop
  /-- The output on the empty input. -/
  outNil : List B

variable (D : Data C B I S)

/-- The state of the automaton after reading the infix `u[a..b-1]`. -/
def segFold (u : List C) (a b : ℕ) : S := ((u.take b).drop a).foldl D.Dstep D.Dstart

/-- The transformation of the infix `u[a..b-1]`, applied to a state. -/
def segTrans (u : List C) (a b : ℕ) (s : S) : S := ((u.take b).drop a).foldl D.Dstep s

/-! ## The states of the transducer -/

/-- The states of the walking transducer. -/
abbrev St (I S : Type) := (Option I × S) ⊕ ((I × (S → S)) ⊕ (I ⊕ I))

/-- Walking to the right. -/
def scanR (tag : Option I) (s : S) : St I S := Sum.inl (tag, s)

/-- Walking to the left, carrying the state transformation of the infix already
traversed. -/
def scanL (i : I) (t : S → S) : St I S := Sum.inr (Sum.inl (i, t))

/-- The auxiliary state used to come back to the current position. -/
def bounceSt (i : I) : St I S := Sum.inr (Sum.inr (Sum.inl i))

/-- Producing the letter of the current element. -/
def emitSt (i : I) : St I S := Sum.inr (Sum.inr (Sum.inr i))

open scoped Classical in
/-- The action performed in an element with tag `i` sitting in a position with
letter `a`: produce its letter, and then either stop, or come back to the same
position for the next element, or start walking. -/
noncomputable def act (i : I) (a : C) : List B ⊕ (St I S × List B × Bool) :=
  if D.isMax i a then Sum.inl [D.lb i a]
  else
    match pick (fun i' => D.succH i i' a) with
    | some i'' => Sum.inr (bounceSt i'', [D.lb i a], true)
    | none =>
        if D.succR i a then Sum.inr (scanR (some i) (D.Dstep D.Dstart a), [D.lb i a], true)
        else Sum.inr (scanL i (fun s => D.Dstep s a), [D.lb i a], false)

open scoped Classical in
/-- The walking transducer. -/
noncomputable def aut : TwoWay C B (St I S) where
  init := scanR none D.Dstart
  step := fun l q r =>
    match q with
    | Sum.inl (tag, s) =>
        match r with
        | none => Sum.inl (match l with | none => D.outNil | some _ => [])
        | some a =>
            match pick (fun i' => D.accR tag i' (D.Dstep s a)) with
            | some i' => act D i' a
            | none => Sum.inr (scanR tag (D.Dstep s a), [], true)
    | Sum.inr (Sum.inl (i, t)) =>
        match r with
        | none => Sum.inl []
        | some a =>
            match pick (fun i' => D.accL i i' (t (D.Dstep D.Dstart a))) with
            | some i' => act D i' a
            | none => Sum.inr (scanL i (fun s => t (D.Dstep s a)), [], false)
    | Sum.inr (Sum.inr (Sum.inl i)) => Sum.inr (emitSt i, [], false)
    | Sum.inr (Sum.inr (Sum.inr i)) =>
        match r with
        | none => Sum.inl []
        | some a => act D i a

/-! ## Configurations at a gap -/

/-- The configuration with the head in the gap `p` of the input `u`. -/
def gap (u : List C) (q : St I S) (p : ℕ) : Cfg C (St I S) :=
  Cfg.conf (u.take p) q (u.drop p)

section ListLemmas

variable {u : List C}

lemma head?_drop (p : ℕ) : (u.drop p).head? = u[p]? := by
  rw [List.head?_eq_getElem?, List.getElem?_drop]
  simp

lemma getLast?_take_pos {p : ℕ} (hp : p ≤ u.length) (hp0 : 0 < p) :
    (u.take p).getLast? = u[p - 1]? := by
  have h1 : (u.take p).length = p := by rw [List.length_take]; omega
  rw [List.getLast?_eq_getElem?, h1, List.getElem?_take]
  simp [show p - 1 < p by omega]

lemma dropLast_take_eq {p : ℕ} (hp : p ≤ u.length) : (u.take p).dropLast = u.take (p - 1) := by
  rcases lt_or_eq_of_le hp with h | h
  · rw [List.dropLast_take h]
  · subst h; rw [List.take_length, List.dropLast_eq_take]

lemma take_succ_eq {p : ℕ} (hp : p < u.length) : u.take p ++ [u[p]] = u.take (p + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hp]
  rfl

lemma drop_eq_cons {p : ℕ} (hp : p < u.length) : u.drop p = u[p] :: u.drop (p + 1) :=
  List.drop_eq_getElem_cons hp

end ListLemmas

section Steps

variable {u : List C}

lemma step_right {p : ℕ} (hp : p < u.length) {q q' : St I S} {o : List B}
    (h : (aut D).step ((u.take p).getLast?) q (some u[p]) = Sum.inr (q', o, true)) :
    (aut D).stepCfg (gap u q p) = some (o, gap u q' (p + 1)) := by
  rw [gap, TwoWay.stepCfg, drop_eq_cons hp]
  simp only [List.head?_cons, h]
  rw [gap, take_succ_eq hp]

lemma step_left {p : ℕ} (hp : p ≤ u.length) (hp0 : 0 < p) {q q' : St I S} {o : List B}
    (h : (aut D).step ((u.take p).getLast?) q (u[p]?) = Sum.inr (q', o, false)) :
    (aut D).stepCfg (gap u q p) = some (o, gap u q' (p - 1)) := by
  have hlast : (u.take p).getLast? = u[p - 1]? := getLast?_take_pos hp hp0
  have hlt : p - 1 < u.length := by omega
  have hsome : u[p - 1]? = some u[p - 1] := List.getElem?_eq_getElem hlt
  have h2 : u.drop (p - 1) = u[p - 1] :: u.drop p := by
    rw [drop_eq_cons hlt, show p - 1 + 1 = p by omega]
  rw [gap, TwoWay.stepCfg, head?_drop, h]
  simp only [hlast, hsome]
  rw [gap, dropLast_take_eq hp, h2]

lemma step_halt {p : ℕ} {q : St I S} {o : List B}
    (h : (aut D).step ((u.take p).getLast?) q (u[p]?) = Sum.inl o) :
    (aut D).stepCfg (gap u q p) = some (o, Cfg.halt) := by
  rw [gap, TwoWay.stepCfg, head?_drop, h]

end Steps

/-! ## Segments -/

section Seg

variable {u : List C}

lemma segFold_succ {p q : ℕ} (hpq : p ≤ q) (hq : q < u.length) :
    segFold D u p (q + 1) = D.Dstep (segFold D u p q) u[q] := by
  have h1 : u.take (q + 1) = u.take q ++ [u[q]] := (take_succ_eq hq).symm
  have h2 : (u.take q).length = q := by rw [List.length_take]; omega
  rw [segFold, segFold, h1, List.drop_append_of_le_length (by omega), List.foldl_append]
  rfl

lemma segFold_self {p : ℕ} (h : p ≤ u.length) : segFold D u p p = D.Dstart := by
  rw [segFold, List.drop_eq_nil_of_le (by rw [List.length_take]; omega)]
  rfl

lemma segTrans_start (a b : ℕ) : segTrans D u a b D.Dstart = segFold D u a b := rfl

lemma segTrans_cons {a b : ℕ} (hab : a < b) (ha : a < u.length) :
    (fun s => segTrans D u (a + 1) b (D.Dstep s u[a])) = segTrans D u a b := by
  funext s
  have hlt : a < (u.take b).length := by rw [List.length_take]; omega
  have hget : (u.take b)[a] = u[a] := List.getElem_take ..
  rw [segTrans, segTrans, List.drop_eq_getElem_cons hlt, hget]
  rfl

lemma segTrans_last {p : ℕ} (hp : p < u.length) :
    (fun s => D.Dstep s u[p]) = segTrans D u p (p + 1) := by
  have h := segTrans_cons D (u := u) (a := p) (b := p + 1) (by omega) hp
  rw [← h]
  funext s
  rw [segTrans, List.drop_eq_nil_of_le (by rw [List.length_take]; omega)]
  rfl

end Seg

/-! ## Correctness -/

section Correct

open scoped Classical

variable {D}
variable {u : List C}

/-- Two configurations that differ only in the state, but whose transitions
agree at the letters actually seen, behave in the same way. -/
lemma reaches_state_congr {q q' : St I S} {U V : List C}
    (h : (aut D).step U.getLast? q V.head? = (aut D).step U.getLast? q' V.head?) {o : List B}
    (hr : (aut D).Reaches (Cfg.conf U q' V) o Cfg.halt) :
    (aut D).Reaches (Cfg.conf U q V) o Cfg.halt := by
  have hstep : (aut D).stepCfg (Cfg.conf U q V) = (aut D).stepCfg (Cfg.conf U q' V) := by
    rw [TwoWay.stepCfg, TwoWay.stepCfg, h]
  cases hr with
  | step hs hrest => exact TwoWay.Reaches.step (hstep.trans hs) hrest

/-- The rightward walk reaches the element that the automaton finds. -/
lemma scanR_reach (tag : Option I) (base : ℕ) :
    ∀ (d q q' : ℕ) (i' : I), q' = q + d → q' < u.length → base ≤ q →
      (∀ m, q ≤ m → m < q' → pick (fun j => D.accR tag j (segFold D u base (m + 1))) = none) →
      pick (fun j => D.accR tag j (segFold D u base (q' + 1))) = some i' →
      ∀ o, (aut D).Reaches (gap u (emitSt i') q') o Cfg.halt →
        (aut D).Reaches (gap u (scanR tag (segFold D u base q)) q) o Cfg.halt := by
  intro d
  induction d with
  | zero =>
      intro q q' i' hd hq' hbq _ hfound o hrest
      have hqq : q' = q := by omega
      subst hqq
      refine reaches_state_congr (D := D) ?_ hrest
      rw [head?_drop, List.getElem?_eq_getElem hq']
      show (match pick (fun j => D.accR tag j (D.Dstep (segFold D u base q') u[q'])) with
          | some i' => act D i' u[q']
          | none => Sum.inr (scanR tag (D.Dstep (segFold D u base q') u[q']), [], true))
        = act D i' u[q']
      rw [← segFold_succ D hbq hq', hfound]
  | succ d ih =>
      intro q q' i' hd hq' hbq hnone hfound o hrest
      have hqlt : q < q' := by omega
      have hq : q < u.length := by omega
      have hpn : pick (fun j => D.accR tag j (segFold D u base (q + 1))) = none :=
        hnone q le_rfl hqlt
      have hstep : (aut D).step ((u.take q).getLast?) (scanR tag (segFold D u base q))
          (some u[q]) = Sum.inr (scanR tag (segFold D u base (q + 1)), [], true) := by
        show (match pick (fun j => D.accR tag j (D.Dstep (segFold D u base q) u[q])) with
            | some i' => act D i' u[q]
            | none => Sum.inr (scanR tag (D.Dstep (segFold D u base q) u[q]), [], true)) = _
        rw [← segFold_succ D hbq hq, hpn]
      have hrec := ih (q + 1) q' i' (by omega) hq' (by omega)
        (fun m hm hm' => hnone m (by omega) hm') hfound o hrest
      have := TwoWay.Reaches.step (step_right D hq hstep) hrec
      simpa using this

/-- If the automaton never accepts, the rightward walk runs off the input and
halts with no output. -/
lemma scanR_end (tag : Option I) (base : ℕ) (hu : 0 < u.length) :
    ∀ (d q : ℕ), q + d = u.length → base ≤ q →
      (∀ m, q ≤ m → m < u.length →
        pick (fun j => D.accR tag j (segFold D u base (m + 1))) = none) →
      (aut D).Reaches (gap u (scanR tag (segFold D u base q)) q) [] Cfg.halt := by
  intro d
  induction d with
  | zero =>
      intro q hq _ _
      have hqn : q = u.length := by omega
      subst hqn
      have hnone : u[u.length]? = none := List.getElem?_eq_none (by omega)
      have hlast : (u.take u.length).getLast? = u[u.length - 1]? :=
        getLast?_take_pos le_rfl hu
      have hsome : u[u.length - 1]? = some u[u.length - 1] :=
        List.getElem?_eq_getElem (by omega)
      have hstep : (aut D).step ((u.take u.length).getLast?)
          (scanR tag (segFold D u base u.length)) (u[u.length]?) = Sum.inl [] := by
        rw [hnone, hlast, hsome]
        rfl
      simpa using TwoWay.Reaches.step (step_halt D hstep) (TwoWay.Reaches.refl _)
  | succ d ih =>
      intro q hq hbq hnone
      have hqlt : q < u.length := by omega
      have hpn : pick (fun j => D.accR tag j (segFold D u base (q + 1))) = none :=
        hnone q le_rfl hqlt
      have hstep : (aut D).step ((u.take q).getLast?) (scanR tag (segFold D u base q))
          (some u[q]) = Sum.inr (scanR tag (segFold D u base (q + 1)), [], true) := by
        show (match pick (fun j => D.accR tag j (D.Dstep (segFold D u base q) u[q])) with
            | some i' => act D i' u[q]
            | none => Sum.inr (scanR tag (D.Dstep (segFold D u base q) u[q]), [], true)) = _
        rw [← segFold_succ D hbq hqlt, hpn]
      have hrec := ih (q + 1) (by omega) (by omega) (fun m hm hm' => hnone m (by omega) hm')
      simpa using TwoWay.Reaches.step (step_right D hqlt hstep) hrec

/-- The leftward walk reaches the element that the automaton finds. -/
lemma scanL_reach (i : I) (base : ℕ) (hbase : base < u.length) :
    ∀ (d q q' : ℕ) (i' : I), q = q' + d → q < base →
      (∀ m, q' < m → m ≤ q → pick (fun j => D.accL i j (segFold D u m (base + 1))) = none) →
      pick (fun j => D.accL i j (segFold D u q' (base + 1))) = some i' →
      ∀ o, (aut D).Reaches (gap u (emitSt i') q') o Cfg.halt →
        (aut D).Reaches (gap u (scanL i (segTrans D u (q + 1) (base + 1))) q) o Cfg.halt := by
  intro d
  induction d with
  | zero =>
      intro q q' i' hd hq _ hfound o hrest
      have hqq : q' = q := by omega
      subst hqq
      have hq' : q' < u.length := by omega
      refine reaches_state_congr (D := D) ?_ hrest
      rw [head?_drop, List.getElem?_eq_getElem hq']
      show (match pick (fun j => D.accL i j
            (segTrans D u (q' + 1) (base + 1) (D.Dstep D.Dstart u[q']))) with
          | some i₁ => act D i₁ u[q']
          | none => Sum.inr (scanL i (fun s =>
              segTrans D u (q' + 1) (base + 1) (D.Dstep s u[q'])), [], false))
        = act D i' u[q']
      rw [show segTrans D u (q' + 1) (base + 1) (D.Dstep D.Dstart u[q'])
            = segFold D u q' (base + 1) by
          rw [← segTrans_start D q' (base + 1)]
          conv_rhs => rw [← segTrans_cons D (a := q') (b := base + 1) (by omega) hq'],
        hfound]
  | succ d ih =>
      intro q q' i' hd hq hnone hfound o hrest
      have hqlt : q' < q := by omega
      have hqu : q < u.length := by omega
      have hpn : pick (fun j => D.accL i j (segFold D u q (base + 1))) = none :=
        hnone q hqlt le_rfl
      have heq : segTrans D u (q + 1) (base + 1) (D.Dstep D.Dstart u[q])
          = segFold D u q (base + 1) := by
        rw [← segTrans_start D q (base + 1)]
        conv_rhs => rw [← segTrans_cons D (a := q) (b := base + 1) (by omega) hqu]
      have hstep : (aut D).step ((u.take q).getLast?)
          (scanL i (segTrans D u (q + 1) (base + 1))) (u[q]?)
          = Sum.inr (scanL i (segTrans D u q (base + 1)), [], false) := by
        rw [List.getElem?_eq_getElem hqu]
        show (match pick (fun j => D.accL i j
              (segTrans D u (q + 1) (base + 1) (D.Dstep D.Dstart u[q]))) with
            | some i₁ => act D i₁ u[q]
            | none => Sum.inr (scanL i (fun s =>
                segTrans D u (q + 1) (base + 1) (D.Dstep s u[q])), [], false)) = _
        rw [heq, hpn, segTrans_cons D (a := q) (b := base + 1) (by omega) hqu]
      have hrec := ih (q - 1) q' i' (by omega) (by omega)
        (fun m hm hm' => hnone m hm (by omega)) hfound o hrest
      have hq1 : q - 1 + 1 = q := by omega
      rw [hq1] at hrec
      have := TwoWay.Reaches.step (step_left D (le_of_lt hqu) (by omega) hstep) hrec
      simpa using this

end Correct

/-! ## The specification -/

section Spec

open scoped Classical

variable {D}
variable {u : List C} {es : List (I × ℕ)} {v : List B}
  (hlen : es.length = v.length)
  (hpos : ∀ x ∈ es, x.2 < u.length)
  (hlab : ∀ (r : ℕ) (i : I) (p : ℕ) (a : C), es[r]? = some (i, p) → u[p]? = some a →
    v[r]? = some (D.lb i a))
  (hmax : ∀ (r : ℕ) (i : I) (p : ℕ) (a : C), es[r]? = some (i, p) → u[p]? = some a →
    (D.isMax i a ↔ r + 1 = es.length))
  (hsuccH : ∀ (r : ℕ) (i : I) (p : ℕ) (a : C) (i₁ : I) (p₁ : ℕ),
    es[r]? = some (i, p) → es[r + 1]? = some (i₁, p₁) → u[p]? = some a →
    ∀ j, (D.succH i j a ↔ (p₁ = p ∧ i₁ = j)))
  (hsuccR : ∀ (r : ℕ) (i : I) (p : ℕ) (a : C) (i₁ : I) (p₁ : ℕ),
    es[r]? = some (i, p) → es[r + 1]? = some (i₁, p₁) → u[p]? = some a →
    (D.succR i a ↔ p < p₁))
  (haccR : ∀ (r : ℕ) (i : I) (p : ℕ) (i₁ : I) (p₁ : ℕ),
    es[r]? = some (i, p) → es[r + 1]? = some (i₁, p₁) →
    ∀ q, p ≤ q → q < u.length → ∀ j,
      (D.accR (some i) j (segFold D u p (q + 1)) ↔ (j = i₁ ∧ q = p₁)))
  (haccL : ∀ (r : ℕ) (i : I) (p : ℕ) (i₁ : I) (p₁ : ℕ),
    es[r]? = some (i, p) → es[r + 1]? = some (i₁, p₁) →
    ∀ q, q ≤ p → ∀ j, (D.accL i j (segFold D u q (p + 1)) ↔ (j = i₁ ∧ q = p₁)))

include hlen hpos hlab hmax hsuccH hsuccR haccR haccL

/-- From an element of the output order, the transducer produces the labels of
that element and of all the later ones, and halts. -/
lemma emit_reach :
    ∀ (d r : ℕ), r + d = es.length → ∀ (i : I) (p : ℕ), es[r]? = some (i, p) →
      (aut D).Reaches (gap u (emitSt i) p) (v.drop r) Cfg.halt := by
  intro d
  induction d with
  | zero =>
      intro r hr i p hes
      rw [List.getElem?_eq_none (by omega)] at hes
      exact absurd hes (by simp)
  | succ d ih =>
      intro r hr i p hes
      have hrl : r < es.length := by omega
      have hmem : (i, p) ∈ es := List.mem_iff_getElem?.2 ⟨r, hes⟩
      have hp : p < u.length := hpos _ hmem
      have ha : u[p]? = some u[p] := List.getElem?_eq_getElem hp
      have hvr : v[r]? = some (D.lb i u[p]) := hlab r i p _ hes ha
      have hrv : r < v.length := by
        rw [← hlen]; omega
      have hvget : v[r] = D.lb i u[p] := by
        rw [List.getElem?_eq_getElem hrv] at hvr
        exact Option.some_inj.1 hvr
      have hdrop : v.drop r = D.lb i u[p] :: v.drop (r + 1) := by
        rw [List.drop_eq_getElem_cons hrv, hvget]
      by_cases hlast : r + 1 = es.length
      · -- the last element
        have hstep : (aut D).step ((u.take p).getLast?) (emitSt i) (u[p]?)
            = Sum.inl [D.lb i u[p]] := by
          rw [ha]
          show act D i u[p] = _
          rw [act, if_pos ((hmax r i p _ hes ha).2 hlast)]
        have hnil : v.drop (r + 1) = [] := by
          rw [List.drop_eq_nil_iff]
          omega
        rw [hdrop, hnil]
        simpa using TwoWay.Reaches.step (step_halt D hstep) (TwoWay.Reaches.refl _)
      · -- there is a next element
        have hrl' : r + 1 < es.length := by omega
        obtain ⟨⟨i₁, p₁⟩, hes1⟩ : ∃ x : I × ℕ, es[r + 1]? = some x := by
          rw [List.getElem?_eq_getElem hrl']
          exact ⟨_, rfl⟩
        have hmem1 : (i₁, p₁) ∈ es := List.mem_iff_getElem?.2 ⟨r + 1, hes1⟩
        have hp1 : p₁ < u.length := hpos _ hmem1
        have hnotmax : ¬ D.isMax i u[p] := by
          rw [hmax r i p _ hes ha]
          exact hlast
        have hIH := ih (r + 1) (by omega) i₁ p₁ hes1
        rcases lt_trichotomy p₁ p with hlt | heq | hgt
        · -- the successor is to the left
          have hH : pick (fun j => D.succH i j u[p]) = none := by
            refine pick_eq_none ?_
            rintro ⟨j, hj⟩
            rw [hsuccH r i p _ i₁ p₁ hes hes1 ha j] at hj
            omega
          have hR : ¬ D.succR i u[p] := by
            rw [hsuccR r i p _ i₁ p₁ hes hes1 ha]
            omega
          have hstep : (aut D).step ((u.take p).getLast?) (emitSt i) (u[p]?)
              = Sum.inr (scanL i (segTrans D u p (p + 1)), [D.lb i u[p]], false) := by
            rw [ha]
            show act D i u[p] = _
            rw [act, if_neg hnotmax, hH, if_neg hR, segTrans_last D hp]
          have hfound : pick (fun j => D.accL i j (segFold D u p₁ (p + 1))) = some i₁ := by
            refine pick_eq_some_of_unique ((haccL r i p i₁ p₁ hes hes1 p₁ (by omega) i₁).2
              ⟨rfl, rfl⟩) ?_
            intro j hj
            exact ((haccL r i p i₁ p₁ hes hes1 p₁ (by omega) j).1 hj).1
          have hnone : ∀ m, p₁ < m → m ≤ p - 1 →
              pick (fun j => D.accL i j (segFold D u m (p + 1))) = none := by
            intro m hm hm'
            refine pick_eq_none ?_
            rintro ⟨j, hj⟩
            have := ((haccL r i p i₁ p₁ hes hes1 m (by omega) j).1 hj).2
            omega
          have hwalk := scanL_reach (D := D) i p hp (p - 1 - p₁) (p - 1) p₁ i₁ (by omega)
            (by omega) hnone hfound _ hIH
          rw [show p - 1 + 1 = p by omega] at hwalk
          have := TwoWay.Reaches.step
            (step_left D (le_of_lt hp) (by omega) hstep) hwalk
          rw [hdrop]
          simpa using this
        · -- the successor is in the same position
          subst heq
          have hH : pick (fun j => D.succH i j u[p₁]) = some i₁ := by
            refine pick_eq_some_of_unique ((hsuccH r i p₁ _ i₁ p₁ hes hes1 ha i₁).2
              ⟨rfl, rfl⟩) ?_
            intro j hj
            exact (((hsuccH r i p₁ _ i₁ p₁ hes hes1 ha j).1 hj).2).symm
          have hstep : (aut D).step ((u.take p₁).getLast?) (emitSt i) (some u[p₁])
              = Sum.inr (bounceSt i₁, [D.lb i u[p₁]], true) := by
            show act D i u[p₁] = _
            rw [act, if_neg hnotmax, hH]
          have hstep2 : (aut D).step ((u.take (p₁ + 1)).getLast?) (bounceSt i₁)
              (u[p₁ + 1]?) = Sum.inr (emitSt i₁, [], false) := rfl
          have h2 := TwoWay.Reaches.step
            (step_left D (by omega) (by omega) hstep2) hIH
          have h1 := TwoWay.Reaches.step (step_right D hp hstep) h2
          rw [hdrop]
          simpa using h1
        · -- the successor is to the right
          have hH : pick (fun j => D.succH i j u[p]) = none := by
            refine pick_eq_none ?_
            rintro ⟨j, hj⟩
            rw [hsuccH r i p _ i₁ p₁ hes hes1 ha j] at hj
            omega
          have hR : D.succR i u[p] := by
            rw [hsuccR r i p _ i₁ p₁ hes hes1 ha]
            omega
          have hstep : (aut D).step ((u.take p).getLast?) (emitSt i) (some u[p])
              = Sum.inr (scanR (some i) (segFold D u p (p + 1)), [D.lb i u[p]], true) := by
            show act D i u[p] = _
            rw [act, if_neg hnotmax, hH, if_pos hR, segFold_succ D le_rfl hp,
              segFold_self D (le_of_lt hp)]
          have hfound : pick (fun j => D.accR (some i) j (segFold D u p (p₁ + 1)))
              = some i₁ := by
            refine pick_eq_some_of_unique
              ((haccR r i p i₁ p₁ hes hes1 p₁ (by omega) hp1 i₁).2 ⟨rfl, rfl⟩) ?_
            intro j hj
            exact ((haccR r i p i₁ p₁ hes hes1 p₁ (by omega) hp1 j).1 hj).1
          have hnone : ∀ m, p + 1 ≤ m → m < p₁ →
              pick (fun j => D.accR (some i) j (segFold D u p (m + 1))) = none := by
            intro m hm hm'
            refine pick_eq_none ?_
            rintro ⟨j, hj⟩
            have := ((haccR r i p i₁ p₁ hes hes1 m (by omega) (by omega) j).1 hj).2
            omega
          have hwalk := scanR_reach (D := D) (some i) p (p₁ - (p + 1)) (p + 1) p₁ i₁
            (by omega) hp1 (by omega) hnone hfound _ hIH
          have := TwoWay.Reaches.step (step_right D hp hstep) hwalk
          rw [hdrop]
          simpa using this

omit hpos hlab hmax hsuccH hsuccR haccR haccL in
/-- If no element is selected, the output is empty. -/
lemma out_nil_of_es_nil (h : es = []) : v = [] := by
  rw [← List.length_eq_zero_iff, ← hlen, h]
  rfl

variable (haccRmin : ∀ q, q < u.length → ∀ j,
    (D.accR none j (segFold D u 0 (q + 1)) ↔ es[0]? = some (j, q)))

include haccRmin

/-- **The walking transducer computes the output.** -/
theorem computes_of_spec (hu : 0 < u.length) : (aut D).Computes u v := by
  have hinit : (aut D).Computes u v ↔
      (aut D).Reaches (gap u (scanR none (segFold D u 0 0)) 0) v Cfg.halt := by
    rw [segFold_self D (by omega)]
    rfl
  rw [hinit]
  by_cases hnil : es = []
  · have hv : v = [] := out_nil_of_es_nil hlen hnil
    subst hv
    refine scanR_end (D := D) none 0 hu u.length 0 (by omega) le_rfl ?_
    intro m _ hm
    refine pick_eq_none ?_
    rintro ⟨j, hj⟩
    rw [haccRmin m hm j, hnil] at hj
    exact absurd hj (by simp)
  · obtain ⟨⟨i₀, p₀⟩, t, hes⟩ := List.exists_cons_of_ne_nil hnil
    have hes0 : es[0]? = some (i₀, p₀) := by rw [hes]; rfl
    have hp0 : p₀ < u.length := hpos _ (by rw [hes]; exact List.mem_cons_self ..)
    have hfound : pick (fun j => D.accR none j (segFold D u 0 (p₀ + 1))) = some i₀ := by
      refine pick_eq_some_of_unique ((haccRmin p₀ hp0 i₀).2 hes0) ?_
      intro j hj
      have := (haccRmin p₀ hp0 j).1 hj
      rw [hes0] at this
      exact (congrArg Prod.fst (Option.some_inj.1 this)).symm
    have hnone : ∀ m, 0 ≤ m → m < p₀ →
        pick (fun j => D.accR none j (segFold D u 0 (m + 1))) = none := by
      intro m _ hm
      refine pick_eq_none ?_
      rintro ⟨j, hj⟩
      have := (haccRmin m (by omega) j).1 hj
      rw [hes0] at this
      have : p₀ = m := congrArg (fun z => (z.getD (i₀, p₀)).2) this
      omega
    have hIH := emit_reach hlen hpos hlab hmax hsuccH hsuccR haccR haccL
      (es.length - 0) 0 (by omega) i₀ p₀ (by rw [hes]; rfl)
    rw [List.drop_zero] at hIH
    exact scanR_reach (D := D) none 0 p₀ 0 p₀ i₀ (by omega) hp0 (by omega) hnone hfound _ hIH

end Spec

/-- On the empty input the transducer produces `outNil`. -/
lemma computes_nil : (aut D).Computes [] D.outNil := by
  have hstep : (aut D).stepCfg (Cfg.conf [] (aut D).init []) = some (D.outNil, Cfg.halt) := rfl
  simpa using TwoWay.Reaches.step hstep (TwoWay.Reaches.refl _)

end WalkAut

end Lax314295Proofs.Transducers
