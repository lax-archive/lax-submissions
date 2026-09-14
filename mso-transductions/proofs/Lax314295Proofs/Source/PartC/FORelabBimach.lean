/-
From first-order relabellings to aperiodic bimachines: one implication of
Theorem `thm:fo-rational-functions` of *Transducers* (M. Bojańczyk).

"Let `k` be the maximal quantifier rank of the first-order formulas used in the
relabelling.  The output produced on the `i`-th position depends only on the
`k`-type of the prefix `a₁ ⋯ a_{i-1}`, on the letter `a_i` and on the `k`-type
of the suffix `a_{i+1} ⋯ a_n`.  To retrieve this information we use the prefix
and suffix automata of the bimachine: after reading `a₁ ⋯ a_i` the prefix
automaton keeps track of the `k`-type of `a₁ ⋯ a_{i-1}` and of the letter
`a_i`, and after reading the suffix `a_{i+1} ⋯ a_n` the suffix automaton keeps
track of its `k`-type."

Both automata are automata of `k`-types, so they are aperiodic
(`Transducers.transAperiodic_tpStep`); for the suffix automaton, which reads the
suffix from right to left, the transition function appends a letter *on the
left*, and its aperiodicity uses that the `k`-type of a string determines the
`k`-type of its reverse (`Transducers.tp_reverse`).

The bimachine has one output block per gap of the input string, while the
relabelling has one per position; the gap `i + 1` is used for the position `i`,
and the gap `0` outputs the empty string, except on the empty input, where it
outputs the string that the relabelling prescribes for the empty input.  This
is why the `k`-type of the whole suffix is enough to recognise the empty input:
for `k ≥ 1` the empty string is the only string of its `k`-type.
-/
import Lax314295Proofs.Source.PartC.FOPos
import Lax314295Proofs.Source.PartC.FORev
import Lax132576Proofs.Source.PartB.Bimachine
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace FORelabBimach

variable {A B : Type}

/-! ## Appending a letter on the left -/

open scoped Classical in
/-- The transition on `k`-types that appends a letter on the *left*.  On the
types that are not realised by any string it is the identity. -/
noncomputable def tpStepL (k : ℕ) (a : A) (t : TpType A k) : TpType A k :=
  if h : ∃ u : List A, tp k u = t then tp k (a :: h.choose) else t

lemma tpStepL_tp (k : ℕ) (a : A) (u : List A) : tpStepL k a (tp k u) = tp k (a :: u) := by
  have h : ∃ z : List A, tp k z = tp k u := ⟨u, rfl⟩
  rw [tpStepL, dif_pos h]
  exact tp_congr k [a] [a] _ _ rfl h.choose_spec

lemma tpStepL_of_not_realised {k : ℕ} {t : TpType A k} (h : ¬ ∃ u : List A, tp k u = t)
    (a : A) : tpStepL k a t = t := by
  rw [tpStepL, dif_neg h]

/-! ## The two automata -/

/-- The state of the prefix automaton after a letter: the `k`-type of the
prefix before the letter that was pending, and the new pending letter. -/
noncomputable def prefStep (k : ℕ) (st : TpType A k × Option A) (a : A) :
    TpType A k × Option A :=
  ((match st.2 with
    | none => st.1
    | some b => tpStep k st.1 b), some a)

/-- The transition function of the suffix automaton, which reads the suffix
from right to left. -/
noncomputable def sufStep (k : ℕ) (t : TpType A k) (a : A) : TpType A k := tpStepL k a t

/-- Absorbing the pending letter into the type. -/
noncomputable def extO (k : ℕ) (t : TpType A k) : Option A → TpType A k
  | none => t
  | some b => tpStep k t b

lemma prefStep_eval_gen (k : ℕ) (t : TpType A k) (o : Option A) :
    ∀ u : List A, u ≠ [] →
      strTrans (prefStep k) u (t, o) =
        (strTrans (tpStep k) u.dropLast (extO k t o), u.getLast?) := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton u a ih =>
      intro _
      have hfold : strTrans (prefStep k) (u ++ [a]) (t, o) =
          prefStep k (strTrans (prefStep k) u (t, o)) a := by
        simp [strTrans, List.foldl_append]
      rw [hfold]
      rcases eq_or_ne u [] with rfl | hu
      · simp [strTrans, prefStep, extO]
      · rw [ih hu]
        have hlast : ∃ b, u.getLast? = some b := by
          cases hb : u.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.mp hb) hu
          | some b => exact ⟨b, rfl⟩
        obtain ⟨b, hb⟩ := hlast
        have hu' : u.dropLast ++ [b] = u := List.dropLast_append_getLast? _ (by rw [hb]; rfl)
        have : prefStep k (strTrans (tpStep k) u.dropLast (extO k t o), u.getLast?) a =
            (tpStep k (strTrans (tpStep k) u.dropLast (extO k t o)) b, some a) := by
          rw [prefStep, hb]
        rw [this]
        have h1 : strTrans (tpStep k) (u ++ [a]).dropLast (extO k t o)
            = tpStep k (strTrans (tpStep k) u.dropLast (extO k t o)) b := by
          rw [List.dropLast_concat]
          conv_lhs => rw [← hu']
          simp [strTrans, List.foldl_append]
        rw [h1]
        simp

lemma prefStep_eval (k : ℕ) (u : List A) :
    strTrans (prefStep k) u (tp k ([] : List A), none) = (tp k u.dropLast, u.getLast?) := by
  rcases eq_or_ne u [] with rfl | hu
  · simp [strTrans]
  · rw [prefStep_eval_gen k _ _ u hu]
    congr 1
    show strTrans (tpStep k) u.dropLast (tp k ([] : List A)) = tp k u.dropLast
    rw [strTrans_tpStep]
    simp

lemma sufStep_eval (k : ℕ) : ∀ (u x : List A),
    strTrans (sufStep k) u (tp k x) = tp k (u.reverse ++ x) := by
  intro u
  induction u with
  | nil => intro x; simp [strTrans]
  | cons a u ih =>
      intro x
      show List.foldl (sufStep k) (tp k x) (a :: u) = _
      rw [List.foldl_cons]
      have h1 : sufStep k (tp k x) a = tp k (a :: x) := tpStepL_tp k a x
      rw [h1]
      have := ih (a :: x)
      show strTrans (sufStep k) u (tp k (a :: x)) = _
      rw [this]
      simp

lemma sufStep_eval_of_not_realised {k : ℕ} {t : TpType A k} (h : ¬ ∃ u : List A, tp k u = t) :
    ∀ z : List A, strTrans (sufStep k) z t = t := by
  intro z
  induction z with
  | nil => rfl
  | cons a z ih =>
      show List.foldl (sufStep k) t (a :: z) = t
      rw [List.foldl_cons]
      have : sufStep k t a = t := tpStepL_of_not_realised h a
      rw [this]
      exact ih

/-! ## Aperiodicity -/

lemma transAperiodic_prefStep (k : ℕ) : TransAperiodic (prefStep (A := A) k) := by
  intro w
  rcases eq_or_ne w [] with rfl | hw
  · refine ⟨0, fun n _ => ?_⟩
    rw [strTrans_iterate_npow, strTrans_iterate_npow]
    have h : ∀ m : ℕ, npow ([] : List A) m = [] := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [npow_succ, ih]; rfl
    rw [h, h]
  · obtain ⟨N, hN⟩ := transAperiodic_tpStep (A := A) k w
    refine ⟨N + 1, fun n hn => ?_⟩
    rw [strTrans_iterate_npow, strTrans_iterate_npow]
    funext st
    obtain ⟨t, o⟩ := st
    have key : ∀ m : ℕ, N + 1 ≤ m →
        strTrans (prefStep k) (npow w m) (t, o) =
          (strTrans (tpStep k) w.dropLast ((strTrans (tpStep k) w)^[N] (extO k t o)),
            w.getLast?) := by
      intro m hm
      have hsplit : npow w m = npow w (m - 1) ++ w := by
        have : m - 1 + 1 = m := by omega
        rw [← this, npow_add]
        simp [npow]
      have hne : npow w m ≠ [] := by
        rw [hsplit]
        intro h
        exact hw (List.append_eq_nil_iff.mp h).2
      rw [prefStep_eval_gen k t o _ hne]
      have hlast : (npow w m).getLast? = w.getLast? := by
        rw [hsplit]
        exact List.getLast?_append_of_ne_nil _ hw
      have hdrop : (npow w m).dropLast = npow w (m - 1) ++ w.dropLast := by
        rw [hsplit, List.dropLast_append_of_ne_nil hw]
      rw [hlast, hdrop]
      congr 1
      have hfold : strTrans (tpStep k) (npow w (m - 1) ++ w.dropLast) (extO k t o)
          = strTrans (tpStep k) w.dropLast
              (strTrans (tpStep k) (npow w (m - 1)) (extO k t o)) := by
        simp [strTrans, List.foldl_append]
      rw [hfold]
      congr 1
      rw [← strTrans_iterate_npow]
      exact congrFun (hN (m - 1) (by omega)) _
    rw [key n hn, key (N + 1) le_rfl]

lemma transAperiodic_sufStep (k : ℕ) : TransAperiodic (sufStep (A := A) k) := by
  intro w
  refine ⟨tpBound k, fun n hn => ?_⟩
  rw [strTrans_iterate_npow, strTrans_iterate_npow]
  funext t
  by_cases ht : ∃ u : List A, tp k u = t
  · obtain ⟨u, rfl⟩ := ht
    have h1 : ∀ m : ℕ, strTrans (sufStep k) (npow w m) (tp k u)
        = tp k ((npow w m).reverse ++ u) := fun m => sufStep_eval k _ _
    rw [h1, h1]
    refine tp_congr k _ _ u u ?_ rfl
    rw [tp_reverse, tp_reverse]
    exact congrArg (tpRev k) (tp_npow_eq k w n (tpBound k) hn le_rfl)
  · rw [sufStep_eval_of_not_realised ht, sufStep_eval_of_not_realised ht]

/-! ## The bimachine of a first-order relabelling -/

variable (R : MSORelabelling A B) (k : ℕ)

open scoped Classical in
/-- The index of the formula of the relabelling that holds at every position
with the given level-`k` data (type of the prefix, letter, type of the
suffix). -/
noncomputable def idxOf (t : TpType A k) (a : A) (s : TpType A k) : Option R.Idx :=
  if h : ∃ i : R.Idx, ∀ (w : List A) (p : ℕ), p < w.length → tp k (w.take p) = t →
      w[p]? = some a → tp k (w.drop (p + 1)) = s →
      MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form i)
    then some h.choose else none

open scoped Classical in
/-- The output function of the bimachine. -/
noncomputable def outOf (st : TpType A k × Option A) (s : TpType A k) : List B :=
  match st.2 with
  | none => if s = tp k ([] : List A) then R.emptyOut else []
  | some a =>
      match idxOf R k st.1 a s with
      | none => []
      | some i => R.out i

/-- The bimachine associated with a first-order relabelling. -/
noncomputable def bimach : Bimachine A B (TpType A k × Option A) (TpType A k) where
  prefixInit := (tp k ([] : List A), none)
  prefixStep := prefStep k
  suffixInit := tp k ([] : List A)
  suffixStep := sufStep k
  out := outOf R k

lemma bimach_chunk (w : List A) (i : ℕ) :
    outOf R k (strTrans (prefStep k) (w.take i) (tp k ([] : List A), none))
        (strTrans (sufStep k) (w.drop i).reverse (tp k ([] : List A)))
      = outOf R k (tp k (w.take i).dropLast, (w.take i).getLast?) (tp k (w.drop i)) := by
  rw [prefStep_eval]
  congr 1
  rw [sufStep_eval]
  simp

/-! ## Correctness -/

variable {R k}

open scoped Classical in
/-- At every position, the index chosen by `idxOf` is the index of the formula
of the relabelling that holds there. -/
lemma idxOf_eq_some (hfo : R.AllFO) (hqr : ∀ i, (R.form i).qrank ≤ k)
    {w : List A} {p : ℕ} (hp : p < w.length) {i₀ : R.Idx}
    (hg : MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form i₀)) :
    idxOf R k (tp k (w.take p)) w[p] (tp k (w.drop (p + 1))) = some i₀ := by
  have hlab : w[p]? = some w[p] := List.getElem?_eq_getElem hp
  have hex : ∃ i : R.Idx, ∀ (v : List A) (q : ℕ), q < v.length →
      tp k (v.take q) = tp k (w.take p) → v[q]? = some w[p] →
      tp k (v.drop (q + 1)) = tp k (w.drop (p + 1)) →
      MSO.Sat v (fun _ => q) (fun _ => ∅) (R.form i) := by
    refine ⟨i₀, fun v q hq h1 h2 h3 => ?_⟩
    refine (sat_const_iff_of_tp_split (R.form i₀) (hfo i₀) (hqr i₀) hp hq ?_ h1.symm h3.symm
      (fun _ => ∅) (fun _ => ∅)).mp hg
    rw [hlab, h2]
  rw [idxOf, dif_pos hex]
  congr 1
  have hsat := hex.choose_spec w p hp rfl hlab rfl
  obtain ⟨j, -, huniq⟩ := R.unique w p hp
  rw [huniq _ hsat, huniq _ hg]

/-- The bimachine computes the function of the relabelling. -/
theorem eval_bimach {f : List A → List B} (hfo : R.AllFO) (hqr : ∀ i, (R.form i).qrank ≤ k)
    (hk : 1 ≤ k) (hf : ∀ w, R.Relabels w (f w)) : (bimach R k).eval = f := by
  classical
  funext w
  have hstep : (bimach R k).eval w =
      ((List.range (w.length + 1)).map (fun i =>
        outOf R k (tp k (w.take i).dropLast, (w.take i).getLast?) (tp k (w.drop i)))).flatten := by
    show ((List.range (w.length + 1)).map (fun i =>
      outOf R k (strTrans (prefStep k) (w.take i) (tp k ([] : List A), none))
        (strTrans (sufStep k) (w.drop i).reverse (tp k ([] : List A))))).flatten = _
    congr 1
    exact List.map_congr_left (fun i _ => bimach_chunk R k w i)
  rw [hstep]
  rcases hf w with ⟨hw, hv⟩ | ⟨hw, g, hgsat, hv⟩
  · subst hw
    rw [hv]
    simp [outOf]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hne : tp (m + 1) w ≠ tp (m + 1) ([] : List A) := by
      intro h
      exact hw (eq_nil_of_tp_succ_eq_nil h)
    have hzero : outOf R (m + 1) (tp (m + 1) (w.take 0).dropLast, (w.take 0).getLast?)
        (tp (m + 1) (w.drop 0)) = [] := by
      simp only [List.take_zero, List.drop_zero, List.dropLast_nil, List.getLast?_nil]
      show (if tp (m + 1) w = tp (m + 1) ([] : List A) then R.emptyOut else []) = []
      rw [if_neg hne]
    have hsucc : ∀ p ∈ List.range w.length,
        outOf R (m + 1) (tp (m + 1) (w.take (p + 1)).dropLast, (w.take (p + 1)).getLast?)
          (tp (m + 1) (w.drop (p + 1))) = R.out (g p) := by
      intro p hp'
      have hp : p < w.length := List.mem_range.mp hp'
      have htake : w.take (p + 1) = w.take p ++ [w[p]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hp]
        rfl
      rw [htake, List.dropLast_concat, List.getLast?_concat]
      show (match idxOf R (m + 1) (tp (m + 1) (w.take p)) w[p] (tp (m + 1) (w.drop (p + 1))) with
        | none => []
        | some i => R.out i) = R.out (g p)
      rw [idxOf_eq_some hfo hqr hp (hgsat p hp)]
    rw [hv, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.flatten_cons, Function.comp_def]
    rw [hzero, List.nil_append]
    exact congrArg List.flatten (List.map_congr_left hsucc)

end FORelabBimach

/-- **One implication of Theorem `thm:fo-rational-functions`.**  A first-order relabelling is
computed by an aperiodic bimachine. -/
theorem isAperiodicBimachine_of_isFORelabelling {A B : Type} [Finite A] {f : List A → List B}
    (h : IsFORelabelling f) : IsAperiodicBimachine f := by
  classical
  obtain ⟨R, hfo, hf⟩ := h
  haveI := R.finIdx
  haveI : Fintype R.Idx := Fintype.ofFinite _
  set k := (Finset.univ.sup fun i => (R.form i).qrank) + 1 with hk
  have hqr : ∀ i, (R.form i).qrank ≤ k := by
    intro i
    exact le_trans (Finset.le_sup (f := fun i => (R.form i).qrank) (Finset.mem_univ i))
      (Nat.le_succ _)
  exact ⟨TpType A k × Option A, TpType A k, inferInstance, inferInstance,
    FORelabBimach.bimach R k,
    FORelabBimach.eval_bimach hfo hqr (by omega) hf,
    FORelabBimach.transAperiodic_prefStep k, FORelabBimach.transAperiodic_sufStep k⟩

end Lax314295Proofs.Transducers
