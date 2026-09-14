/-
The automaton of `k`-types, and the implication
"first-order definable ⇒ aperiodic dfa" of Theorem `thm:logic-aperiodic` of *Transducers*
(M. Bojańczyk).

"Define the set of states `Q` to be the set of possible `k`-types of strings in
`A*`.  As we have remarked before, this is a finite set.  By the congruence
property in the above lemma, we can define an automaton structure on this set,
since the `k`-type of `wa` depends only on the `k`-type of `w` and the letter
`a`.  By the aperiodicity property in the lemma, the automaton is aperiodic.
Finally, since the language is defined by a first-order formula of quantifier
rank at most `k`, it follows that strings that reach the same state cannot be
distinguished by the language."

The set of states is the whole type `TpType A k` of Definition `def:k-types`, which is
finite for a finite alphabet; on the types that are not realised by any string
the transition function is the identity, which is harmless both for the runs and
for aperiodicity.

The formula given by `FODefinable` may have free first-order variables (its
truth value does not depend on them, but this is only a semantic condition), so
the argument is run for the sentence obtained by quantifying them existentially;
this only increases the quantifier rank.  The empty string has to be treated
separately, because the existential closure of a formula is false in it; this is
harmless because, for `k ≥ 1`, the empty string is the only string of its
`k`-type.
-/
import Lax314295Proofs.Source.PartC.FOComp
import Lax916827Proofs.Source.PartC.MSOSyntax
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

variable {A : Type}

/-! ## Finiteness of the type of `k`-types -/

instance finite_tpType [Finite A] (k : ℕ) : Finite (TpType A k) := by
  induction k with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ k ih =>
      haveI := ih
      exact inferInstanceAs (Finite (Set (TpType A k × A × TpType A k)))

/-! ## The automaton -/

open scoped Classical in
/-- The transition function on `k`-types: appending a letter to any string of
the given type.  On the types that are not realised by any string it is the
identity. -/
noncomputable def tpStep (k : ℕ) (t : TpType A k) (a : A) : TpType A k :=
  if h : ∃ u : List A, tp k u = t then tp k (h.choose ++ [a]) else t

lemma tpStep_tp (k : ℕ) (u : List A) (a : A) : tpStep k (tp k u) a = tp k (u ++ [a]) := by
  have h : ∃ z : List A, tp k z = tp k u := ⟨u, rfl⟩
  rw [tpStep, dif_pos h]
  exact tp_congr k _ _ _ _ h.choose_spec rfl

lemma tpStep_of_not_realised {k : ℕ} {t : TpType A k} (h : ¬ ∃ u : List A, tp k u = t)
    (a : A) : tpStep k t a = t := by
  rw [tpStep, dif_neg h]

lemma strTrans_tpStep (k : ℕ) (u z : List A) :
    strTrans (tpStep k) z (tp k u) = tp k (u ++ z) := by
  induction z generalizing u with
  | nil => simp [strTrans]
  | cons a z ih =>
      show List.foldl (tpStep k) (tp k u) (a :: z) = _
      rw [List.foldl_cons, tpStep_tp]
      have := ih (u := u ++ [a])
      rw [show List.foldl (tpStep k) (tp k (u ++ [a])) z
        = strTrans (tpStep k) z (tp k (u ++ [a])) from rfl, this]
      simp

lemma strTrans_tpStep_of_not_realised {k : ℕ} {t : TpType A k}
    (h : ¬ ∃ u : List A, tp k u = t) (z : List A) : strTrans (tpStep k) z t = t := by
  induction z with
  | nil => rfl
  | cons a z ih =>
      show List.foldl (tpStep k) t (a :: z) = t
      rw [List.foldl_cons, tpStep_of_not_realised h]
      exact ih

/-- Iterating the state transformation of a string is the state transformation
of its powers. -/
lemma strTrans_iterate_npow {Q : Type} (δ : Q → A → Q) (w : List A) :
    ∀ n : ℕ, (strTrans δ w)^[n] = strTrans δ (npow w n) := by
  intro n
  induction n with
  | zero => funext q; rfl
  | succ n ih =>
      funext q
      rw [Function.iterate_succ_apply, ih]
      simp [strTrans, npow_succ, List.foldl_append]

/-- The automaton of `k`-types is aperiodic. -/
theorem transAperiodic_tpStep (k : ℕ) : TransAperiodic (tpStep (A := A) k) := by
  intro w
  refine ⟨tpBound k, fun n hn => ?_⟩
  rw [strTrans_iterate_npow, strTrans_iterate_npow]
  funext t
  by_cases ht : ∃ u : List A, tp k u = t
  · obtain ⟨u, rfl⟩ := ht
    rw [strTrans_tpStep, strTrans_tpStep]
    exact tp_congr k u u _ _ rfl (tp_npow_eq k w n (tpBound k) hn le_rfl)
  · rw [strTrans_tpStep_of_not_realised ht, strTrans_tpStep_of_not_realised ht]

/-- The dfa of `k`-types recognising a language that is a union of classes of
strings of the same `k`-type. -/
noncomputable def tpDFA (k : ℕ) (L : Language A) : DFA A (TpType A k) where
  step := tpStep k
  start := tp k []
  accept := {t | ∃ u : List A, tp k u = t ∧ u ∈ L}

lemma tpDFA_eval (k : ℕ) (L : Language A) (w : List A) : (tpDFA k L).eval w = tp k w := by
  have h : (tpDFA k L).eval w = strTrans (tpStep k) w (tp k []) := rfl
  rw [h, strTrans_tpStep]
  simp

/-! ## The easy implication of Theorem `thm:logic-aperiodic` -/

/-- The empty string is the only string of its `k`-type, as soon as `k ≥ 1`. -/
lemma eq_nil_of_tp_succ_eq_nil {k : ℕ} {w : List A}
    (h : tp (k + 1) w = tp (k + 1) ([] : List A)) : w = [] := by
  cases w with
  | nil => rfl
  | cons a z =>
      exfalso
      have hmem : (tp k ([] : List A), a, tp k z) ∈ tpSet k (a :: z) :=
        ⟨[], a, z, rfl, rfl⟩
      rw [(tp_succ_eq_iff_tpSet k (a :: z) []).mp h] at hmem
      obtain ⟨w₁, b, w₂, hw, -⟩ := hmem
      simp at hw

lemma MSO.isFO_closeFO : ∀ (is : List ℕ) {φ : MSO A}, φ.IsFO → (MSO.closeFO φ is).IsFO := by
  intro is
  induction is with
  | nil => exact fun h => h
  | cons i is ih => exact fun h => ih h

/-- **The easy implication of Theorem `thm:logic-aperiodic`.**  A first-order definable
language is recognised by an aperiodic dfa. -/
theorem aperiodic_dfa_of_foDefinable [Finite A] (L : Language A) (h : FODefinable L) :
    ∃ (σ : Type) (_ : Finite σ) (M : DFA A σ), TransAperiodic M.step ∧ M.accepts = L := by
  obtain ⟨φ, hfo, hsat⟩ := h
  -- the existential closure of `φ` is a sentence defining `L` on nonempty strings
  set ψ := MSO.closeFO φ φ.foVars with hψdef
  have hψfo : ψ.IsFO := MSO.isFO_closeFO _ hfo
  have hψfree : ψ.freeFO = ∅ := by
    refine Set.eq_empty_of_subset_empty ?_
    intro x hx
    obtain ⟨h1, h2⟩ := MSO.freeFO_closeFO φ φ.foVars hx
    exact h2 (MSO.freeFO_subset_foVars φ h1)
  set k := ψ.qrank + 1 with hk
  -- strings of the same `k`-type cannot be distinguished by `L`
  have hkey : ∀ u w : List A, tp k u = tp k w → u ∈ L → w ∈ L := by
    intro u w htp hu
    by_cases hune : u = []
    · subst hune
      rw [eq_nil_of_tp_succ_eq_nil htp.symm]
      exact hu
    · have hall : ∀ (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat u fo so φ :=
        fun fo so => (hsat u fo so).mpr hu
      have hsatψ : MSO.Sat u (fun _ => 0) (fun _ => ∅) ψ :=
        MSO.sat_closeFO_of_forall hune hall _ _ _
      have hsatψ' : MSO.Sat w (fun _ => 0) (fun _ => ∅) ψ :=
        (sat_iff_of_tp_eq htp ψ hψfo (Nat.le_succ _) hψfree _ _ _ _).mp hsatψ
      obtain ⟨fo', hfo'⟩ := MSO.exists_sat_of_sat_closeFO φ.foVars _ _ hsatψ'
      exact (hsat w fo' (fun _ => ∅)).mp hfo'
  refine ⟨TpType A k, inferInstance, tpDFA k L, transAperiodic_tpStep k, ?_⟩
  ext w
  constructor
  · intro hw
    have hw' : (tpDFA k L).eval w ∈ (tpDFA k L).accept := hw
    rw [tpDFA_eval] at hw'
    obtain ⟨u, hu, huL⟩ := hw'
    exact hkey u w hu huL
  · intro hw
    show (tpDFA k L).eval w ∈ (tpDFA k L).accept
    rw [tpDFA_eval]
    exact ⟨w, rfl, hw⟩

end Lax314295Proofs.Transducers
