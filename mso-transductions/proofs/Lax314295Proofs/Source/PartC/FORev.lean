/- First-order definable languages: sentences, invariance under `k`-types, and closure under
reversal.  These are the tools of Section *The first-order fragment* of *Transducers* (M. Bojańczyk)
that are needed for Theorem `thm:fo-rational-functions`, on top of Theorem `thm:logic-aperiodic`.

Three things are proved here.

* Every first-order definable language is defined by a first-order *sentence*
  (`Transducers.FODefinable.exists_sentence`): the formula given by
  `FODefinable` may have free variables, whose valuation is irrelevant, so it
  can be closed existentially; the empty string, on which an existential
  closure is always false, is treated separately.
* A language is first-order definable as soon as it is a union of classes of
  strings with the same `k`-type, and conversely a first-order definable
  language is such a union for a suitable `k`
  (`Transducers.foDefinable_of_tp_invariant`,
  `Transducers.exists_tp_invariant_of_foDefinable`).  Both directions are
  Theorem `thm:logic-aperiodic` together with the automaton of `k`-types.
* The `k`-type of the reverse of a string is determined by the `k`-type of the
  string (`Transducers.tp_reverse`), because the definition of a type is
  symmetric.  Consequently first-order definable languages are closed under
  reversal (`Transducers.FODefinable.reverse`), which is what makes the suffix
  automaton of a bimachine describable in first-order logic.
-/
import Lax314295Proofs.Source.PartC.FOTypeDFA
import Lax314295Proofs.Source.PartC.FOMealy
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

variable {A : Type}

/-! ## First-order definability by a sentence -/

namespace MSO

/-- The sentence saying that the string is not empty. -/
def nonemptyF : MSO A := exFO 0 (le 0 0)

lemma isFO_nonemptyF : (nonemptyF : MSO A).IsFO := trivial

lemma freeFO_nonemptyF : (nonemptyF : MSO A).freeFO = ∅ := by
  ext i
  simp [nonemptyF, freeFO]

lemma sat_nonemptyF (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    Sat w fo so (nonemptyF : MSO A) ↔ w ≠ [] := by
  constructor
  · rintro ⟨p, hp, -⟩ rfl
    simp at hp
  · intro hw
    refine ⟨0, ?_, le_rfl⟩
    cases w with
    | nil => exact absurd rfl hw
    | cons a u => simp

end MSO

open MSO

/-- A first-order definable language is defined by a first-order *sentence*. -/
theorem FODefinable.exists_sentence {L : Language A} (h : FODefinable L) :
    ∃ φ : MSO A, φ.IsFO ∧ φ.freeFO = ∅ ∧
      ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat w fo so φ ↔ w ∈ L := by
  classical
  obtain ⟨φ₀, hfo, hsat⟩ := h
  set ψ := MSO.and (MSO.closeSelf φ₀) MSO.nonemptyF with hψ
  have hψfo : ψ.IsFO := ⟨MSO.isFO_closeSelf hfo, isFO_nonemptyF⟩
  have hψfree : ψ.freeFO = ∅ := by
    rw [hψ]
    show (MSO.closeSelf φ₀).freeFO ∪ (nonemptyF : MSO A).freeFO = ∅
    rw [MSO.freeFO_closeSelf, freeFO_nonemptyF]
    simp
  have hψsat : ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      MSO.Sat w fo so ψ ↔ (w ≠ [] ∧ w ∈ L) := by
    intro w fo so
    show (MSO.Sat w fo so (MSO.closeSelf φ₀) ∧ MSO.Sat w fo so nonemptyF) ↔ _
    rw [sat_nonemptyF]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      obtain ⟨fo', hfo'⟩ := MSO.exists_sat_of_sat_closeFO φ₀.foVars fo so h1
      exact (hsat w fo' so).mp hfo'
    · rintro ⟨h1, h2⟩
      exact ⟨MSO.sat_closeFO_of_forall h1 (fun fo' so' => (hsat w fo' so').mpr h2) _ _ _, h1⟩
  by_cases hnil : [] ∈ L
  · refine ⟨MSO.or ψ (MSO.not MSO.nonemptyF), ⟨hψfo, isFO_nonemptyF (A := A)⟩, ?_, ?_⟩
    · show ψ.freeFO ∪ (nonemptyF : MSO A).freeFO = ∅
      rw [hψfree, freeFO_nonemptyF]; simp
    · intro w fo so
      show (MSO.Sat w fo so ψ ∨ ¬ MSO.Sat w fo so nonemptyF) ↔ w ∈ L
      rw [hψsat, sat_nonemptyF]
      constructor
      · rintro (⟨-, h⟩ | h)
        · exact h
        · rw [not_not.mp h]; exact hnil
      · intro hw
        by_cases hwn : w = []
        · exact Or.inr (by simp [hwn])
        · exact Or.inl ⟨hwn, hw⟩
  · refine ⟨ψ, hψfo, hψfree, ?_⟩
    intro w fo so
    rw [hψsat]
    constructor
    · exact fun h => h.2
    · intro hw
      refine ⟨?_, hw⟩
      rintro rfl
      exact hnil hw

/-! ## First-order definability and `k`-types -/

/-- A first-order definable language is a union of classes of strings with the
same `k`-type, for `k` the quantifier rank of a defining sentence. -/
theorem exists_tp_invariant_of_foDefinable {L : Language A} (h : FODefinable L) :
    ∃ k : ℕ, ∀ u v : List A, tp k u = tp k v → (u ∈ L ↔ v ∈ L) := by
  obtain ⟨φ, hfo, hfree, hsat⟩ := FODefinable.exists_sentence h
  refine ⟨φ.qrank, fun u v huv => ?_⟩
  rw [← hsat u (fun _ => 0) (fun _ => ∅), ← hsat v (fun _ => 0) (fun _ => ∅)]
  exact sat_iff_of_tp_eq huv φ hfo le_rfl hfree _ _ _ _

/-- A language that is a union of classes of strings with the same `k`-type is
first-order definable: it is recognised by the (aperiodic) automaton of
`k`-types. -/
theorem foDefinable_of_tp_invariant [Finite A] (k : ℕ) (L : Language A)
    (h : ∀ u v : List A, tp k u = tp k v → (u ∈ L ↔ v ∈ L)) : FODefinable L := by
  have hacc : (tpDFA k L).accepts = L := by
    ext w
    constructor
    · intro hw
      have hw' : (tpDFA k L).eval w ∈ (tpDFA k L).accept := hw
      rw [tpDFA_eval] at hw'
      obtain ⟨u, hu, huL⟩ := hw'
      exact (h u w hu).mp huL
    · intro hw
      show (tpDFA k L).eval w ∈ (tpDFA k L).accept
      rw [tpDFA_eval]
      exact ⟨w, rfl, hw⟩
  have := foDefinable_of_aperiodic_dfa (tpDFA k L) (transAperiodic_tpStep k)
  rwa [hacc] at this

/-! ## Reversal -/

/-- The set of triples of the reversed type. -/
def tpRevSet (k : ℕ) (rec : TpType A k → TpType A k)
    (T : Set (TpType A k × A × TpType A k)) : Set (TpType A k × A × TpType A k) :=
  {u : TpType A k × A × TpType A k |
    ∃ (t₁ : TpType A k) (a : A) (t₂ : TpType A k),
      (t₁, a, t₂) ∈ T ∧ u = (rec t₂, a, rec t₁)}

/-- The `k`-type of the reverse of a string, as a function of its `k`-type. -/
def tpRev : (k : ℕ) → TpType A k → TpType A k
  | 0, t => t
  | k + 1, T => tpRevSet k (tpRev k) T

lemma reverse_eq_of_reverse_eq {w x y : List A} {a : A} (h : w.reverse = x ++ a :: y) :
    w = y.reverse ++ a :: x.reverse := by
  have := congrArg List.reverse h
  simpa using this

/-- The `k`-type of a string determines the `k`-type of its reverse. -/
theorem tp_reverse : ∀ (k : ℕ) (w : List A), tp k w.reverse = tpRev k (tp k w) := by
  intro k
  induction k with
  | zero => intro w; rfl
  | succ k ih =>
      intro w
      show tpSet k w.reverse = tpRevSet k (tpRev k) (tpSet k w)
      ext t
      constructor
      · rintro ⟨x, a, y, hx, rfl⟩
        refine ⟨tp k y.reverse, a, tp k x.reverse, ?_, ?_⟩
        · exact ⟨y.reverse, a, x.reverse, reverse_eq_of_reverse_eq hx, rfl⟩
        · have e1 : tpRev k (tp k x.reverse) = tp k x := by
            rw [← ih x.reverse]; simp
          have e2 : tpRev k (tp k y.reverse) = tp k y := by
            rw [← ih y.reverse]; simp
          rw [e1, e2]
      · rintro ⟨t₁, a, t₂, ⟨w₁, b, w₂, hw, heq⟩, rfl⟩
        simp only [Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        subst e2
        refine ⟨w₂.reverse, a, w₁.reverse, ?_, ?_⟩
        · rw [hw]; simp
        · rw [e1, e3, ih w₁, ih w₂]

/-- First-order definable languages are closed under reversal. -/
theorem FODefinable.reverse [Finite A] {L : Language A} (h : FODefinable L) :
    FODefinable {u : List A | u.reverse ∈ L} := by
  obtain ⟨k, hk⟩ := exists_tp_invariant_of_foDefinable h
  refine foDefinable_of_tp_invariant k _ (fun u v huv => ?_)
  exact hk u.reverse v.reverse (by rw [tp_reverse, tp_reverse, huv])

/-! ## The state languages of an aperiodic automaton -/

/-- For an aperiodic transition function, the set of strings that lead from a
given state to a given state is first-order definable. -/
theorem foDefinable_state_lang [Finite A] {Q : Type} [Finite Q] (δ : Q → A → Q)
    (h : TransAperiodic δ) (q₀ q : Q) :
    FODefinable {u : List A | strTrans δ u q₀ = q} := by
  have hM := foDefinable_of_aperiodic_dfa (⟨δ, q₀, {q}⟩ : DFA A Q) h
  have hacc : (⟨δ, q₀, {q}⟩ : DFA A Q).accepts = {u : List A | strTrans δ u q₀ = q} := by
    ext u
    show (⟨δ, q₀, {q}⟩ : DFA A Q).eval u ∈ ({q} : Set Q) ↔ _
    show List.foldl δ q₀ u = q ↔ _
    rfl
  rwa [hacc] at hM

/-- For an aperiodic transition function, the set of strings whose *reverse*
leads from a given state to a given state is first-order definable. -/
theorem foDefinable_rev_state_lang [Finite A] {Q : Type} [Finite Q] (δ : Q → A → Q)
    (h : TransAperiodic δ) (q₀ q : Q) :
    FODefinable {u : List A | strTrans δ u.reverse q₀ = q} :=
  FODefinable.reverse (foDefinable_state_lang δ h q₀ q)

end Lax314295Proofs.Transducers
