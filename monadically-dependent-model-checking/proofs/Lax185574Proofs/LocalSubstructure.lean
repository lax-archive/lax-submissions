import Lax185574.LocalSubstructure
import Lax185574Proofs.DistanceFormulas
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
Proof that local formulas are evaluated in any induced substructure that
contains the ball of the right radius around the tuple.
-/

namespace Lax185574Proofs.LocalSubstructure

open FirstOrder FirstOrder.Language
open Lax185574.GaifmanGraph Lax185574.LocalFormulas
open Lax185574Proofs.DistanceFormulas

universe u v z

variable {L : Language.{u, v}} [L.IsRelational] {V : Type z} [L.Structure V]

/-- The inclusion of an induced substructure maps edges of its Gaifman
graph to edges of the Gaifman graph of the whole structure. -/
def inducedGaifmanHom (B : Set V) :
    @gaifmanGraph L B (induced B) →g (gaifmanGraph L (V := V)) where
  toFun := Subtype.val
  map_rel' := by
    intro a b h
    unfold gaifmanGraph at h ⊢
    rw [SimpleGraph.fromRel_adj] at h ⊢
    obtain ⟨hab, h⟩ := h
    refine ⟨fun e => hab (Subtype.ext e), ?_⟩
    rcases h with ⟨l, R, x, hx, ⟨i, hi⟩, ⟨j, hj⟩⟩ | ⟨l, R, x, hx, ⟨i, hi⟩, ⟨j, hj⟩⟩
    · exact Or.inl ⟨l, R, Subtype.val ∘ x, hx, ⟨i, by simp [hi]⟩, ⟨j, by simp [hj]⟩⟩
    · exact Or.inr ⟨l, R, Subtype.val ∘ x, hx, ⟨i, by simp [hi]⟩, ⟨j, by simp [hj]⟩⟩

theorem withinDist_map {W W' : Type*} {G : SimpleGraph W} {G' : SimpleGraph W'} (f : G →g G')
    {d : ℕ} {x y : W} (h : WithinDist G d x y) : WithinDist G' d (f x) (f y) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.map f, by rw [SimpleGraph.Walk.length_map]; exact hp⟩

theorem withinDist_of_induced (B : Set V) {d : ℕ} {x y : B}
    (h : WithinDist (@gaifmanGraph L B (induced B)) d x y) :
    WithinDist (gaifmanGraph L (V := V)) d x.val y.val := by
  exact withinDist_map (inducedGaifmanHom B) h

/-- Short walks from a centre survive in the induced substructure, as long
as the substructure contains the ball of radius `r` around the centre. -/
theorem withinDist_induced_of_withinDist (r : ℕ) (B : Set V) (c : B)
    (hB : {w | WithinDist (gaifmanGraph L (V := V)) r c.val w} ⊆ B) :
    ∀ d, d ≤ r → ∀ w : V, WithinDist (gaifmanGraph L (V := V)) d c.val w →
      ∃ hw : w ∈ B, WithinDist (@gaifmanGraph L B (induced B)) d c ⟨w, hw⟩ := by
  intro d
  induction d with
  | zero =>
    intro _ w ⟨p, hp⟩
    have : c.val = w := p.eq_of_length_eq_zero (by omega)
    subst this
    exact ⟨c.2, SimpleGraph.Walk.nil, le_refl _⟩
  | succ d ih =>
    intro hd w ⟨p, hp⟩
    by_cases hlen : p.length ≤ d
    · obtain ⟨hw, q, hq⟩ := ih (by omega) w ⟨p, hlen⟩
      exact ⟨hw, q, by omega⟩
    · -- the walk has length exactly `d + 1`: split off the last edge
      cases hrev : p.reverse with
      | nil =>
        have := congrArg SimpleGraph.Walk.length hrev
        rw [SimpleGraph.Walk.length_reverse] at this
        simp only [SimpleGraph.Walk.length_nil] at this
        omega
      | @cons _ m _ hwm q =>
        have hqlen : q.length = d := by
          have := congrArg SimpleGraph.Walk.length hrev
          rw [SimpleGraph.Walk.length_reverse] at this
          simp only [SimpleGraph.Walk.length_cons] at this
          omega
        obtain ⟨hm, q', hq'⟩ := ih (by omega) m ⟨q.reverse, by simp [hqlen]⟩
        unfold gaifmanGraph at hwm
        rw [SimpleGraph.fromRel_adj] at hwm
        obtain ⟨hne, hrel⟩ := hwm
        obtain ⟨l, R, x, hx, hwx, hmx⟩ : ∃ (l : ℕ) (R : L.Relations l) (x : Fin l → V),
            Structure.RelMap R x ∧ w ∈ Set.range x ∧ m ∈ Set.range x := by
          rcases hrel with ⟨l, R, x, hx, h1, h2⟩ | ⟨l, R, x, hx, h1, h2⟩
          · exact ⟨l, R, x, hx, h1, h2⟩
          · exact ⟨l, R, x, hx, h2, h1⟩
        obtain ⟨q'', hq''⟩ := withinDist_of_induced (L := L) B ⟨q', hq'⟩
        -- every entry of the witnessing tuple is close to the centre
        have entry_mem : ∀ t, x t ∈ B := by
          intro t
          apply hB
          by_cases hxt : m = x t
          · exact ⟨q''.copy rfl hxt, by simp only [SimpleGraph.Walk.length_copy]; omega⟩
          · have hadj : (gaifmanGraph L (V := V)).Adj m (x t) := by
              unfold gaifmanGraph
              rw [SimpleGraph.fromRel_adj]
              exact ⟨hxt, Or.inl ⟨l, R, x, hx, hmx, ⟨t, rfl⟩⟩⟩
            exact ⟨q''.concat hadj, by simp only [SimpleGraph.Walk.length_concat]; omega⟩
        obtain ⟨tw, htw⟩ := hwx
        have hw : w ∈ B := htw ▸ entry_mem tw
        have hadjB : (@gaifmanGraph L B (induced B)).Adj ⟨m, hm⟩ ⟨w, hw⟩ := by
          unfold gaifmanGraph
          rw [SimpleGraph.fromRel_adj]
          refine ⟨fun e => hne (congrArg Subtype.val e).symm, Or.inl ⟨l, R,
            fun t => ⟨x t, entry_mem t⟩, hx, ?_, ⟨tw, Subtype.ext htw⟩⟩⟩
          obtain ⟨tm, htm⟩ := hmx
          exact ⟨tm, Subtype.ext htm⟩
        exact ⟨hw, q'.concat hadjB, by simp only [SimpleGraph.Walk.length_concat]; omega⟩

/-- In a relational language, a term evaluated at elements of `B` is the
image of its evaluation in the induced substructure. -/
theorem realize_term_induced (B : Set V) {β : Type*} (t : L.Term β) (e : β → B) :
    t.realize (Subtype.val ∘ e) = (@Term.realize L B (induced B) β e t).val := by
  cases t with
  | var x => rfl
  | func f _ => exact isEmptyElim f

/-- For `y` in `B` and a centre whose ball of radius `r` lies in `B`, the
distance at most `s ≤ r` is the same in the Gaifman graphs of `A` and
`A[B]`. -/
theorem withinDist_induced_iff (r s : ℕ) (hs : s ≤ r) (B : Set V) (c y : B)
    (hB : {w | WithinDist (gaifmanGraph L (V := V)) r c.val w} ⊆ B) :
    WithinDist (@gaifmanGraph L B (induced B)) s c y ↔
      WithinDist (gaifmanGraph L (V := V)) s c.val y.val := by
  refine ⟨withinDist_of_induced B, fun h => ?_⟩
  obtain ⟨_, h'⟩ := withinDist_induced_of_withinDist r B c hB s hs y.val h
  exact h'

variable [Finite (Σ l, L.Relations l)]

theorem realize_iff_realize_induced_bounded (r k : ℕ) (B : Set V) (a : Fin k → B)
    (hB : ball L r (Subtype.val ∘ a) ⊆ B) :
    ∀ {n : ℕ} (φ : L.BoundedFormula (Fin k) n), IsLocal r φ → ∀ xs : Fin n → B,
      (φ.Realize (Subtype.val ∘ a) (Subtype.val ∘ xs) ↔
        @BoundedFormula.Realize L B (induced B) _ _ φ a xs) := by
  have hball : ∀ i, {w | WithinDist (gaifmanGraph L (V := V)) r (a i).val w} ⊆ B :=
    fun i w hw => hB ⟨i, hw⟩
  have hguard : ∀ {n s : ℕ}, s ≤ r → ∀ (xs : Fin (n + 1) → B),
      (@BoundedFormula.Realize L B (induced B) _ _ (ballGuard L k s n) a xs ↔
        (ballGuard L k s n).Realize (Subtype.val ∘ a) (Subtype.val ∘ xs)) := by
    intro n s hs xs
    rw [@realize_ballGuard L B (induced B), realize_ballGuard]
    exact exists_congr fun i => withinDist_induced_iff r s hs B (a i) _ (hball i)
  have hcomp : ∀ {n : ℕ} (xs : Fin n → B) (y : B),
      (Subtype.val ∘ Fin.snoc xs y : Fin (n + 1) → V) = Fin.snoc (Subtype.val ∘ xs) y.val := by
    intro n xs y
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  intro n φ hφ
  induction hφ with
  | falsum => intro xs; rfl
  | equal t₁ t₂ =>
    intro xs
    simp only [BoundedFormula.Realize]
    have h := fun t : L.Term (Fin k ⊕ Fin _) =>
      realize_term_induced B t (Sum.elim a xs)
    rw [Sum.comp_elim] at h
    rw [h, h]
    exact Subtype.ext_iff.symm
  | rel R ts =>
    intro xs
    simp only [BoundedFormula.Realize]
    have h := fun t : L.Term (Fin k ⊕ Fin _) =>
      realize_term_induced B t (Sum.elim a xs)
    rw [Sum.comp_elim] at h
    simp only [h]
    rfl
  | imp _ _ ih₁ ih₂ =>
    intro xs
    simp only [BoundedFormula.realize_imp]
    rw [ih₁, ih₂]
  | @all n s φ hs _ ih =>
    intro xs
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp]
    constructor
    · intro h y hy
      rw [← ih]
      rw [hguard hs] at hy
      rw [hcomp] at hy ⊢
      exact h _ hy
    · intro h y hy
      have hy' : y ∈ B := by
        have hy2 := hy
        rw [realize_ballGuard] at hy2
        obtain ⟨i, hi⟩ := hy2
        simp only [Fin.snoc_last, Function.comp_apply] at hi
        obtain ⟨p, hp⟩ := hi
        exact hball i ⟨p, by omega⟩
      have key := h ⟨y, hy'⟩ (by rw [hguard hs, hcomp]; exact hy)
      rw [← ih, hcomp] at key
      exact key
  | @ex n s φ hs _ ih =>
    intro xs
    simp only [BoundedFormula.realize_ex, BoundedFormula.realize_inf]
    constructor
    · rintro ⟨y, hy, hφ⟩
      have hy' : y ∈ B := by
        have hy2 := hy
        rw [realize_ballGuard] at hy2
        obtain ⟨i, hi⟩ := hy2
        simp only [Fin.snoc_last, Function.comp_apply] at hi
        obtain ⟨p, hp⟩ := hi
        exact hball i ⟨p, by omega⟩
      refine ⟨⟨y, hy'⟩, by rw [hguard hs, hcomp]; exact hy, ?_⟩
      rw [← ih, hcomp]
      exact hφ
    · rintro ⟨y, hy, hφ⟩
      rw [hguard hs, hcomp] at hy
      rw [← ih, hcomp] at hφ
      exact ⟨y, hy, hφ⟩

/--
---
conclusion: Lax185574.LocalSubstructure.realize_iff_realize_induced
---
An `r`-local formula holds of a tuple in a structure if and only if it
holds of the tuple in an induced substructure that contains the ball of
radius `r` around the tuple. The quantifiers of the formula are guarded by
balls of radius at most `r` around the tuple, and these balls are the same
in the structure and in the substructure, since a walk of length at most
`r` from the tuple uses only relation tuples whose entries lie in the ball.
-/
theorem realize_iff_realize_induced (L : Language.{u, v}) [L.IsRelational]
    [Finite (Σ l, L.Relations l)] (r k : ℕ) (φ : L.Formula (Fin k)) (hφ : IsLocal r φ)
    (V : Type z) [L.Structure V] (B : Set V) (a : Fin k → B) :
    ball L r (Subtype.val ∘ a) ⊆ B →
      (φ.Realize (Subtype.val ∘ a) ↔ @Formula.Realize L B (induced B) _ φ a) := by
  intro hB
  have := realize_iff_realize_induced_bounded r k B a hB φ hφ default
  unfold Formula.Realize
  convert this using 2

end Lax185574Proofs.LocalSubstructure
