import Lax185574.LocalFormulas
import Mathlib.Tactic.FinCases

/-!
Semantics of the adjacency and distance formulas of `Lax185574.LocalFormulas`.
The formula `adj_σ` defines adjacency in the Gaifman graph, and the formula
`dist(x₁, x₂) ≤ r` holds exactly if a walk of length at most `r` joins the two
elements.
-/

open FirstOrder FirstOrder.Language Lax185574.GaifmanGraph Lax185574.LocalFormulas

universe u v w

namespace Lax185574Proofs.DistanceFormulas

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

theorem realize_instantiate {β : Type*} {j n : ℕ} (φ : L.Formula (Fin j))
    (t : Fin j → L.Term (β ⊕ Fin n)) (v : β → M) (xs : Fin n → M) :
    (instantiate φ t).Realize v xs ↔ φ.Realize (fun i => (t i).realize (Sum.elim v xs)) := by
  unfold instantiate
  rw [BoundedFormula.realize_relabel, BoundedFormula.realize_subst]
  unfold Formula.Realize
  have h1 : (xs ∘ Fin.castAdd 0 : Fin n → M) = xs := by funext i; rfl
  have h2 : ((xs ∘ Fin.natAdd n) : Fin 0 → M) = default := Subsingleton.elim _ _
  simp only [h1, h2, Function.comp_id]

theorem realize_adjVia {l : ℕ} (R : L.Relations l) (a b : M) :
    (adjVia R).Realize ![a, b] ↔
      ∃ x : Fin l → M, Structure.RelMap R x ∧ ∃ i j, i ≠ j ∧ x i = a ∧ x j = b := by
  unfold adjVia
  split_ifs with hl
  · rw [BoundedFormula.realize_exs]
    simp only [BoundedFormula.realize_iSup]
    constructor
    · rintro ⟨xs, π, h⟩
      refine ⟨_, h, π.symm ⟨0, by omega⟩, π.symm ⟨1, by omega⟩, ?_, ?_, ?_⟩
      · simp
      · simp [adjSlot]
      · simp [adjSlot]
    · rintro ⟨x, hx, i, j, hij, rfl, rfl⟩
      let σ : Equiv.Perm (Fin l) := Equiv.swap i ⟨0, by omega⟩
      have hσj : σ j ≠ ⟨0, by omega⟩ := by
        intro h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact hij h.symm
      let τ : Equiv.Perm (Fin l) := Equiv.swap (σ j) ⟨1, by omega⟩
      let π : Equiv.Perm (Fin l) := σ.trans τ
      have hπi : π i = ⟨0, by omega⟩ := by
        simp only [π, Equiv.trans_apply, σ, Equiv.swap_apply_left, τ]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => hσj (by simpa [σ] using h.symm)
        · simp
      have hπj : π j = ⟨1, by omega⟩ := by
        simp [π, τ]
      refine ⟨fun p => x (π.symm ⟨p.val + 2, by omega⟩), π, ?_⟩
      simp only [BoundedFormula.Realize]
      convert hx using 1
      funext m
      unfold adjSlot
      split_ifs with hm
      · simp only [Term.realize_var, Sum.elim_inl]
        rcases (show (π m).val = 0 ∨ (π m).val = 1 by omega) with h | h
        · have : π m = ⟨0, by omega⟩ := Fin.ext h
          have hm' : m = i := π.injective (this.trans hπi.symm)
          subst hm'
          simp [h]
        · have : π m = ⟨1, by omega⟩ := Fin.ext h
          have hm' : m = j := π.injective (this.trans hπj.symm)
          subst hm'
          simp [h]
      · simp only [Term.realize_var, Sum.elim_inr]
        congr 1
        apply π.injective
        simp only [Equiv.apply_symm_apply]
        ext; simp; omega
  · simp only [Formula.Realize, BoundedFormula.realize_bot, false_iff]
    rintro ⟨x, -, i, j, hij, -, -⟩
    apply hij
    ext; omega

theorem realize_adjFormula [Finite (Σ l, L.Relations l)] (a b : M) :
    (adjFormula L).Realize ![a, b] ↔ (gaifmanGraph L (V := M)).Adj a b := by
  unfold adjFormula
  unfold Formula.Realize
  rw [BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_iSup]
  simp only [Term.realize_var, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold gaifmanGraph
  rw [SimpleGraph.fromRel_adj]
  have key : ∀ (R : Σ l, L.Relations l), (adjVia R.2).Realize ![a, b] ↔
      ∃ x : Fin R.1 → M, Structure.RelMap R.2 x ∧ ∃ i j, i ≠ j ∧ x i = a ∧ x j = b :=
    fun R => realize_adjVia R.2 a b
  simp only [Formula.Realize] at key
  simp only [key]
  constructor
  · rintro ⟨hab, ⟨l, R⟩, x, hx, i, j, -, rfl, rfl⟩
    exact ⟨hab, Or.inl ⟨l, R, x, hx, ⟨i, rfl⟩, ⟨j, rfl⟩⟩⟩
  · rintro ⟨hab, h⟩
    refine ⟨hab, ?_⟩
    rcases h with ⟨l, R, x, hx, ⟨i, hi⟩, ⟨j, hj⟩⟩ | ⟨l, R, x, hx, ⟨i, hi⟩, ⟨j, hj⟩⟩
    · refine ⟨⟨l, R⟩, x, hx, i, j, ?_, hi, hj⟩
      rintro rfl; exact hab (hi.symm.trans hj)
    · refine ⟨⟨l, R⟩, x, hx, j, i, ?_, hj, hi⟩
      rintro rfl; exact hab (hj.symm.trans hi)

/-- Walk sequences with equal-or-adjacent steps. -/
def StepSeq (G : SimpleGraph M) (r : ℕ) (a b : M) : Prop :=
  ∃ w : Fin (r + 1) → M, w 0 = a ∧ w (Fin.last r) = b ∧
    ∀ i : Fin r, w i.castSucc = w i.succ ∨ G.Adj (w i.castSucc) (w i.succ)

theorem stepSeq_succ (G : SimpleGraph M) (r : ℕ) (a b : M) :
    StepSeq G (r + 1) a b ↔ ∃ c, (a = c ∨ G.Adj a c) ∧ StepSeq G r c b := by
  constructor
  · rintro ⟨w, h0, hl, hs⟩
    refine ⟨w 1, ?_, Fin.tail w, rfl, ?_, fun i => ?_⟩
    · have := hs 0; simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, h0] at this; exact this
    · show w (Fin.last r).succ = b; rw [Fin.succ_last]; exact hl
    · have := hs i.succ; rw [← Fin.succ_castSucc] at this; exact this
  · rintro ⟨c, hc, w, h0, hl, hs⟩
    refine ⟨Fin.cons a w, rfl, ?_, fun i => ?_⟩
    · rw [← Fin.succ_last, Fin.cons_succ]; exact hl
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one, h0]
        exact hc
      · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]; exact hs i

theorem stepSeq_iff (G : SimpleGraph M) (r : ℕ) (a b : M) :
    StepSeq G r a b ↔ WithinDist G r a b := by
  induction r generalizing a with
  | zero =>
    constructor
    · rintro ⟨w, h0, hl, -⟩
      have : a = b := by rw [← h0, ← hl]; rfl
      subst this; exact ⟨SimpleGraph.Walk.nil, le_refl _⟩
    · rintro ⟨p, hp⟩
      have : a = b := p.eq_of_length_eq_zero (by omega)
      subst this
      exact ⟨fun _ => a, rfl, rfl, fun i => i.elim0⟩
  | succ r ih =>
    rw [stepSeq_succ]
    constructor
    · rintro ⟨c, hc | hc, h⟩
      · subst hc; obtain ⟨p, hp⟩ := (ih a).1 h; exact ⟨p, by omega⟩
      · obtain ⟨p, hp⟩ := (ih c).1 h; exact ⟨SimpleGraph.Walk.cons hc p, by simp; omega⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => exact ⟨_, Or.inl rfl, (ih _).2 ⟨SimpleGraph.Walk.nil, by simp⟩⟩
      | cons h p => exact ⟨_, Or.inr h, (ih _).2 ⟨p, by simp at hp; omega⟩⟩

theorem realize_distFormula [Finite (Σ l, L.Relations l)] (r : ℕ) (a b : M) :
    (distFormula L r).Realize ![a, b] ↔ WithinDist (gaifmanGraph L (V := M)) r a b := by
  rw [← stepSeq_iff]
  unfold distFormula
  rw [BoundedFormula.realize_exs]
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual,
    BoundedFormula.realize_iInf, BoundedFormula.realize_sup]
  have hadj : ∀ (xs : Fin r → M) (i : Fin r),
      (instantiate (adjFormula L) ![walkVertex (L := L) i.castSucc, walkVertex i.succ]).Realize
        ![a, b] xs ↔
      (gaifmanGraph L (V := M)).Adj ((walkVertex (L := L) i.castSucc).realize (Sum.elim ![a, b] xs))
        ((walkVertex (L := L) i.succ).realize (Sum.elim ![a, b] xs)) := by
    intro xs i
    rw [realize_instantiate, ← realize_adjFormula]
    congr! 1
    funext m
    fin_cases m <;> rfl
  simp only [hadj]
  have hw : ∀ (xs : Fin r → M) (i : Fin (r + 1)),
      (walkVertex (L := L) i).realize (Sum.elim ![a, b] xs) = (Fin.cons a xs : Fin (r + 1) → M) i := by
    intro xs i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [walkVertex]
    · simp [walkVertex]
  simp only [hw, Term.realize_var, Sum.elim_inl]
  constructor
  · rintro ⟨xs, hl, hs⟩
    exact ⟨Fin.cons a xs, rfl, by simpa using hl, hs⟩
  · rintro ⟨w, h0, hl, hs⟩
    refine ⟨Fin.tail w, ?_, ?_⟩
    · have : (Fin.cons a (Fin.tail w) : Fin (r + 1) → M) = w := by
        rw [← h0]; exact Fin.cons_self_tail w
      rw [this]; simpa using hl
    · have : (Fin.cons a (Fin.tail w) : Fin (r + 1) → M) = w := by
        rw [← h0]; exact Fin.cons_self_tail w
      rw [this]; exact hs

/-- The guard `y ∈ Ball_s(x̄)` holds exactly if the newly bound variable is
within distance `s` of some free variable. -/
theorem realize_ballGuard [Finite (Σ l, L.Relations l)] (k s n : ℕ) (v : Fin k → M)
    (xs : Fin (n + 1) → M) :
    (ballGuard L k s n).Realize v xs ↔
      ∃ i, WithinDist (gaifmanGraph L (V := M)) s (v i) (xs (Fin.last n)) := by
  unfold ballGuard
  rw [BoundedFormula.realize_iSup]
  refine exists_congr fun i => ?_
  rw [realize_instantiate, ← realize_distFormula]
  congr! 1
  funext m
  fin_cases m <;> rfl

end Lax185574Proofs.DistanceFormulas
