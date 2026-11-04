import Lax185574Proofs.DefinableFlipFormula
import Lax185574.GaifmanGraph
import Lax185574.PhiPsiPatterns
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
A first-order formula expressing distance at most `r` in a definable
flip: `φ(z̄ x, y)` holds if and only if `y` is within distance `r` of `x`
in `G ⊕ (z̄, R)`.
-/

namespace Lax185574Proofs.FlipDistanceFormula

open FirstOrder FirstOrder.Language
open Lax185574.AtomicTypes Lax185574.DefinableFlips Lax185574.GaifmanGraph

universe u

variable {V : Type u}

/-- Distance at most `r` is witnessed by a sequence of `r + 1` vertices in
which consecutive vertices are equal or adjacent. -/
theorem withinDist_iff_chain (H : SimpleGraph V) (r : ℕ) (x y : V) :
    WithinDist H r x y ↔ ∃ ws : Fin (r + 1) → V, ws 0 = x ∧ ws (Fin.last r) = y ∧
      ∀ i : Fin r, ws i.castSucc = ws i.succ ∨ H.Adj (ws i.castSucc) (ws i.succ) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun i => w.getVert i, w.getVert_zero, w.getVert_of_length_le hw, fun i => ?_⟩
    by_cases hi : (i : ℕ) < w.length
    · right
      simpa using w.adj_getVert_succ hi
    · left
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [w.getVert_of_length_le (by omega), w.getVert_of_length_le (by omega)]
  · rintro ⟨ws, h0, hr, hstep⟩
    have key : ∀ k (hk : k ≤ r), WithinDist H k x (ws ⟨k, by omega⟩) := by
      intro k
      induction k with
      | zero =>
        intro _
        have h0' : x = ws ⟨0, by omega⟩ := h0.symm
        exact ⟨(SimpleGraph.Walk.nil : H.Walk x x).copy rfl h0',
          by simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_nil, le_refl]⟩
      | succ k ih =>
        intro hk
        obtain ⟨p, hp⟩ := ih (by omega)
        rcases hstep ⟨k, by omega⟩ with h | h
        · refine ⟨p.copy rfl h, ?_⟩
          rw [SimpleGraph.Walk.length_copy]; omega
        · refine ⟨p.concat h, ?_⟩
          rw [SimpleGraph.Walk.length_concat]; omega
    have := key r le_rfl
    rwa [show (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r from rfl, hr] at this

/-- The formula `φ(z̄ x, y)` saying that `y` is within distance `r` of `x`
in the flip whose edges are defined by `E(x, y, z̄)`. -/
noncomputable def distFormula {s : ℕ} (r : ℕ) (E : Language.graph.Formula (Fin 2 ⊕ Fin s)) :
    Language.graph.Formula (Fin (s + 1) ⊕ Fin 1) :=
  let w : Fin (r + 1) → Language.graph.Term ((Fin (s + 1) ⊕ Fin 1) ⊕ Fin (r + 1)) :=
    fun i => Term.var (Sum.inr i)
  let x : Language.graph.Term ((Fin (s + 1) ⊕ Fin 1) ⊕ Fin (r + 1)) :=
    Term.var (Sum.inl (Sum.inl (Fin.last s)))
  let y : Language.graph.Term ((Fin (s + 1) ⊕ Fin 1) ⊕ Fin (r + 1)) :=
    Term.var (Sum.inl (Sum.inr 0))
  let step : Fin r → Language.graph.BoundedFormula (Fin (s + 1) ⊕ Fin 1) (r + 1) := fun i =>
    (w i.castSucc).bdEqual (w i.succ) ⊔
      BoundedFormula.relabel
        (Sum.elim (fun j : Fin 2 => Sum.inr (![i.castSucc, i.succ] j))
          (fun j : Fin s => Sum.inl (Sum.inl (Fin.castSucc j)))) E
  BoundedFormula.exs ((w 0).bdEqual x ⊓ (w (Fin.last r)).bdEqual y ⊓ BoundedFormula.iInf step)

theorem holds_distFormula {s : ℕ} (r : ℕ) (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (E : Language.graph.Formula (Fin 2 ⊕ Fin s))
    (hE : ∀ (G : SimpleGraph V) (p : Fin s → V) (x y : V),
      (flipOver G p R).Adj x y ↔
        @Formula.Realize Language.graph V G.structure _ E (Sum.elim ![x, y] p))
    (G : SimpleGraph V) (a : Fin (s + 1) → V) (c : V) :
    Lax185574.PhiPsiPatterns.Holds G (distFormula r E) a c ↔
      WithinDist (flipOver G (a ∘ Fin.castSucc) R) r (a (Fin.last s)) c := by
  let _ := G.structure
  rw [withinDist_iff_chain]
  unfold Lax185574.PhiPsiPatterns.Holds distFormula
  dsimp only
  rw [BoundedFormula.realize_exs]
  refine exists_congr fun ws => ?_
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual, Term.realize_var,
    Sum.elim_inr, Sum.elim_inl, BoundedFormula.realize_iInf, BoundedFormula.realize_sup,
    BoundedFormula.realize_relabel]
  rw [and_assoc]
  refine and_congr Iff.rfl (and_congr (by simp) (forall_congr' fun i => or_congr Iff.rfl ?_))
  rw [hE]
  unfold Formula.Realize
  have h1 : (Sum.elim (Sum.elim a ![c]) (ws ∘ Fin.castAdd 0) ∘
      Sum.elim (fun j : Fin 2 => (Sum.inr (![i.castSucc, i.succ] j) :
        (Fin (s + 1) ⊕ Fin 1) ⊕ Fin (r + 1)))
        (fun j : Fin s => Sum.inl (Sum.inl (Fin.castSucc j)))) =
      Sum.elim ![ws i.castSucc, ws i.succ] (a ∘ Fin.castSucc) := by
    funext j
    rcases j with j | j
    · fin_cases j <;> rfl
    · rfl
  rw [h1]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

end Lax185574Proofs.FlipDistanceFormula
