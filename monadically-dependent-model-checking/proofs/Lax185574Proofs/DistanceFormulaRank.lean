import Lax185574.LocalFormulas
import Lax185574.FirstOrderTypes

open FirstOrder FirstOrder.Language Lax185574.GaifmanGraph Lax185574.LocalFormulas
open Lax185574.FirstOrderTypes

/-!
Quantifier ranks of substitutions, relabellings, finite connectives and of
the adjacency and distance formulas of `Lax185574.LocalFormulas`. The formula
`dist(x₁, x₂) ≤ r` has rank at most `r + α − 2` over a signature of arity at
most `α`.
-/

universe u v

namespace Lax185574Proofs.DistanceFormulaRank

variable {L : Language.{u, v}}

theorem qr_castLE {α : Type*} : ∀ {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormula α m),
    quantifierRank (φ.castLE h) = quantifierRank φ
  | _, _, _, .falsum => rfl
  | _, _, _, .equal _ _ => rfl
  | _, _, _, .rel _ _ => rfl
  | _, _, h, .imp a b => by
      simp only [BoundedFormula.castLE, quantifierRank, qr_castLE h a, qr_castLE h b]
  | _, _, h, .all a => by
      simp only [BoundedFormula.castLE, quantifierRank, qr_castLE _ a]

theorem qr_subst {α β : Type*} {n : ℕ} (φ : L.BoundedFormula α n) (f : α → L.Term β) :
    quantifierRank (φ.subst f) = quantifierRank φ := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp a b iha ihb => simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, quantifierRank] at *; rw [iha, ihb]
  | all a ih => simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, quantifierRank, id] at *; rw [ih]

theorem qr_relabel {α β : Type*} {m : ℕ} (g : α → β ⊕ Fin m) {k : ℕ} (φ : L.BoundedFormula α k) :
    quantifierRank (φ.relabel g) = quantifierRank φ := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp a b iha ihb => simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, quantifierRank] at *; rw [iha, ihb]
  | all a ih =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, quantifierRank] at *
      rw [qr_castLE, ih]

theorem qr_sup {α : Type*} {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    quantifierRank (φ ⊔ ψ) = max (quantifierRank φ) (quantifierRank ψ) := by
  show max (max (quantifierRank φ) 0) (quantifierRank ψ) = _
  simp

theorem qr_inf {α : Type*} {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    quantifierRank (φ ⊓ ψ) = max (quantifierRank φ) (quantifierRank ψ) := by
  show max (max (quantifierRank φ) (max (quantifierRank ψ) 0)) 0 = _
  simp

theorem qr_not {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n) :
    quantifierRank (∼φ) = quantifierRank φ := by
  show max (quantifierRank φ) 0 = _; simp

theorem qr_ex {α : Type*} {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    quantifierRank φ.ex = quantifierRank φ + 1 := by
  show max (max (quantifierRank φ) 0 + 1) 0 = _; simp

theorem qr_exs {α : Type*} : ∀ {n : ℕ} (φ : L.BoundedFormula α n),
    quantifierRank φ.exs = quantifierRank φ + n
  | 0, φ => rfl
  | n + 1, φ => by
      show quantifierRank (φ.ex.exs) = _
      rw [qr_exs, qr_ex]; omega

theorem qr_foldr_sup_le {α : Type*} {n : ℕ} (l : List (L.BoundedFormula α n)) (b : ℕ)
    (h : ∀ φ ∈ l, quantifierRank φ ≤ b) : quantifierRank (l.foldr (· ⊔ ·) ⊥) ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons x l ih =>
      simp only [List.foldr_cons, qr_sup]
      exact max_le (h x (by simp)) (ih fun φ hφ => h φ (by simp [hφ]))

theorem qr_foldr_inf_le {α : Type*} {n : ℕ} (l : List (L.BoundedFormula α n)) (b : ℕ)
    (h : ∀ φ ∈ l, quantifierRank φ ≤ b) : quantifierRank (l.foldr (· ⊓ ·) ⊤) ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons x l ih =>
      simp only [List.foldr_cons, qr_inf]
      exact max_le (h x (by simp)) (ih fun φ hφ => h φ (by simp [hφ]))

theorem qr_iSup_le {α β : Type*} [Finite β] {n : ℕ} (f : β → L.BoundedFormula α n) (b : ℕ)
    (h : ∀ i, quantifierRank (f i) ≤ b) : quantifierRank (BoundedFormula.iSup f) ≤ b := by
  unfold BoundedFormula.iSup
  dsimp only
  apply qr_foldr_sup_le
  intro φ hφ
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hφ
  exact h i

theorem qr_iInf_le {α β : Type*} [Finite β] {n : ℕ} (f : β → L.BoundedFormula α n) (b : ℕ)
    (h : ∀ i, quantifierRank (f i) ≤ b) : quantifierRank (BoundedFormula.iInf f) ≤ b := by
  unfold BoundedFormula.iInf
  dsimp only
  apply qr_foldr_inf_le
  intro φ hφ
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hφ
  exact h i

theorem qr_instantiate {β : Type*} {j n : ℕ} (φ : L.Formula (Fin j)) (t : Fin j → L.Term (β ⊕ Fin n)) :
    quantifierRank (instantiate φ t) = quantifierRank φ := by
  unfold instantiate; rw [qr_relabel, qr_subst]

theorem qr_adjFormula [Finite (Σ l, L.Relations l)] (α : ℕ) (hα : ∀ l, α < l → IsEmpty (L.Relations l)) :
    quantifierRank (adjFormula L) ≤ α - 2 := by
  unfold adjFormula
  rw [qr_inf]
  refine max_le (by rw [qr_not]; exact Nat.zero_le _) (qr_iSup_le _ _ fun R => ?_)
  obtain ⟨l, R⟩ := R
  unfold adjVia
  split_ifs with h
  · rw [qr_exs]
    have : l ≤ α := by
      by_contra hc; exact (hα l (by omega)).false R
    have h0 : quantifierRank (BoundedFormula.iSup fun π : Equiv.Perm (Fin l) =>
        BoundedFormula.rel R fun m => adjSlot (L := L) (π m)) ≤ 0 :=
      qr_iSup_le _ _ fun _ => le_refl _
    dsimp only at h0 ⊢
    omega
  · exact Nat.zero_le _

theorem qr_distFormula [Finite (Σ l, L.Relations l)] (α : ℕ) (hα : ∀ l, α < l → IsEmpty (L.Relations l)) (r : ℕ) :
    quantifierRank (distFormula L r) ≤ r + (α - 2) := by
  unfold distFormula
  rw [qr_exs, qr_inf]
  have : quantifierRank (BoundedFormula.iInf fun i : Fin r =>
      ((walkVertex (L := L) i.castSucc).bdEqual (walkVertex i.succ)) ⊔
        instantiate (adjFormula L) ![walkVertex i.castSucc, walkVertex i.succ]) ≤ α - 2 :=
    qr_iInf_le _ _ fun i => by
      rw [qr_sup, qr_instantiate]; exact max_le (Nat.zero_le _) (qr_adjFormula α hα)
  have h2 : quantifierRank ((walkVertex (L := L) (Fin.last r)).bdEqual
      (Term.var (Sum.inl 1) : L.Term (Fin 2 ⊕ Fin r))) = 0 := rfl
  omega

end Lax185574Proofs.DistanceFormulaRank
