import Lax185574.DistanceLogic
import Lax185574.FirstOrderTypes
import Lax185574Proofs.DistanceFormulaRank
import Lax185574Proofs.WalkDistance
import Mathlib.Tactic.FinCases

/-!
Distance formulas over partial graphs as first-order formulas. A distance
atom `dist(x, y) ≤ r` is expressed by a walk along resolved pairs, which
needs `r` nested quantifiers. So a formula of distance rank `(k, q)` is
equivalent to a first-order formula of quantifier rank at most
`ρ⁺(k, q) + q`, as in the proof of lem:ball-tree-bound.
-/

namespace Lax185574Proofs.DistanceTranslation

open FirstOrder FirstOrder.Language
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.FirstOrderTypes
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO
open Lax185574Proofs.DistanceFormulaRank Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

/-! ### Building blocks -/

/-- The map sending the last variable to the new bound variable. -/
def lastToBound (ℓ : ℕ) : Fin (ℓ + 1) → Fin ℓ ⊕ Fin 1 :=
  Fin.lastCases (motive := fun _ => Fin ℓ ⊕ Fin 1) (Sum.inr 0) Sum.inl

/-- `∃ x_{ℓ+1} ψ`: existential quantification of the last free variable. -/
def exLast {ℓ : ℕ} (ψ : language.Formula (Fin (ℓ + 1))) : language.Formula (Fin ℓ) :=
  BoundedFormula.ex (BoundedFormula.relabel (lastToBound ℓ) ψ : language.BoundedFormula (Fin ℓ) 1)

theorem qr_exLast {ℓ : ℕ} (ψ : language.Formula (Fin (ℓ + 1))) :
    quantifierRank (exLast ψ) = quantifierRank ψ + 1 := by
  rw [exLast, qr_ex, qr_relabel]

theorem qr_formula_relabel {α β : Type*} (g : α → β) (φ : language.Formula α) :
    quantifierRank (φ.relabel g) = quantifierRank φ :=
  qr_relabel _ φ

section Semantics

variable {M : Type*} [language.Structure M]

theorem realize_exLast {ℓ : ℕ} (ψ : language.Formula (Fin (ℓ + 1))) (v : Fin ℓ → M) :
    (exLast ψ).Realize v ↔ ∃ y, ψ.Realize (Fin.snoc v y) := by
  simp only [exLast, Formula.Realize, BoundedFormula.realize_ex, BoundedFormula.realize_relabel]
  refine exists_congr fun y => ?_
  have h1 : (Sum.elim v (Fin.snoc (default : Fin 0 → M) y ∘ Fin.castAdd 0) ∘ lastToBound ℓ) =
      Fin.snoc v y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Function.comp_apply, lastToBound, Fin.lastCases_last, Sum.elim_inr, Fin.snoc_last]
      rfl
    · simp [lastToBound]
  rw [h1]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

end Semantics

/-- Adjacency along a resolved pair: `E(x₀, x₁) ∨ N(x₀, x₁)`. -/
def adjF : language.Formula (Fin 2) :=
  Relations.formula₂ (L := language) Rel.edge (Term.var 0) (Term.var 1) ⊔
    Relations.formula₂ (L := language) Rel.nonEdge (Term.var 0) (Term.var 1)

/-- `dist(x₀, x₁) ≤ r`, by walks along resolved pairs. -/
def distF : ℕ → language.Formula (Fin 2)
  | 0 => Term.equal (Term.var 0) (Term.var 1)
  | r + 1 => distF r ⊔ exLast (adjF.relabel ![0, 2] ⊓ (distF r).relabel ![2, 1])

theorem qr_distF : ∀ r, quantifierRank (distF r) ≤ r
  | 0 => Nat.zero_le _
  | r + 1 => by
    have ih := qr_distF r
    rw [distF, qr_sup, qr_exLast, qr_inf, qr_formula_relabel, qr_formula_relabel]
    have : quantifierRank adjF = 0 := rfl
    omega

theorem withinDist_succ_iff {V : Type*} {H : SimpleGraph V} {r : ℕ} {a b : V} :
    WithinDist H (r + 1) a b ↔ WithinDist H r a b ∨ ∃ z, H.Adj a z ∧ WithinDist H r z b := by
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | nil => exact Or.inl (withinDist_refl _ _ _)
    | cons h p => exact Or.inr ⟨_, h, p, by simp at hp; omega⟩
  · rintro (h | ⟨z, hz, p, hp⟩)
    · exact withinDist_mono (by omega) h
    · exact ⟨.cons hz p, by simp; omega⟩

section PartialGraph

variable {V : Type*} (G : PartialGraph V)

theorem realize_adjF (a b : V) :
    @Formula.Realize _ _ G.structure _ adjF ![a, b] ↔ G.resolved.Adj a b := by
  let _ := G.structure
  simp only [adjF, Formula.realize_sup, PartialGraph.resolved, SimpleGraph.sup_adj]
  rfl

theorem realize_distF (r : ℕ) (a b : V) :
    @Formula.Realize _ _ G.structure _ (distF r) ![a, b] ↔ WithinDist G.resolved r a b := by
  let _ := G.structure
  induction r generalizing a b with
  | zero =>
    simp only [distF, Formula.realize_equal, Term.realize_var]
    simp [withinDist_zero]
  | succ r ih =>
    rw [withinDist_succ_iff]
    simp only [distF, Formula.realize_sup, realize_exLast, Formula.realize_inf,
      Formula.realize_relabel]
    refine or_congr (ih a b) (exists_congr fun z => ?_)
    have h1 : (Fin.snoc ![a, b] z ∘ ![0, 2] : Fin 2 → V) = ![a, z] := by
      funext i; fin_cases i <;> rfl
    have h2 : (Fin.snoc ![a, b] z ∘ ![2, 1] : Fin 2 → V) = ![z, b] := by
      funext i; fin_cases i <;> rfl
    rw [h1, h2, realize_adjF]
    exact and_congr Iff.rfl (ih z b)

theorem realize_color {ℓ : ℕ} (Y : ℕ) (i : Fin ℓ) (v : Fin ℓ → V) :
    @Formula.Realize _ _ G.structure _
      (Relations.formula₁ (L := language) (Rel.color Y) (Term.var i)) v ↔ G.color (v i) = Y :=
  Iff.rfl

theorem realize_distF_relabel {ℓ : ℕ} (r : ℕ) (i j : Fin ℓ) (v : Fin ℓ → V) :
    @Formula.Realize _ _ G.structure _ ((distF r).relabel ![i, j]) v ↔
      WithinDist G.resolved r (v i) (v j) := by
  let _ := G.structure
  rw [Formula.realize_relabel, ← realize_distF]
  have : (v ∘ ![i, j] : Fin 2 → V) = ![v i, v j] := by
    funext m; fin_cases m <;> rfl
  rw [this]

end PartialGraph

/-! ### The translation -/

/-- The first-order formula expressing a distance formula. -/
def toFO : {ℓ : ℕ} → DistFO ℓ → language.Formula (Fin ℓ)
  | _, .eq i j => Term.equal (Term.var i) (Term.var j)
  | _, .edge i j => Relations.formula₂ (L := language) Rel.edge (Term.var i) (Term.var j)
  | _, .nonEdge i j => Relations.formula₂ (L := language) Rel.nonEdge (Term.var i) (Term.var j)
  | _, .color Y i => Relations.formula₁ (L := language) (Rel.color Y) (Term.var i)
  | _, .distLe r i j => (distF r).relabel ![i, j]
  | _, .distColorLt 0 _ _ => ⊥
  | ℓ, .distColorLt (s + 1) Y i =>
      exLast (Relations.formula₁ (L := language) (Rel.color Y) (Term.var (Fin.last ℓ)) ⊓
        (distF s).relabel ![i.castSucc, Fin.last ℓ])
  | _, .not φ => ∼(toFO φ)
  | _, .and φ ψ => toFO φ ⊓ toFO ψ
  | ℓ, .exLocal i s φ => exLast ((distF s).relabel ![i.castSucc, Fin.last ℓ] ⊓ toFO φ)

theorem realize_toFO {V : Type*} (G : PartialGraph V) :
    ∀ {ℓ : ℕ} (φ : DistFO ℓ) (v : Fin ℓ → V),
      @Formula.Realize _ _ G.structure _ (toFO φ) v ↔ Sat G v φ := by
  let _ := G.structure
  intro ℓ φ
  induction φ with
  | eq i j =>
    intro w
    simp only [toFO, Formula.realize_equal, Term.realize_var, Sat]
  | edge i j =>
    intro w
    exact Iff.rfl
  | nonEdge i j =>
    intro w
    exact Iff.rfl
  | color Y i =>
    intro w
    exact realize_color G Y i w
  | distLe r i j =>
    intro w
    simp only [toFO, Sat]
    exact realize_distF_relabel G r i j w
  | distColorLt r Y i =>
    intro w
    cases r with
    | zero =>
      simp only [toFO, Sat, Formula.realize_bot, false_iff, not_exists, not_and]
      rintro u - ⟨p, hp⟩
      omega
    | succ s =>
      simp only [toFO, Sat, realize_exLast, Formula.realize_inf, realize_color,
        realize_distF_relabel, Fin.snoc_last, Fin.snoc_castSucc]
      refine exists_congr fun u => and_congr Iff.rfl ?_
      simp only [WithinDist, DistFO.WithinDistLt, Nat.lt_succ_iff]
  | not φ ih =>
    intro w
    simp only [toFO, Formula.realize_not, Sat, ih]
  | and φ ψ ihφ ihψ =>
    intro w
    simp only [toFO, Formula.realize_inf, Sat, ihφ, ihψ]
  | exLocal i s φ ih =>
    intro w
    simp only [toFO, Sat, realize_exLast, Formula.realize_inf, realize_distF_relabel,
      Fin.snoc_last, Fin.snoc_castSucc, ih]

theorem rhoPlus_succ_left_le (k q : ℕ) : rhoPlus (k + 1) q ≤ rhoPlus k (q + 1) :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- A formula of distance rank `(k, q)` translates to a formula of
quantifier rank at most `ρ⁺(k, q) + q`. -/
theorem qr_toFO {k q ℓ : ℕ} {φ : DistFO ℓ} (h : DRank k q φ) :
    quantifierRank (toFO φ) ≤ rhoPlus k q + q := by
  induction h with
  | eq => exact Nat.zero_le _
  | edge => exact Nat.zero_le _
  | nonEdge => exact Nat.zero_le _
  | color => exact Nat.zero_le _
  | @distLe k q ℓ r i j hr =>
    have := qr_distF r
    have := rhoMinus_le_rhoPlus k q
    simp only [toFO, qr_formula_relabel]
    omega
  | @distColorLt k q ℓ r Y i hr =>
    cases r with
    | zero => exact Nat.zero_le _
    | succ s =>
      have := qr_distF s
      simp only [toFO, qr_exLast, qr_inf, qr_formula_relabel]
      have : quantifierRank (Relations.formula₁ (L := language) (Rel.color Y)
          (Term.var (Fin.last ℓ))) = 0 := rfl
      omega
  | not _ ih =>
    simp only [toFO, qr_not]
    exact ih
  | and _ _ ih1 ih2 =>
    simp only [toFO, qr_inf]
    omega
  | @exLocal k q ℓ i φ _ ih =>
    have := qr_distF (rhoPlus (k + 1) q)
    have := rhoPlus_succ_left_le k q
    simp only [toFO, qr_exLast, qr_inf, qr_formula_relabel]
    omega

end Lax185574Proofs.DistanceTranslation
