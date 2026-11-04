import Lax185574.DefinableFlipFormula
import Mathlib.ModelTheory.Complexity

namespace Lax185574Proofs.DefinableFlipFormula

open FirstOrder FirstOrder.Language
open Lax185574.AtomicTypes Lax185574.DefinableFlips

universe u w

section QF

variable {L : Language} {α : Type w} {n : ℕ}

theorem isQF_foldr_sup (l : List (L.BoundedFormula α n)) (h : ∀ φ ∈ l, φ.IsQF) :
    (l.foldr (· ⊔ ·) ⊥).IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons φ l ih =>
    exact (h φ (by simp)).sup (ih fun ψ hψ => h ψ (by simp [hψ]))

theorem isQF_foldr_inf (l : List (L.BoundedFormula α n)) (h : ∀ φ ∈ l, φ.IsQF) :
    (l.foldr (· ⊓ ·) ⊤).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons φ l ih =>
    exact (h φ (by simp)).inf (ih fun ψ hψ => h ψ (by simp [hψ]))

theorem isQF_iSup {β : Type*} [Finite β] (f : β → L.BoundedFormula α n)
    (h : ∀ b, (f b).IsQF) : (BoundedFormula.iSup f).IsQF := by
  unfold BoundedFormula.iSup
  exact isQF_foldr_sup _ fun φ hφ => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hφ
    exact h b

theorem isQF_iInf {β : Type*} [Finite β] (f : β → L.BoundedFormula α n)
    (h : ∀ b, (f b).IsQF) : (BoundedFormula.iInf f).IsQF := by
  unfold BoundedFormula.iInf
  exact isQF_foldr_inf _ fun φ hφ => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hφ
    exact h b

end QF

section Formulas

variable {β : Type w}

/-- The edge formula `E(a, b)` on two variables. -/
def adjF (a b : β) : Language.graph.Formula β :=
  Relations.formula₂ Language.adj (Term.var a) (Term.var b)

/-- The equality formula `a = b` on two variables. -/
def eqF (a b : β) : Language.graph.Formula β :=
  Term.equal (Term.var a) (Term.var b)

/-- The formula saying that the pair `(a, b)` has the atomic type `P`. -/
def pairTypeF (P : PairType) (a b : β) : Language.graph.Formula β :=
  match P with
  | .eq => eqF a b
  | .adj => (eqF a b).not ⊓ adjF a b
  | .nonAdj => (eqF a b).not ⊓ (adjF a b).not

/-- The formula saying that `atp(a/z̄) = P`. -/
noncomputable def atpF {s : ℕ} (P : Fin s → PairType) (a : β) (z : Fin s → β) :
    Language.graph.Formula β :=
  BoundedFormula.iInf fun i => pairTypeF (P i) a (z i)

/-- The formula saying that `(atp(a/z̄), atp(b/z̄)) ∈ R`. -/
noncomputable def relF {s : ℕ} (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (a b : β) (z : Fin s → β) : Language.graph.Formula β :=
  open Classical in
  BoundedFormula.iSup fun PQ : (Fin s → PairType) × (Fin s → PairType) =>
    if R PQ.1 PQ.2 then atpF PQ.1 a z ⊓ atpF PQ.2 b z else ⊥

/-- The edge formula of `G ⊕ (z̄, R)` on the variables `a`, `b`. -/
noncomputable def flipAdjF {s : ℕ} (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (a b : β) (z : Fin s → β) : Language.graph.Formula β :=
  (eqF a b).not ⊓ ((adjF a b ⊓ (relF R a b z).not) ⊔ ((adjF a b).not ⊓ relF R a b z))

theorem isQF_pairTypeF (P : PairType) (a b : β) : (pairTypeF P a b).IsQF := by
  have he : (eqF a b).IsQF := (BoundedFormula.IsAtomic.equal _ _).isQF
  have ha : (adjF a b).IsQF := (BoundedFormula.IsAtomic.rel _ _).isQF
  cases P
  · exact he
  · exact he.not.inf ha
  · exact he.not.inf ha.not

theorem isQF_flipAdjF {s : ℕ} (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (a b : β) (z : Fin s → β) : (flipAdjF R a b z).IsQF := by
  have he : (eqF a b).IsQF := (BoundedFormula.IsAtomic.equal _ _).isQF
  have ha : (adjF a b).IsQF := (BoundedFormula.IsAtomic.rel _ _).isQF
  have hatp : ∀ (P : Fin s → PairType) (c : β), (atpF P c z).IsQF := fun P c =>
    isQF_iInf _ fun i => isQF_pairTypeF _ _ _
  have hr : (relF R a b z).IsQF := by
    classical
    unfold relF
    refine isQF_iSup _ fun PQ => ?_
    split_ifs
    · exact (hatp _ _).inf (hatp _ _)
    · exact BoundedFormula.isQF_bot
  exact he.not.inf ((ha.inf hr.not).sup (ha.not.inf hr))

variable {V : Type u} (G : SimpleGraph V) (e : β → V)

theorem realize_adjF (a b : β) :
    @Formula.Realize Language.graph V G.structure _ (adjF a b) e ↔ G.Adj (e a) (e b) :=
  Iff.rfl

theorem realize_eqF (a b : β) :
    @Formula.Realize Language.graph V G.structure _ (eqF a b) e ↔ e a = e b :=
  Iff.rfl

theorem realize_pairTypeF (P : PairType) (a b : β) :
    @Formula.Realize Language.graph V G.structure _ (pairTypeF P a b) e ↔
      pairType G (e a) (e b) = P := by
  let _ := G.structure
  unfold pairType
  cases P <;> simp only [pairTypeF, Formula.realize_inf, Formula.realize_not,
    realize_eqF, realize_adjF] <;> split_ifs <;> simp_all

theorem realize_atpF {s : ℕ} (P : Fin s → PairType) (a : β) (z : Fin s → β) :
    @Formula.Realize Language.graph V G.structure _ (atpF P a z) e ↔
      atomicTypeOver G (e ∘ z) (e a) = P := by
  let _ := G.structure
  unfold atpF
  rw [Formula.Realize, BoundedFormula.realize_iInf]
  change (∀ i, Formula.Realize (pairTypeF (P i) a (z i)) e) ↔ _
  rw [funext_iff]
  simp only [realize_pairTypeF, atomicTypeOver, Function.comp]

theorem realize_relF {s : ℕ} (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (a b : β) (z : Fin s → β) :
    @Formula.Realize Language.graph V G.structure _ (relF R a b z) e ↔
      R (atomicTypeOver G (e ∘ z) (e a)) (atomicTypeOver G (e ∘ z) (e b)) := by
  classical
  let _ := G.structure
  unfold relF
  rw [Formula.Realize, BoundedFormula.realize_iSup]
  change (∃ PQ : (Fin s → PairType) × (Fin s → PairType), Formula.Realize
    (if R PQ.1 PQ.2 then atpF PQ.1 a z ⊓ atpF PQ.2 b z else ⊥) e) ↔ _
  constructor
  · rintro ⟨PQ, h⟩
    split_ifs at h with hR
    · rw [Formula.realize_inf, realize_atpF, realize_atpF] at h
      rwa [h.1, h.2]
    · exact (Formula.realize_bot.mp h).elim
  · intro h
    refine ⟨(atomicTypeOver G (e ∘ z) (e a), atomicTypeOver G (e ∘ z) (e b)), ?_⟩
    simp only [h, if_true, Formula.realize_inf, realize_atpF, and_self]

theorem realize_flipAdjF {s : ℕ} (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (hR : ∀ P Q, R P Q → R Q P) (a b : β) (z : Fin s → β) :
    @Formula.Realize Language.graph V G.structure _ (flipAdjF R a b z) e ↔
      (flipOver G (e ∘ z) R).Adj (e a) (e b) := by
  let _ := G.structure
  unfold flipAdjF flipOver
  simp only [Formula.realize_inf, Formula.realize_sup, Formula.realize_not, realize_eqF,
    realize_adjF, realize_relF, SimpleGraph.fromRel_adj, Xor]
  have hsym : ∀ P Q, R P Q ↔ R Q P := fun P Q => ⟨hR P Q, hR Q P⟩
  rw [G.adj_comm (e b), hsym (atomicTypeOver G (e ∘ z) (e b))]
  tauto

end Formulas

/--
---
conclusion: Lax185574.DefinableFlipFormula.exists_isQF_flipOver_formula
---
Two distinct vertices are adjacent in `G ⊕ (p̄, R)` exactly when either
they are adjacent and the pair of their atomic types over `p̄` is not in
`R`, or they are non-adjacent and the pair is in `R`. Membership of the
pair of atomic types in `R` is a finite disjunction, over the pairs in
`R`, of conjunctions of the atomic formulas `x = pᵢ`, `x ≠ pᵢ ∧ E(x, pᵢ)`
and `x ≠ pᵢ ∧ ¬E(x, pᵢ)`.
-/
theorem exists_isQF_flipOver_formula (s : ℕ)
    (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (hR : ∀ P Q, R P Q → R Q P) :
    ∃ φ : Language.graph.Formula (Fin 2 ⊕ Fin s), φ.IsQF ∧
      ∀ (V : Type u) (G : SimpleGraph V) (p : Fin s → V) (x y : V),
        (flipOver G p R).Adj x y ↔
          @Formula.Realize Language.graph V G.structure _ φ (Sum.elim ![x, y] p) := by
  refine ⟨flipAdjF R (Sum.inl 0) (Sum.inl 1) Sum.inr, isQF_flipAdjF _ _ _ _,
    fun V G p x y => ?_⟩
  rw [realize_flipAdjF G _ R hR]
  rfl

end Lax185574Proofs.DefinableFlipFormula
