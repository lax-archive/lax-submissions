import Lax185574Proofs.Conversions.MergeConstructionLength
import Lax185574Proofs.DistanceFormulas
import Lax185574Proofs.DistanceFormulaRank

/-!
The formulas of the definability part of cl:from-merge-to-construction,
over any structure in which formulas `φ^i_≡` and `φ^i_R` of quantifier
rank at most 5 define the partitions and relations of the merge sequence.

- γ_i(x, y) = x ≠ y ∧ ∀a ∀b ((φ^i_≡(x, a) ∧ φ^i_≡(y, b) ∧ a ≠ b) → φ^{i+1}_R(a, b))
  defines the block D_i, with quantifier rank at most 7.
- Γ_j = ⋁_{i<j} γ_i defines the pairs resolved at the start of stage j.
- A rectangle XY of parts of 𝒫_j is defined from parameters p ∈ X and
  q ∈ Y by x ≠ y ∧ ((φ^j_≡(x, p) ∧ φ^j_≡(y, q)) ∨ (φ^j_≡(x, q) ∧ φ^j_≡(y, p))).
-/

namespace Lax185574Proofs.Conversions.MergeConstruction

open FirstOrder FirstOrder.Language
open Lax185574.PartialGraphs Lax185574.MergeSequences Lax185574.FirstOrderTypes
open Lax185574.LocalFormulas
open Lax185574Proofs.DistanceFormulas Lax185574Proofs.DistanceFormulaRank
open Lax185574Proofs.FormulaRank

open Classical

noncomputable section

variable {L : Language} (eqF relF : ℕ → L.Formula (Fin 2))

/-- The formula `φ(s, t)` for a formula `φ(x, y)`. -/
def pairF (φ : L.Formula (Fin 2)) {β : Type} (s t : β) : L.Formula β := φ.relabel ![s, t]

/-- `s ≠ t`. -/
def neF {β : Type} (s t : β) : L.Formula β := ∼(Term.equal (Term.var s) (Term.var t))

/-- The body of `γ_i`, with free variables `x, y` and bound variables
`a, b`. -/
def gammaBody (i : ℕ) : L.BoundedFormula (Fin 2) 2 :=
  ((instantiate (eqF i) ![Term.var (Sum.inl 0), Term.var (Sum.inr 0)] ⊓
      instantiate (eqF i) ![Term.var (Sum.inl 1), Term.var (Sum.inr 1)]) ⊓
      ∼(Term.bdEqual (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1)))) ⟹
    instantiate (relF (i + 1)) ![Term.var (Sum.inr 0), Term.var (Sum.inr 1)]

/-- `γ_i(x, y)`, defining the block `D_i`. -/
def gammaF (i : ℕ) : L.Formula (Fin 2) :=
  neF 0 1 ⊓ BoundedFormula.all (BoundedFormula.all (gammaBody eqF relF i))

/-- `Γ_j(x, y) = ⋁_{i<j} γ_i(x, y)`, defining the pairs resolved at the
start of stage `j`. -/
def GammaF (j : ℕ) : L.Formula (Fin 2) :=
  BoundedFormula.iSup fun i : Fin j => gammaF eqF relF i

/-- The rectangle of the parts of `𝒫_j` of `p` and `q`. -/
def rectF (j : ℕ) {β : Type} (x y p q : β) : L.Formula β :=
  neF x y ⊓ ((pairF (eqF j) x p ⊓ pairF (eqF j) y q) ⊔ (pairF (eqF j) x q ⊓ pairF (eqF j) y p))

/-! ### Quantifier ranks -/

variable {eqF relF}

theorem qr_pairF (φ : L.Formula (Fin 2)) {β : Type} (s t : β) :
    quantifierRank (pairF φ s t) = quantifierRank φ :=
  quantifierRank_formula_relabel _ φ

theorem qr_neF {β : Type} (s t : β) : quantifierRank (neF (L := L) s t) = 0 := by
  rw [neF, qr_not]; rfl

theorem qr_gammaF (heq : ∀ i, quantifierRank (eqF i) ≤ 5) (hrel : ∀ i, quantifierRank (relF i) ≤ 5)
    (i : ℕ) : quantifierRank (gammaF eqF relF i) ≤ 7 := by
  have h1 := heq i
  have h2 := hrel (i + 1)
  simp only [gammaF, gammaBody, qr_inf, qr_neF, quantifierRank, qr_instantiate]
  simp only [Term.bdEqual, quantifierRank]
  omega

theorem qr_GammaF (heq : ∀ i, quantifierRank (eqF i) ≤ 5) (hrel : ∀ i, quantifierRank (relF i) ≤ 5)
    (j : ℕ) : quantifierRank (GammaF eqF relF j) ≤ 7 :=
  qr_iSup_le _ _ fun i => qr_gammaF heq hrel i

theorem qr_rectF (heq : ∀ i, quantifierRank (eqF i) ≤ 5) (j : ℕ) {β : Type} (x y p q : β) :
    quantifierRank (rectF eqF j x y p q) ≤ 5 := by
  have := heq j
  simp only [rectF, qr_inf, qr_sup, qr_neF, qr_pairF]
  omega

/-! ### Realization -/

variable {n : ℕ} {G : SimpleGraph (Fin n)} {ms : List (Setoid (Fin n) × SimpleGraph (Fin n))}
variable [L.Structure (Fin n)]

theorem realize_pairF (φ : L.Formula (Fin 2)) {β : Type} (s t : β) (v : β → Fin n) :
    (pairF φ s t).Realize v ↔ φ.Realize ![v s, v t] := by
  rw [pairF, Formula.realize_relabel]
  have : v ∘ ![s, t] = ![v s, v t] := by funext i; fin_cases i <;> rfl
  rw [this]

theorem realize_neF {β : Type} (s t : β) (v : β → Fin n) :
    (neF (L := L) s t).Realize v ↔ v s ≠ v t := by
  simp [neF, Formula.realize_not, Formula.realize_equal]

variable (hEq : ∀ i < ms.length, ∀ x : Fin 2 → Fin n, (eqF i).Realize x ↔ part ms i (x 0) (x 1))
variable (hRel : ∀ i < ms.length, ∀ x : Fin 2 → Fin n,
  (relF i).Realize x ↔ (rel ms i).Adj (x 0) (x 1))

include hEq hRel in
theorem realize_gammaF {i : ℕ} (hi : i + 1 < ms.length) (x : Fin 2 → Fin n) :
    (gammaF eqF relF i).Realize x ↔ (block ms i).Adj (x 0) (x 1) := by
  rw [block_adj]
  unfold gammaF
  rw [Formula.realize_inf, realize_neF]
  refine and_congr Iff.rfl ?_
  unfold Formula.Realize
  simp only [BoundedFormula.realize_all, gammaBody, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, realize_instantiate,
    BoundedFormula.realize_bdEqual]
  have hfun : ∀ (env : Fin 2 ⊕ Fin 2 → Fin n) (t0 t1 : L.Term (Fin 2 ⊕ Fin 2)),
      (fun k => Term.realize env (![t0, t1] k)) = ![t0.realize env, t1.realize env] := by
    intro env t0 t1; funext k; fin_cases k <;> rfl
  have h0 : ∀ a b : Fin n, (Fin.snoc (Fin.snoc (default : Fin 0 → Fin n) a) b : Fin 2 → Fin n) 0 = a :=
    fun _ _ => rfl
  have h1 : ∀ a b : Fin n, (Fin.snoc (Fin.snoc (default : Fin 0 → Fin n) a) b : Fin 2 → Fin n) 1 = b :=
    fun _ _ => rfl
  simp only [hfun, Term.realize_var, Sum.elim_inl, Sum.elim_inr, h0, h1]
  simp only [hEq i (by omega), hRel (i + 1) hi, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h a b ha hb hab
    exact h a b ⟨⟨(part ms i).symm ha, (part ms i).symm hb⟩, hab⟩
  · rintro h a b ⟨⟨ha, hb⟩, hab⟩
    exact h a b ((part ms i).symm ha) ((part ms i).symm hb) hab

include hEq hRel in
theorem realize_GammaF {j : ℕ} (hj : j < ms.length) (x : Fin 2 → Fin n) :
    (GammaF eqF relF j).Realize x ↔ (resolvedAt ms j).Adj (x 0) (x 1) := by
  rw [resolvedAt_adj]
  unfold GammaF Formula.Realize
  rw [BoundedFormula.realize_iSup]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.2, (realize_gammaF hEq hRel (by omega) x).1 hi⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, (realize_gammaF hEq hRel (by omega) x).2 h⟩

include hEq in
theorem realize_rectF {j : ℕ} (hj : j < ms.length) {β : Type} (x y p q : β) (v : β → Fin n)
    (hp : rep (part ms j) (v p) = v p) (hq : rep (part ms j) (v q) = v q) :
    (rectF eqF j x y p q).Realize v ↔ (rect ms j (v p) (v q)).Adj (v x) (v y) := by
  rw [rect_adj, rectF, Formula.realize_inf, realize_neF, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_inf, realize_pairF, realize_pairF, realize_pairF, realize_pairF]
  simp only [hEq j hj, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [col_eq_least_iff hp, col_eq_least_iff hq, col_eq_least_iff hp, col_eq_least_iff hq]
  tauto

end

end Lax185574Proofs.Conversions.MergeConstruction
