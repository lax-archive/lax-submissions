import Lax185574.Colorings
import Lax185574.FirstOrderTypes
import Lax185574Proofs.DefinableFlipFormula
import Lax185574Proofs.AtomicTypeBridge
import Lax185574Proofs.FormulaRank

/-!
Types are transported along quantifier-free definitions. If every
relation of a structure `M'` on `V` is defined by a quantifier-free
formula in a structure `M` on the same set, then the type of a tuple in
`M` determines its type in `M'`, at the same quantifier rank and over the
same parameters. The case used is a colored graph `G⁺` and a flip `H` of
`G`, expanded by the colors and by predicates for the parts of the flip.
-/

namespace Lax185574Proofs.TypeTransport

open FirstOrder FirstOrder.Language Structure Lax185574.FirstOrderTypes
open Lax710763.Transductions Lax185574.Colorings
open Lax185574Proofs.AtomicTypeBridge Lax185574Proofs.FormulaRank

universe u v u' v' z w

theorem quantifierRank_eq_zero_of_isQF {L : Language.{u, v}} {α : Type w} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsQF) : quantifierRank φ = 0 := by
  induction h with
  | falsum => rfl
  | of_isAtomic h => cases h <;> rfl
  | imp _ _ ih₁ ih₂ => simp [quantifierRank, ih₁, ih₂]

section Translation

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L'.IsRelational]
variable (ρ : ∀ {l : ℕ}, L'.Relations l → L.Formula (Fin l))
variable {α : Type w}

/-- Replace every relation by its defining formula. -/
def tr : ∀ {n : ℕ}, L'.BoundedFormula α n → L.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (.var (termVar t₁)) (.var (termVar t₂))
  | _, .rel R ts => BoundedFormula.relabel (fun m => termVar (ts m)) (ρ R)
  | _, .imp φ ψ => .imp (tr φ) (tr ψ)
  | _, .all φ => .all (tr φ)

theorem quantifierRank_tr (hρ : ∀ {l : ℕ} (R : L'.Relations l), quantifierRank (ρ R) = 0) :
    ∀ {n : ℕ} (φ : L'.BoundedFormula α n), quantifierRank (tr ρ φ) ≤ quantifierRank φ
  | _, .falsum => le_rfl
  | _, .equal _ _ => le_rfl
  | _, .rel R _ => by
      simp only [tr]
      rw [quantifierRank_relabel, hρ R]
      exact Nat.zero_le _
  | _, .imp φ ψ => by
      have h1 := quantifierRank_tr hρ φ
      have h2 := quantifierRank_tr hρ ψ
      simp only [tr, quantifierRank] at h1 h2 ⊢
      omega
  | _, .all φ => by
      have h1 := quantifierRank_tr hρ φ
      simp only [tr, quantifierRank] at h1 ⊢
      omega

theorem realize_tr {V : Type z} (M : L.Structure V) (M' : L'.Structure V)
    (hρ : ∀ {l : ℕ} (R : L'.Relations l) (x : Fin l → V),
      @Formula.Realize L V M _ (ρ R) x ↔ @RelMap L' V M' l R x) :
    ∀ {n : ℕ} (φ : L'.BoundedFormula α n) (v : α → V) (xs : Fin n → V),
      @BoundedFormula.Realize L V M α n (tr ρ φ) v xs ↔
        @BoundedFormula.Realize L' V M' α n φ v xs := by
  intro n φ
  induction φ with
  | falsum => intro v xs; exact Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    simp only [tr, BoundedFormula.Realize, Term.realize_var]
    rw [@realize_term L' _ V M' _ t₁, @realize_term L' _ V M' _ t₂]
  | rel R ts =>
    intro v xs
    simp only [tr]
    rw [@BoundedFormula.realize_relabel L V M]
    have := hρ R fun m => Sum.elim v xs (termVar (ts m))
    unfold Formula.Realize at this
    simp only [BoundedFormula.Realize, @realize_term L' _ V M' _]
    convert this using 2
    funext m
    simp only [Function.comp_apply]
    generalize termVar (ts m) = t
    cases t <;> rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    simp only [tr, BoundedFormula.Realize, ihφ, ihψ]
  | all φ ih =>
    intro v xs
    simp only [tr, BoundedFormula.Realize, ih]

/-- Types in `M` determine types in `M'`. -/
theorem rankTypeOver_eq_of {V : Type z} (M : L.Structure V) (M' : L'.Structure V)
    (hρ0 : ∀ {l : ℕ} (R : L'.Relations l), quantifierRank (ρ R) = 0)
    (hρ : ∀ {l : ℕ} (R : L'.Relations l) (x : Fin l → V),
      @Formula.Realize L V M _ (ρ R) x ↔ @RelMap L' V M' l R x)
    (q : ℕ) (W : Set V) {K : ℕ} (x y : Fin K → V)
    (h : @rankTypeOver L V M q W K x = @rankTypeOver L V M q W K y) :
    @rankTypeOver L' V M' q W K x = @rankTypeOver L' V M' q W K y := by
  ext φ
  simp only [rankTypeOver, Set.mem_ofPred_eq]
  refine and_congr_right fun hφ => ?_
  have hr : quantifierRank (tr ρ φ) ≤ q := (quantifierRank_tr ρ hρ0 φ).trans hφ
  have key : ∀ z : Fin K → V, @Formula.Realize L' V M' _ φ (Sum.elim z Subtype.val) ↔
      tr ρ φ ∈ @rankTypeOver L V M q W K z := by
    intro z
    simp only [rankTypeOver, Set.mem_ofPred_eq, hr, true_and]
    unfold Formula.Realize
    rw [realize_tr ρ M M' hρ]
  rw [key, key, h]

end Translation

section Flip

open Lax185574Proofs.DefinableFlipFormula

variable {c s : ℕ}

/-- The atom `U_j(x)` for the color `j`. -/
def colorAtom {k : ℕ} (j : Fin k) {β : Type} (b : β) : (withColors Language.graph k).Formula β :=
  (LHom.sumInr : colorLanguage k →ᴸ withColors Language.graph k).onFormula
    (Relations.formula₁ (ColorRel.color j : (colorLanguage k).Relations 1) (Term.var b))

/-- The atom `E(a, b)` in a colored graph. -/
def edgeAtom {k : ℕ} {β : Type} (a b : β) : (withColors Language.graph k).Formula β :=
  (LHom.sumInl : Language.graph →ᴸ withColors Language.graph k).onFormula (adjF a b)

/-- The formula saying that the parts of `x₀` and `x₁` are toggled. -/
noncomputable def toggledF (tog : Fin s → Fin s → Bool) :
    (withColors Language.graph (c + s)).Formula (Fin 2) :=
  BoundedFormula.iSup fun ij : Fin s × Fin s =>
    if tog ij.1 ij.2 then colorAtom (Fin.natAdd c ij.1) 0 ⊓ colorAtom (Fin.natAdd c ij.2) 1
    else ⊥

/-- The edges of `G`, defined in the flip `H` expanded by its parts. -/
noncomputable def edgeBackF (tog : Fin s → Fin s → Bool) :
    (withColors Language.graph (c + s)).Formula (Fin 2) :=
  (Term.equal (Term.var 0) (Term.var 1)).not ⊓
    ((edgeAtom 0 1 ⊓ (toggledF (c := c) tog).not) ⊔ ((edgeAtom 0 1).not ⊓ toggledF (c := c) tog))

/-- The defining formulas of the relations of `G⁺` in `H⁺`. -/
noncomputable def rho (tog : Fin s → Fin s → Bool) :
    ∀ {l : ℕ}, (withColors Language.graph c).Relations l →
      (withColors Language.graph (c + s)).Formula (Fin l)
  | _, Sum.inl .adj => edgeBackF (c := c) tog
  | _, Sum.inr (.color i) => colorAtom (Fin.castAdd s i) 0

theorem isQF_colorAtom {k : ℕ} (j : Fin k) {β : Type} (b : β) : (colorAtom j b).IsQF :=
  (BoundedFormula.IsAtomic.rel _ _).isQF

theorem isQF_edgeAtom {k : ℕ} {β : Type} (a b : β) : (edgeAtom (k := k) a b).IsQF :=
  (BoundedFormula.IsAtomic.rel _ _).isQF

theorem quantifierRank_rho (tog : Fin s → Fin s → Bool) {l : ℕ}
    (R : (withColors Language.graph c).Relations l) : quantifierRank (rho tog R) = 0 := by
  apply quantifierRank_eq_zero_of_isQF
  rcases R with R | R
  · cases R
    have ht : (toggledF (c := c) tog).IsQF := isQF_iSup _ fun ij => by
      split_ifs
      · exact (isQF_colorAtom _ _).inf (isQF_colorAtom _ _)
      · exact BoundedFormula.isQF_bot
    exact (BoundedFormula.IsAtomic.equal _ _).isQF.not.inf
      (((isQF_edgeAtom _ _).inf ht.not).sup ((isQF_edgeAtom _ _).not.inf ht))
  · cases R
    exact isQF_colorAtom _ _

variable {V : Type z}

theorem realize_colorAtom {k : ℕ} (G : SimpleGraph V) (colors : Fin k → Set V) (j : Fin k)
    {β : Type} (b : β) (e : β → V) :
    @Formula.Realize _ V (expansion G colors) _ (colorAtom j b) e ↔ e b ∈ colors j := by
  let _ := G.structure
  let _ := colorStructure colors
  unfold colorAtom
  rw [show (LHom.sumInr : colorLanguage k →ᴸ withColors Language.graph k).onFormula
      (Relations.formula₁ (ColorRel.color j : (colorLanguage k).Relations 1) (Term.var b)) =
      LHom.sumInr.onBoundedFormula _ from rfl]
  unfold Formula.Realize
  rw [LHom.realize_onBoundedFormula]
  rfl

theorem realize_edgeAtom {k : ℕ} (G : SimpleGraph V) (colors : Fin k → Set V)
    {β : Type} (a b : β) (e : β → V) :
    @Formula.Realize _ V (expansion G colors) _ (edgeAtom a b) e ↔ G.Adj (e a) (e b) := by
  let _ := G.structure
  let _ := colorStructure colors
  unfold edgeAtom
  unfold Formula.Realize
  rw [show (LHom.sumInl : Language.graph →ᴸ withColors Language.graph k).onFormula (adjF a b) =
      LHom.sumInl.onBoundedFormula _ from rfl, LHom.realize_onBoundedFormula]
  rfl

theorem realize_rho (G H : SimpleGraph V) (colors : Fin c → Set V) (lab : V → Fin s)
    (tog : Fin s → Fin s → Bool)
    (hGH : ∀ x y, G.Adj x y ↔ x ≠ y ∧ Xor (H.Adj x y) (tog (lab x) (lab y) = true))
    {l : ℕ} (R : (withColors Language.graph c).Relations l) (x : Fin l → V) :
    @Formula.Realize _ V (expansion H (Fin.append colors fun i => {y | lab y = i})) _
        (rho tog R) x ↔ @RelMap _ V (expansion G colors) l R x := by
  let _ := expansion H (Fin.append colors fun i => {y | lab y = i})
  rcases R with R | R
  · cases R
    have htog : @Formula.Realize _ V (expansion H (Fin.append colors fun i => {y | lab y = i})) _
        (toggledF (c := c) tog) x ↔ tog (lab (x 0)) (lab (x 1)) = true := by
      unfold toggledF Formula.Realize
      rw [BoundedFormula.realize_iSup]
      constructor
      · rintro ⟨ij, h⟩
        split_ifs at h with hij
        · change Formula.Realize _ _ at h
          rw [Formula.realize_inf, realize_colorAtom, realize_colorAtom] at h
          simp only [Fin.append_right, Set.mem_ofPred_eq] at h
          rw [h.1, h.2]; exact hij
        · exact absurd h (by simp [BoundedFormula.Realize])
      · intro h
        refine ⟨(lab (x 0), lab (x 1)), ?_⟩
        simp only [h, if_true]
        change Formula.Realize _ _
        rw [Formula.realize_inf, realize_colorAtom, realize_colorAtom]
        simp
    change @Formula.Realize _ V _ _ (edgeBackF (c := c) tog) x ↔ G.Adj (x 0) (x 1)
    unfold edgeBackF
    simp only [Formula.realize_inf, Formula.realize_sup, Formula.realize_not,
      realize_edgeAtom, htog, Formula.realize_equal, Term.realize_var, hGH, Xor]
    tauto
  · cases R with
    | color i =>
      change @Formula.Realize _ V (expansion H (Fin.append colors fun i => {y | lab y = i})) _
        (colorAtom (Fin.castAdd s i) 0) x ↔ x 0 ∈ colors i
      rw [realize_colorAtom, Fin.append_left]

/-- Types in the expanded flip determine types in `G⁺`. -/
theorem rankTypeOver_eq_of_flip (G H : SimpleGraph V) (colors : Fin c → Set V)
    (lab : V → Fin s) (tog : Fin s → Fin s → Bool)
    (hGH : ∀ x y, G.Adj x y ↔ x ≠ y ∧ Xor (H.Adj x y) (tog (lab x) (lab y) = true))
    (q : ℕ) (W : Set V) {K : ℕ} (x y : Fin K → V)
    (h : @rankTypeOver _ V (expansion H (Fin.append colors fun i => {y | lab y = i})) q W K x =
      @rankTypeOver _ V (expansion H (Fin.append colors fun i => {y | lab y = i})) q W K y) :
    @rankTypeOver _ V (expansion G colors) q W K x =
      @rankTypeOver _ V (expansion G colors) q W K y :=
  rankTypeOver_eq_of (fun R => rho tog R) _ _ (fun R => quantifierRank_rho tog R)
    (fun R x => realize_rho G H colors lab tog hGH R x) q W x y h

end Flip

end Lax185574Proofs.TypeTransport
