import Lax185574Proofs.IP.Coding

/-!
The two formulas of the reduction of coding to single variables.

For a coding formula `θ(x₀ x₁ … x_{p+1}, ȳ, z)`, the formula
`θ₁(x, ȳ, z)` says that `x` extends by elements `x₁, …, x_{p+1}` of a
color `A` to a tuple coding `z` and no other element of a color `C`.

For a map `μ` telling which entries of the left tuple are variables and
which are parameters, `θ_μ` is `θ` with the parameter entries replaced by
the elements of singleton colors.
-/

namespace Lax185574Proofs.IP

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.Transductions
open Lax185574Proofs.Interface.Old Lax185574Proofs.IndependenceProperty

variable {k p q : ℕ}

/-- Variables of `θ` inside the body of `θ₁`. -/
def mainVar : (Fin (p + 2) ⊕ Fin q) ⊕ Fin 1 → ((Fin 1 ⊕ Fin q) ⊕ Fin 1) ⊕ Fin (p + 1)
  | Sum.inl (Sum.inl i) => Fin.cases (Sum.inl (Sum.inl (Sum.inl 0))) Sum.inr i
  | Sum.inl (Sum.inr j) => Sum.inl (Sum.inl (Sum.inr j))
  | Sum.inr _ => Sum.inl (Sum.inr 0)

/-- Variables of `θ` inside the uniqueness clause of `θ₁`. -/
def uniqVar :
    (Fin (p + 2) ⊕ Fin q) ⊕ Fin 1 → (((Fin 1 ⊕ Fin q) ⊕ Fin 1) ⊕ Fin (p + 1)) ⊕ Fin 1
  | Sum.inl (Sum.inl i) => Fin.cases (Sum.inl (Sum.inl (Sum.inl (Sum.inl 0))))
      (fun t => Sum.inl (Sum.inr t)) i
  | Sum.inl (Sum.inr j) => Sum.inl (Sum.inl (Sum.inl (Sum.inr j)))
  | Sum.inr _ => Sum.inr 0

/-- The formula `θ₁(x, ȳ, z)`, with the colors `A` (number `k`) and `C`
(number `k + 1`). -/
noncomputable def theta₁ (θ : (CL k).Formula ((Fin (p + 2) ⊕ Fin q) ⊕ Fin 1)) :
    (CL (k + 2)).Formula ((Fin 1 ⊕ Fin q) ⊕ Fin 1) :=
  Formula.iExs (Fin (p + 1))
    ((Formula.iInf fun t : Fin (p + 1) => colorAtom (Fin.natAdd k 0) (Sum.inr t)) ⊓
      (liftColors 2 θ).relabel mainVar ⊓
      (Formula.iExs (Fin 1)
        (colorAtom (Fin.natAdd k 1) (Sum.inr 0) ⊓
          ((Term.var (Sum.inr 0)).equal (Term.var (Sum.inl (Sum.inl (Sum.inr 0))))).not ⊓
          (liftColors 2 θ).relabel uniqVar)).not)

theorem realizeIn_theta₁ {n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin k → Set (Fin n))
    (A Cs : Set (Fin n)) (θ : (CL k).Formula ((Fin (p + 2) ⊕ Fin q) ⊕ Fin 1))
    (x : Fin n) (y : Fin q → Fin n) (z : Fin n) :
    RealizeIn G.structure (Fin.append colors ![A, Cs]) (theta₁ θ)
        (Sum.elim (Sum.elim (fun _ => x) y) (fun _ => z)) ↔
      ∃ x' : Fin (p + 1) → Fin n, (∀ t, x' t ∈ A) ∧
        RealizeIn G.structure colors θ (Sum.elim (Sum.elim (Fin.cons x x') y) (fun _ => z)) ∧
        ∀ z', z' ∈ Cs → z' ≠ z →
          ¬ RealizeIn G.structure colors θ (Sum.elim (Sum.elim (Fin.cons x x') y) (fun _ => z')) := by
  have hA : Fin.append colors ![A, Cs] (Fin.natAdd k 0) = A := by rw [Fin.append_right]; rfl
  have hC : Fin.append colors ![A, Cs] (Fin.natAdd k 1) = Cs := by rw [Fin.append_right]; rfl
  unfold theta₁
  rw [realizeIn_iExs]
  apply exists_congr
  intro x'
  rw [realizeIn_inf, realizeIn_inf, realizeIn_iInf, realizeIn_not, realizeIn_iExs,
    realizeIn_relabel, realizeIn_liftColors]
  simp only [Lax185574Proofs.IndependenceProperty.realizeIn_colorAtom, hA, hC, realizeIn_inf,
    realizeIn_not, realizeIn_relabel, realizeIn_liftColors, Sum.elim_inr, not_exists]
  have e1 : (Sum.elim (Sum.elim (Sum.elim (fun _ => x) y) fun _ => z) x' ∘ mainVar) =
      Sum.elim (Sum.elim (Fin.cons x x' : Fin (p + 2) → Fin n) y) (fun _ : Fin 1 => z) := by
    funext v
    rcases v with (i | j) | w
    · cases i using Fin.cases <;> rfl
    · rfl
    · rfl
  have e2 : ∀ u : Fin 1 → Fin n,
      (Sum.elim (Sum.elim (Sum.elim (Sum.elim (fun _ => x) y) fun _ => z) x') u ∘ uniqVar) =
      Sum.elim (Sum.elim (Fin.cons x x' : Fin (p + 2) → Fin n) y) (fun _ : Fin 1 => u 0) := by
    intro u
    funext v
    rcases v with (i | j) | w
    · cases i using Fin.cases <;> rfl
    · rfl
    · rw [Subsingleton.elim w 0]; rfl
  rw [e1]
  simp only [e2]
  have heq : ∀ u : Fin 1 → Fin n, RealizeIn G.structure (Fin.append colors ![A, Cs])
      ((Term.var (Sum.inr 0)).equal (Term.var (Sum.inl (Sum.inl (Sum.inr 0)))) :
        (CL (k + 2)).Formula ((((Fin 1 ⊕ Fin q) ⊕ Fin 1) ⊕ Fin (p + 1)) ⊕ Fin 1))
      (Sum.elim (Sum.elim (Sum.elim (Sum.elim (fun _ => x) y) fun _ => z) x') u) ↔ u 0 = z := by
    intro u
    unfold RealizeIn
    let _ := G.structure
    let _ := colorStructure (Fin.append colors ![A, Cs])
    simp only [Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  simp only [heq]
  constructor
  · rintro ⟨⟨hx, hθ⟩, hu⟩
    refine ⟨hx, hθ, fun z' hz' hne h => hu (fun _ => z') ⟨⟨hz', hne⟩, h⟩⟩
  · rintro ⟨hx, hθ, hu⟩
    exact ⟨⟨hx, hθ⟩, fun u ⟨⟨hz', hne⟩, h⟩ => hu (u 0) hz' hne h⟩

/-- Variables of `θ` inside `θ_μ`. -/
def paramVar (μ : Fin (p + 2) → Fin (p + 1) ⊕ Fin (p + 2)) :
    (Fin (p + 2) ⊕ Fin q) ⊕ Fin 1 → ((Fin (p + 1) ⊕ Fin q) ⊕ Fin 1) ⊕ Fin (p + 2) :=
  Sum.elim
    (Sum.elim (fun i => Sum.elim (fun v => Sum.inl (Sum.inl (Sum.inl v))) Sum.inr (μ i))
      (fun j => Sum.inl (Sum.inl (Sum.inr j))))
    (fun _ => Sum.inl (Sum.inr 0))

theorem comp_paramVar {n : ℕ} (μ : Fin (p + 2) → Fin (p + 1) ⊕ Fin (p + 2))
    (xv : Fin (p + 1) → Fin n) (y : Fin q → Fin n) (z : Fin n) (par : Fin (p + 2) → Fin n) :
    (Sum.elim (Sum.elim (Sum.elim xv y) (fun _ : Fin 1 => z)) par ∘ paramVar μ) =
      Sum.elim (Sum.elim (fun i => Sum.elim xv par (μ i)) y) (fun _ : Fin 1 => z) := by
  funext v
  rcases v with (i | j) | w
  · simp only [paramVar, Function.comp_apply, Sum.elim_inl]
    cases μ i <;> rfl
  · rfl
  · rfl

/-- The formula `θ_μ`, with the singleton colors `k + s` for the parameters. -/
noncomputable def thetaParam (θ : (CL k).Formula ((Fin (p + 2) ⊕ Fin q) ⊕ Fin 1))
    (μ : Fin (p + 2) → Fin (p + 1) ⊕ Fin (p + 2)) :
    (CL (k + (p + 2))).Formula ((Fin (p + 1) ⊕ Fin q) ⊕ Fin 1) :=
  Formula.iExs (Fin (p + 2))
    ((Formula.iInf fun s : Fin (p + 2) => colorAtom (Fin.natAdd k s) (Sum.inr s)) ⊓
      (liftColors (p + 2) θ).relabel (paramVar μ))

theorem realizeIn_thetaParam {n : ℕ} (G : SimpleGraph (Fin n)) (colors : Fin k → Set (Fin n))
    (par : Fin (p + 2) → Fin n) (θ : (CL k).Formula ((Fin (p + 2) ⊕ Fin q) ⊕ Fin 1))
    (μ : Fin (p + 2) → Fin (p + 1) ⊕ Fin (p + 2))
    (xv : Fin (p + 1) → Fin n) (y : Fin q → Fin n) (z : Fin n) :
    RealizeIn G.structure (Fin.append colors fun s => {par s}) (thetaParam θ μ)
        (Sum.elim (Sum.elim xv y) (fun _ => z)) ↔
      RealizeIn G.structure colors θ
        (Sum.elim (Sum.elim (fun i => Sum.elim xv par (μ i)) y) (fun _ => z)) := by
  unfold thetaParam
  rw [realizeIn_iExs]
  simp only [realizeIn_inf, realizeIn_iInf, Lax185574Proofs.IndependenceProperty.realizeIn_colorAtom,
    Fin.append_right, Sum.elim_inr, Set.mem_singleton_iff, realizeIn_relabel,
    realizeIn_liftColors]
  constructor
  · rintro ⟨u, hu, h⟩
    have hu' : u = par := funext hu
    subst hu'
    rwa [comp_paramVar] at h
  · intro h
    exact ⟨par, fun s => rfl, by rwa [comp_paramVar]⟩

end Lax185574Proofs.IP
