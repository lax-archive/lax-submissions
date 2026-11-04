import Lax185574Proofs.Chain.Types
import Lax710763.MonadicDependence
import Lax710763.Transductions
import Lax185574Proofs.Lib.MonadicDependenceClosure

/-!
First-order definability of the partitions into types (`cl:types-definable`
of the companion paper), and the formula `φ*` of the reduction without
copying (`lem:types-without-copying`, appendix `sec:types-without-copying`).

The formulas live in the language of graphs with five colors: `A`, `R₀`,
`R⁺`, `R⁻` and `R^∈`, in this order. `tauF k s t` says that the vertices
denoted by the terms `s` and `t` have the same `(k+1)`-type over the
first color. `phiF k` defines, for `x ∉ R` and `y ∈ R`, the adjacency of
the bipartite graph `H` of the reduction, and `psiF k` is its symmetric
version, the adjacency formula of a transduction.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open FirstOrder FirstOrder.Language Lax710763.Transductions

/-- Graphs with five colors. -/
abbrev L5 : Language := withColors Language.graph 5

section Syntax

variable {α : Type}

/-- A term lifted under one more quantifier. -/
def liftT {m : ℕ} (t : L5.Term (α ⊕ Fin m)) : L5.Term (α ⊕ Fin (m + 1)) :=
  t.relabel (Sum.map id Fin.castSucc)

/-- The most recently quantified variable. -/
def newV (m : ℕ) : L5.Term (α ⊕ Fin (m + 1)) := Term.var (Sum.inr (Fin.last m))

/-- Adjacency. -/
def adjF {m : ℕ} (s t : L5.Term (α ⊕ Fin m)) : L5.BoundedFormula α m :=
  BoundedFormula.rel (Sum.inl .adj) ![s, t]

/-- Membership in a color. -/
def colF {m : ℕ} (i : Fin 5) (s : L5.Term (α ⊕ Fin m)) : L5.BoundedFormula α m :=
  BoundedFormula.rel (Sum.inr (.color i)) ![s]

/-- `x` is complete (`b = true`) or anticomplete (`b = false`) to the
part of `y` with `x` removed, for the part given by the formula `τ`. -/
def homF (τ : ∀ {m : ℕ}, L5.Term (α ⊕ Fin m) → L5.Term (α ⊕ Fin m) → L5.BoundedFormula α m)
    (b : Bool) {m : ℕ} (x y : L5.Term (α ⊕ Fin m)) : L5.BoundedFormula α m :=
  BoundedFormula.all
    ((((Term.bdEqual (newV m) (liftT x)).not ⊓ τ (liftT y) (newV m))).imp
      (if b then adjF (liftT x) (newV m) else (adjF (liftT x) (newV m)).not))

/-- `τ_k(s, t)`: same `(k+1)`-type over the color `A`. -/
def tauF : ℕ → ∀ {m : ℕ}, L5.Term (α ⊕ Fin m) → L5.Term (α ⊕ Fin m) → L5.BoundedFormula α m
  | 0, m, s, t =>
    Term.bdEqual s t ⊔ ((colF 0 s).not ⊓ (colF 0 t).not ⊓
      BoundedFormula.all ((colF 0 (newV m)).imp
        ((adjF (liftT s) (newV m)).iff (adjF (liftT t) (newV m)))))
  | k + 1, m, s, t =>
    tauF k s t ⊓ BoundedFormula.all
      (((homF (tauF k) true (liftT s) (newV m)).iff (homF (tauF k) true (liftT t) (newV m))) ⊓
        ((homF (tauF k) false (liftT s) (newV m)).iff (homF (tauF k) false (liftT t) (newV m))))

/-- Membership in `R = R₀ ∪ R⁺ ∪ R⁻ ∪ R^∈`. -/
def inRF {m : ℕ} (s : L5.Term (α ⊕ Fin m)) : L5.BoundedFormula α m :=
  colF 1 s ⊔ colF 2 s ⊔ colF 3 s ⊔ colF 4 s

/-- `φ*(x, y)` of the reduction. -/
def phiF (k : ℕ) {m : ℕ} (x y : L5.Term (α ⊕ Fin m)) : L5.BoundedFormula α m :=
  (inRF x).not ⊓ inRF y ⊓ (colF 1 y).imp (adjF x y) ⊓
    (colF 2 y).imp (homF (tauF k) true x y) ⊓ (colF 3 y).imp (homF (tauF k) false x y) ⊓
    (colF 4 y).imp (tauF k x y)

/-- The adjacency formula of the reduction. -/
def psiF (k : ℕ) : L5.Formula (Fin 2) :=
  (Term.bdEqual (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))).not ⊓
    (phiF k (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1)) ⊔
      phiF k (Term.var (Sum.inl 1)) (Term.var (Sum.inl 0)))

end Syntax

/-! ### Semantics -/

section Semantics

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (colors : Fin 5 → Set V)

/-- The colored graph as a structure. -/
@[reducible] def str5 : L5.Structure V :=
  @Language.sumStructure _ _ V G.structure (colorStructure colors)

variable {α : Type} {m : ℕ} (v : α → V) (xs : Fin m → V)

theorem realize_liftT (t : L5.Term (α ⊕ Fin m)) (a : V) :
    @Term.realize L5 V (str5 G colors) _ (Sum.elim v (Fin.snoc xs a)) (liftT t) =
      @Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) t := by
  unfold liftT
  rw [@Term.realize_relabel]
  congr 1
  funext i
  rcases i with i | i
  · rfl
  · simp

theorem realize_newV (a : V) :
    @Term.realize L5 V (str5 G colors) _ (Sum.elim v (Fin.snoc xs a)) (newV m) = a := by
  simp [newV]

theorem realize_adjF (s t : L5.Term (α ⊕ Fin m)) :
    @BoundedFormula.Realize L5 V (str5 G colors) _ _ (adjF s t) v xs ↔
      G.Adj (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) s)
        (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) t) := by
  unfold adjF
  exact Iff.rfl

theorem realize_colF (i : Fin 5) (s : L5.Term (α ⊕ Fin m)) :
    @BoundedFormula.Realize L5 V (str5 G colors) _ _ (colF i s) v xs ↔
      @Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) s ∈ colors i := by
  unfold colF
  exact Iff.rfl

theorem realize_tauF (A : Finset V) (hA : colors 0 = (A : Set V)) :
    ∀ (k : ℕ) {m : ℕ} (s t : L5.Term (α ⊕ Fin m)) (xs : Fin m → V),
      @BoundedFormula.Realize L5 V (str5 G colors) _ _ (tauF k s t) v xs ↔
        tpRel G A k (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) s)
          (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) t)
  | 0, m, s, t, xs => by
    let _ := str5 G colors
    unfold tauF
    simp only [BoundedFormula.realize_sup, BoundedFormula.realize_inf,
      BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, BoundedFormula.realize_all,
      BoundedFormula.realize_imp, BoundedFormula.realize_iff]
    simp only [realize_colF, realize_adjF, realize_liftT, realize_newV, hA, Finset.mem_coe,
      tpRel_zero, and_assoc]
  | k + 1, m, s, t, xs => by
    let _ := str5 G colors
    unfold tauF
    simp only [BoundedFormula.realize_inf, BoundedFormula.realize_all,
      BoundedFormula.realize_iff]
    rw [realize_tauF A hA k s t xs, tpRel_succ]
    refine and_congr Iff.rfl (forall_congr' fun y => ?_)
    have hhom : ∀ (b : Bool) (x : L5.Term (α ⊕ Fin (m + 1))),
        BoundedFormula.Realize (homF (tauF k) b x (newV m)) v (Fin.snoc xs y) ↔
          (if b then IsComplete G (Term.realize (Sum.elim v (Fin.snoc xs y)) x)
            (cls (tpRel G A k) y)
          else IsAnticomplete G (Term.realize (Sum.elim v (Fin.snoc xs y)) x)
            (cls (tpRel G A k) y)) := by
      intro b x
      unfold homF
      simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp,
        BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual]
      cases b
      · simp only [Bool.false_eq_true, if_false, BoundedFormula.realize_not]
        simp only [IsAnticomplete, mem_cls]
        constructor
        · intro h z hz hzx
          have := h z
          rw [realize_tauF A hA k] at this
          simp only [realize_liftT, realize_newV, realize_adjF] at this
          exact this ⟨hzx, hz⟩
        · intro h z hz
          rw [realize_tauF A hA k] at hz
          simp only [realize_liftT, realize_newV, realize_adjF] at hz ⊢
          exact h z hz.2 hz.1
      · simp only [if_true]
        simp only [IsComplete, mem_cls]
        constructor
        · intro h z hz hzx
          have := h z
          rw [realize_tauF A hA k] at this
          simp only [realize_liftT, realize_newV, realize_adjF] at this
          exact this ⟨hzx, hz⟩
        · intro h z hz
          rw [realize_tauF A hA k] at hz
          simp only [realize_liftT, realize_newV, realize_adjF] at hz ⊢
          exact h z hz.2 hz.1
    rw [hhom true, hhom true, hhom false, hhom false]
    simp only [if_true, Bool.false_eq_true, if_false, realize_liftT]

/-- The set `R = R₀ ∪ R⁺ ∪ R⁻ ∪ R^∈` of a coloring. -/
def rSet (colors : Fin 5 → Set V) : Set V := colors 1 ∪ colors 2 ∪ colors 3 ∪ colors 4

/-- The relation `φ*(x, y)` of the reduction. -/
def PhiRel (A : Finset V) (k : ℕ) (x y : V) : Prop :=
  x ∉ rSet colors ∧ y ∈ rSet colors ∧ (y ∈ colors 1 → G.Adj x y) ∧
    (y ∈ colors 2 → IsComplete G x (cls (tpRel G A k) y)) ∧
    (y ∈ colors 3 → IsAnticomplete G x (cls (tpRel G A k) y)) ∧
    (y ∈ colors 4 → tpRel G A k x y)

/-- The graph `H` of the reduction. -/
def redGraph (A : Finset V) (k : ℕ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (PhiRel G colors A k x y ∨ PhiRel G colors A k y x)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem realize_inRF (s : L5.Term (α ⊕ Fin m)) :
    @BoundedFormula.Realize L5 V (str5 G colors) _ _ (inRF s) v xs ↔
      @Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) s ∈ rSet colors := by
  let _ := str5 G colors
  unfold inRF rSet
  simp only [BoundedFormula.realize_sup, realize_colF, Set.mem_union]

theorem realize_homF (A : Finset V) (hA : colors 0 = (A : Set V)) (k : ℕ) (b : Bool)
    (x y : L5.Term (α ⊕ Fin m)) :
    @BoundedFormula.Realize L5 V (str5 G colors) _ _ (homF (tauF k) b x y) v xs ↔
      (if b then IsComplete G (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) x)
          (cls (tpRel G A k) (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) y))
        else IsAnticomplete G (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) x)
          (cls (tpRel G A k) (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) y))) := by
  let _ := str5 G colors
  unfold homF
  simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual]
  cases b
  · simp only [Bool.false_eq_true, if_false, BoundedFormula.realize_not, IsAnticomplete, mem_cls]
    constructor
    · intro h z hz hzx
      have := h z
      rw [realize_tauF G colors v A hA k] at this
      simp only [realize_liftT, realize_newV, realize_adjF] at this
      exact this ⟨hzx, hz⟩
    · intro h z hz
      rw [realize_tauF G colors v A hA k] at hz
      simp only [realize_liftT, realize_newV, realize_adjF] at hz ⊢
      exact h z hz.2 hz.1
  · simp only [if_true, IsComplete, mem_cls]
    constructor
    · intro h z hz hzx
      have := h z
      rw [realize_tauF G colors v A hA k] at this
      simp only [realize_liftT, realize_newV, realize_adjF] at this
      exact this ⟨hzx, hz⟩
    · intro h z hz
      rw [realize_tauF G colors v A hA k] at hz
      simp only [realize_liftT, realize_newV, realize_adjF] at hz ⊢
      exact h z hz.2 hz.1

theorem realize_phiF (A : Finset V) (hA : colors 0 = (A : Set V)) (k : ℕ)
    (x y : L5.Term (α ⊕ Fin m)) :
    @BoundedFormula.Realize L5 V (str5 G colors) _ _ (phiF k x y) v xs ↔
      PhiRel G colors A k (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) x)
        (@Term.realize L5 V (str5 G colors) _ (Sum.elim v xs) y) := by
  let _ := str5 G colors
  unfold phiF PhiRel
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not, BoundedFormula.realize_imp,
    realize_inRF, realize_colF, realize_adjF, realize_homF G colors v xs A hA,
    realize_tauF G colors v A hA, if_true, Bool.false_eq_true, if_false, and_assoc]

end Semantics

/-! ### The transduced class -/

section Class

open Lax199508.GraphClasses Lax710763.MonadicDependence

theorem realizeIn_psiF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (colors : Fin 5 → Set (Fin n)) (A : Finset (Fin n)) (hA : colors 0 = (A : Set (Fin n)))
    (k : ℕ) (w : Fin 2 → Fin n) :
    RealizeIn G.structure colors (psiF k) w ↔ (redGraph G colors A k).Adj (w 0) (w 1) := by
  unfold RealizeIn psiF
  change @BoundedFormula.Realize L5 (Fin n) (str5 G colors) _ _ _ w default ↔ _
  let _ := str5 G colors
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not,
    BoundedFormula.realize_bdEqual, BoundedFormula.realize_sup, realize_phiF G colors w _ A hA]
  rfl

/-- The graphs `H` of the reduction for the `(k+2)`-types, over all
colorings of members of `C`. -/
def redClass (C : GraphClass) (k : ℕ) : GraphClass :=
  fun n H => ∃ G : SimpleGraph (Fin n), C n G ∧ ∃ colors : Fin 5 → Set (Fin n),
    ∀ x y, H.Adj x y ↔ RealizeIn G.structure colors (psiF k) ![x, y]

theorem transduces_redClass (C : GraphClass) (k : ℕ) :
    Lax710763.GraphTransductions.Transduces C (redClass C k) := by
  refine ⟨⟨5, ⊤, fun {r} R => match r, R with | _, .adj => psiF k⟩, ?_⟩
  intro n N hN
  obtain ⟨H, hH, rfl⟩ := hN
  obtain ⟨G, hG, colors, hc⟩ := hH
  refine ⟨n, G.structure, ⟨G, hG, rfl⟩, colors, Function.Embedding.refl _, ?_, ?_⟩
  · intro x
    let := G.structure
    let := colorStructure colors
    change (∃ y : Fin n, y = x) ↔ RealizeIn G.structure colors
      (⊤ : (withColors Language.graph 5).Formula (Fin 1)) ![x]
    unfold RealizeIn
    rw [Language.Formula.realize_top]
    exact iff_true_intro ⟨x, rfl⟩
  · intro r R w
    cases R
    change H.Adj (w 0) (w 1) ↔ RealizeIn G.structure colors (psiF k) w
    rw [hc]
    have : ![w 0, w 1] = w := by ext i; fin_cases i <;> rfl
    rw [this]

theorem monadicallyDependent_redClass (C : GraphClass) (hC : MonadicallyDependent C) (k : ℕ) :
    MonadicallyDependent (redClass C k) :=
  Lax185574Proofs.Lib.MonadicDependenceClosure.monadicallyDependent_of_transduces hC
    (transduces_redClass C k)

end Class

end Lax185574Proofs.Chain
