import Lax185574.AtomicTypes
import Lax185574.Partitions
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Lax185574Proofs.FlipBasics

/-!
Formulas of quantifier rank 0 only see atomic facts. In a graph, the
type of quantifier rank 0 of a vertex `x` over a set `Y` is therefore
determined by `Y ∩ {x}` and `Y ∩ N(x)`, so the number of atomic types
of the vertices of `X` over `Y` is the number of parts of the partition
into atomic types over `Y` that meet `X`.
-/

namespace Lax185574Proofs.AtomicTypeBridge

open FirstOrder FirstOrder.Language Structure
open Lax185574.FirstOrderTypes Lax185574.AtomicTypes Lax185574.Partitions

universe u v w z

section General

variable {L : Language.{u, v}} [L.IsRelational]

/-- The variable of a term of a relational language. -/
def termVar {β : Type w} : L.Term β → β
  | .var a => a
  | .func f _ => isEmptyElim f

theorem term_eq_var {β : Type w} (t : L.Term β) : t = .var (termVar t) := by
  cases t with
  | var a => rfl
  | func f _ => exact isEmptyElim f

theorem realize_term {M : Type z} [L.Structure M] {β : Type w} (t : L.Term β) (e : β → M) :
    t.realize e = e (termVar t) := by
  rw [term_eq_var t]; rfl

/-- A formula of quantifier rank 0 holds for two valuations alike if they
satisfy the same equalities and the same relations. -/
theorem realize_congr_of_rank_zero {M : Type z} [L.Structure M] {α : Type w} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), quantifierRank φ = 0 →
      ∀ (f g : α → M) (xs ys : Fin n → M),
      (∀ a b, Sum.elim f xs a = Sum.elim f xs b ↔ Sum.elim g ys a = Sum.elim g ys b) →
      (∀ (l : ℕ) (R : L.Relations l) (x : Fin l → α ⊕ Fin n),
        RelMap R (Sum.elim f xs ∘ x) ↔ RelMap R (Sum.elim g ys ∘ x)) →
      (φ.Realize f xs ↔ φ.Realize g ys)
  | _, .falsum, _, _, _, _, _, _, _ => Iff.rfl
  | _, .equal t₁ t₂, _, f, g, xs, ys, heq, _ => by
      simp only [BoundedFormula.Realize, realize_term]
      exact heq _ _
  | _, .rel R ts, _, f, g, xs, ys, _, hrel => by
      simp only [BoundedFormula.Realize, realize_term]
      exact hrel _ R fun i => termVar (ts i)
  | _, .imp φ ψ, h, f, g, xs, ys, heq, hrel => by
      have h' : quantifierRank φ = 0 ∧ quantifierRank ψ = 0 := by
        simp only [quantifierRank] at h; omega
      simp only [BoundedFormula.Realize]
      rw [realize_congr_of_rank_zero φ h'.1 f g xs ys heq hrel,
        realize_congr_of_rank_zero ψ h'.2 f g xs ys heq hrel]
  | _, .all _, h, _, _, _, _, _, _ => by simp [quantifierRank] at h

/-- Two images of a set have the same size if the two maps identify the
same elements. -/
theorem ncard_image_congr {α : Type u} {β : Type v} {γ : Type w} {S : Set α}
    (f : α → β) (g : α → γ) (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y ↔ g x = g y) :
    (f '' S).ncard = (g '' S).ncard := by
  classical
  refine Set.ncard_congr (fun b hb => g (Classical.choose hb)) ?_ ?_ ?_
  · intro b hb
    exact ⟨_, (Classical.choose_spec hb).1, rfl⟩
  · intro b b' hb hb' e
    have h1 := Classical.choose_spec hb
    have h2 := Classical.choose_spec hb'
    rw [← h1.2, ← h2.2]
    exact (h _ h1.1 _ h2.1).mpr e
  · rintro c ⟨x, hx, rfl⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    have h1 := Classical.choose_spec (⟨x, hx, rfl⟩ : f x ∈ f '' S)
    exact (h _ h1.1 _ hx).mp h1.2

end General

section Graph

variable {V : Type z}

/-- The formula `x₀ = y` for a parameter `y`. -/
def eqParam {Y : Set V} (y : Y) : Language.graph.Formula (Fin 1 ⊕ Y) :=
  Term.equal (Term.var (Sum.inl 0)) (Term.var (Sum.inr y))

/-- The formula `E(x₀, y)` for a parameter `y`. -/
def adjParam {Y : Set V} (y : Y) : Language.graph.Formula (Fin 1 ⊕ Y) :=
  Relations.formula₂ Language.adj (Term.var (Sum.inl 0)) (Term.var (Sum.inr y))

/-- In a graph, two vertices have the same type of quantifier rank 0 over
`Y` exactly when they lie in the same part of the partition into atomic
types over `Y`. -/
theorem rankTypeOver_zero_eq_iff (G : SimpleGraph V) (Y : Set V) (x x' : V) :
    @rankTypeOver Language.graph V G.structure 0 Y 1 ![x] =
        @rankTypeOver Language.graph V G.structure 0 Y 1 ![x'] ↔
      atomicTypes G Y x x' := by
  let _ := G.structure
  rw [Lax185574Proofs.FlipBasics.atomicTypes_rel_iff']
  constructor
  · intro h
    have mem : ∀ φ : Language.graph.Formula (Fin 1 ⊕ Y), quantifierRank φ = 0 →
        (φ.Realize (Sum.elim ![x] Subtype.val) ↔ φ.Realize (Sum.elim ![x'] Subtype.val)) := by
      intro φ hφ
      have := congrArg (fun T => φ ∈ T) h
      simp only [rankTypeOver, Set.mem_ofPred_eq, hφ, le_refl, true_and] at this
      exact Iff.of_eq this
    have heq : ∀ y : Y, (x = y ↔ x' = y) := fun y => by
      exact mem (eqParam y) rfl
    have hadj : ∀ y : Y, (G.Adj x y ↔ G.Adj x' y) := fun y => by
      exact mem (adjParam y) rfl
    by_cases hxx : x = x'
    · exact Or.inl hxx
    right
    refine ⟨fun hx => hxx ((heq ⟨x, hx⟩).mp rfl).symm, fun hx => hxx ((heq ⟨x', hx⟩).mpr rfl),
      fun s hs => hadj ⟨s, hs⟩⟩
  · rintro (rfl | ⟨hx, hx', hadj⟩)
    · rfl
    ext φ
    simp only [rankTypeOver, Set.mem_ofPred_eq]
    refine and_congr_right fun hφ => ?_
    have hφ : quantifierRank φ = 0 := by omega
    let e : (Fin 1 ⊕ Y) ⊕ Fin 0 → V := Sum.elim (Sum.elim ![x] Subtype.val) default
    let e' : (Fin 1 ⊕ Y) ⊕ Fin 0 → V := Sum.elim (Sum.elim ![x'] Subtype.val) default
    have P : ∀ a, (e a = x ∧ e' a = x') ∨ (e a = e' a ∧ e a ∈ Y) := by
      rintro ((i | y) | i)
      · left; fin_cases i; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, y.2⟩
      · exact i.elim0
    refine realize_congr_of_rank_zero φ hφ _ _ default default ?_ ?_
    · intro a b
      change e a = e b ↔ e' a = e' b
      rcases P a with ⟨ha, ha'⟩ | ⟨ha, hY⟩ <;> rcases P b with ⟨hb, hb'⟩ | ⟨hb, hY'⟩
      · rw [ha, ha', hb, hb']; simp
      · rw [ha, ha', ← hb]
        exact ⟨fun h => absurd (h ▸ hY') hx, fun h => absurd (h ▸ hY') hx'⟩
      · rw [hb, hb', ← ha]
        exact ⟨fun h => absurd (h ▸ hY) hx, fun h => absurd (h ▸ hY) hx'⟩
      · rw [ha, hb]
    · intro l R xx
      cases R
      change G.Adj (e (xx 0)) (e (xx 1)) ↔ G.Adj (e' (xx 0)) (e' (xx 1))
      rcases P (xx 0) with ⟨ha, ha'⟩ | ⟨ha, hY⟩ <;>
        rcases P (xx 1) with ⟨hb, hb'⟩ | ⟨hb, hY'⟩
      · rw [ha, ha', hb, hb']; simp
      · rw [ha, ha', ← hb]; exact hadj _ hY'
      · rw [hb, hb', ← ha, G.adj_comm, G.adj_comm _ x']; exact hadj _ hY
      · rw [ha, hb]

/-- The number of atomic types over `Y` of the vertices of `X` is the
number of parts of the partition into atomic types over `Y` that meet
`X`. -/
theorem atomicTypeCount_eq_partCount (G : SimpleGraph V) (X Y : Set V) :
    atomicTypeCount G X Y = partCount (atomicTypes G Y) X := by
  unfold atomicTypeCount typeCountOver typesOver partCount
  have h1 : {v : Fin 1 → V | ∀ i, v i ∈ X} = (fun x => ![x]) '' X := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro h; exact ⟨v 0, h 0, by ext i; fin_cases i; rfl⟩
    · rintro ⟨x, hx, rfl⟩ i; fin_cases i; exact hx
  rw [h1, Set.image_image]
  refine ncard_image_congr _ _ fun x _ y _ => ?_
  rw [rankTypeOver_zero_eq_iff, Quotient.eq]

end Graph

end Lax185574Proofs.AtomicTypeBridge
