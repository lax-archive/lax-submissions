import Lax185574.GaifmanLocality
import Lax185574.LocalSubstructure
import Lax185574.LocalToGlobal
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
Proof that the type of a tuple is determined by its type in an induced
substructure containing a ball of radius `7^q` around it, following the
proof of lem:local-to-global. Since the signature may be infinite, each
formula is first restricted to the finite sublanguage of its relation
symbols, to which Gaifman's locality theorem applies.
-/

namespace Lax185574Proofs.LocalToGlobal

open FirstOrder FirstOrder.Language
open Lax185574.FirstOrderTypes Lax185574.GaifmanGraph Lax185574.LocalFormulas
open Lax185574.GaifmanLocality

universe u v z

variable {L : Language.{u, v}}

/-! ### Finite sublanguages -/

/-- The sublanguage with the relation symbols in `S` and no function
symbols. -/
def subLang (S : Set (Σ l, L.Relations l)) : Language.{u, v} :=
  ⟨fun _ => PEmpty, fun l => {R : L.Relations l // (⟨l, R⟩ : Σ l, L.Relations l) ∈ S}⟩

instance (S : Set (Σ l, L.Relations l)) : (subLang S).IsRelational :=
  fun _ => (inferInstance : IsEmpty PEmpty)

instance (S : Set (Σ l, L.Relations l)) [Finite S] : Finite (Σ l, (subLang S).Relations l) := by
  refine Finite.of_injective (fun R : Σ l, (subLang S).Relations l => (⟨⟨R.1, R.2.1⟩, R.2.2⟩ : S))
    ?_
  rintro ⟨l₁, R₁, h₁⟩ ⟨l₂, R₂, h₂⟩ h
  simp only [Subtype.mk.injEq, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq] at h
  subst h
  rfl

theorem subLang_arity (S : Set (Σ l, L.Relations l)) {α : ℕ}
    (hα : ∀ l, α < l → IsEmpty (L.Relations l)) :
    ∀ l, α < l → IsEmpty ((subLang S).Relations l) :=
  fun l hl => ⟨fun R => (hα l hl).false R.1⟩

/-- The inclusion of the sublanguage. -/
def incl (S : Set (Σ l, L.Relations l)) : subLang S →ᴸ L where
  onFunction := fun _ f => PEmpty.elim f
  onRelation := fun _ R => R.1

/-- The structure of the sublanguage on an `L`-structure. -/
@[implicit_reducible]
def subStructure (S : Set (Σ l, L.Relations l)) (M : Type*) [L.Structure M] :
    (subLang S).Structure M where
  funMap f := PEmpty.elim f
  RelMap R x := Structure.RelMap R.1 x

/-- The relation symbols occurring in a formula. -/
def symbols {α : Type*} : {n : ℕ} → L.BoundedFormula α n → Set (Σ l, L.Relations l)
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel R _ => {⟨_, R⟩}
  | _, .imp φ ψ => symbols φ ∪ symbols ψ
  | _, .all φ => symbols φ

theorem symbols_finite {α : Type*} : ∀ {n : ℕ} (φ : L.BoundedFormula α n), (symbols φ).Finite
  | _, .falsum => Set.finite_empty
  | _, .equal _ _ => Set.finite_empty
  | _, .rel _ _ => Set.finite_singleton _
  | _, .imp φ ψ => (symbols_finite φ).union (symbols_finite ψ)
  | _, .all φ => symbols_finite φ

variable [L.IsRelational]

/-- A term of a relational language as a term of the sublanguage. -/
def restrictTerm (S : Set (Σ l, L.Relations l)) {β : Type*} : L.Term β → (subLang S).Term β
  | .var x => .var x
  | .func f _ => isEmptyElim f

/-- A formula as a formula of the sublanguage, where relation atoms with
symbols outside `S` become falsum. -/
noncomputable def restrict (S : Set (Σ l, L.Relations l)) {α : Type*} :
    {n : ℕ} → L.BoundedFormula α n → (subLang S).BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (restrictTerm S t₁) (restrictTerm S t₂)
  | _, .rel R ts => by
    classical
    exact if h : (⟨_, R⟩ : Σ l, L.Relations l) ∈ S then
      .rel (⟨R, h⟩ : (subLang S).Relations _) fun i => restrictTerm S (ts i)
    else .falsum
  | _, .imp φ ψ => .imp (restrict S φ) (restrict S ψ)
  | _, .all φ => .all (restrict S φ)

theorem quantifierRank_restrict (S : Set (Σ l, L.Relations l)) {α : Type*} :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n), quantifierRank (restrict S φ) = quantifierRank φ
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => by
    simp only [restrict]
    split_ifs <;> rfl
  | _, .imp φ ψ => by
    simp only [restrict, quantifierRank, quantifierRank_restrict S φ, quantifierRank_restrict S ψ]
  | _, .all φ => by simp only [restrict, quantifierRank, quantifierRank_restrict S φ]

theorem realize_restrictTerm (S : Set (Σ l, L.Relations l)) {M : Type*} [L.Structure M]
    {β : Type*} (t : L.Term β) (v : β → M) :
    @Term.realize (subLang S) M (subStructure S M) β v (restrictTerm S t) = t.realize v := by
  cases t with
  | var x => rfl
  | func f _ => exact isEmptyElim f

theorem realize_restrict (S : Set (Σ l, L.Relations l)) {M : Type*} [L.Structure M]
    {α : Type*} : ∀ {n : ℕ} (φ : L.BoundedFormula α n), symbols φ ⊆ S → ∀ (v : α → M)
      (xs : Fin n → M),
      (@BoundedFormula.Realize (subLang S) M (subStructure S M) α n (restrict S φ) v xs ↔
        φ.Realize v xs)
  | _, .falsum, _, _, _ => Iff.rfl
  | _, .equal t₁ t₂, _, v, xs => by
    simp only [restrict, BoundedFormula.Realize, realize_restrictTerm]
  | _, .rel R ts, h, v, xs => by
    simp only [restrict]
    rw [dif_pos (h rfl)]
    simp only [BoundedFormula.Realize]
    change Structure.RelMap R _ ↔ _
    simp only [realize_restrictTerm]
  | _, .imp φ ψ, h, v, xs => by
    simp only [restrict, BoundedFormula.realize_imp]
    rw [realize_restrict S φ (fun _ hx => h (Or.inl hx)),
      realize_restrict S ψ (fun _ hx => h (Or.inr hx))]
  | _, .all φ, h, v, xs => by
    simp only [restrict, BoundedFormula.realize_all]
    exact forall_congr' fun x => realize_restrict S φ h v _

omit [L.IsRelational] in
theorem quantifierRank_onBoundedFormula {L' : Language.{u, v}} (ϕ : L' →ᴸ L) {α : Type*} :
    ∀ {n : ℕ} (φ : L'.BoundedFormula α n),
      quantifierRank (ϕ.onBoundedFormula φ) = quantifierRank φ
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp φ ψ => by
    simp only [LHom.onBoundedFormula, quantifierRank, quantifierRank_onBoundedFormula ϕ φ,
      quantifierRank_onBoundedFormula ϕ ψ]
  | _, .all φ => by
    simp only [LHom.onBoundedFormula, quantifierRank, quantifierRank_onBoundedFormula ϕ φ]

omit [L.IsRelational] in
/-- The Gaifman graph of the sublanguage is a subgraph. -/
theorem gaifman_sub_le (S : Set (Σ l, L.Relations l)) (M : Type*) [L.Structure M] :
    @gaifmanGraph (subLang S) M (subStructure S M) ≤ gaifmanGraph L (V := M) := by
  intro a b h
  unfold gaifmanGraph at h ⊢
  rw [SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨hab, h⟩ := h
  refine ⟨hab, ?_⟩
  rcases h with ⟨l, R, x, hx, ha, hb⟩ | ⟨l, R, x, hx, ha, hb⟩
  · exact Or.inl ⟨l, R.1, x, hx, ha, hb⟩
  · exact Or.inr ⟨l, R.1, x, hx, ha, hb⟩

omit [L.IsRelational] in
theorem ball_sub_subset (S : Set (Σ l, L.Relations l)) {M : Type*} [L.Structure M] (r : ℕ)
    {k : ℕ} (a : Fin k → M) :
    @ball (subLang S) M (subStructure S M) r k a ⊆ ball L r a := by
  rintro w ⟨i, p, hp⟩
  exact ⟨i, p.mapLe (gaifman_sub_le S M), by rw [SimpleGraph.Walk.length_mapLe]; exact hp⟩

/-- The induced substructure of the sublanguage is the reduct of the induced
substructure. -/
theorem isExpansionOn_induced (S : Set (Σ l, L.Relations l)) {M : Type*} [L.Structure M]
    (B : Set M) :
    @LHom.IsExpansionOn _ _ (incl S) B (@induced (subLang S) M (subStructure S M) _ B)
      (induced B) :=
  @LHom.IsExpansionOn.mk _ _ (incl S) B (@induced (subLang S) M (subStructure S M) _ B)
    (induced B) (fun f => PEmpty.elim f) (fun _ _ => rfl)

omit [L.IsRelational] in
theorem boolean_agree {S : Set (Σ l, L.Relations l)} {k : ℕ} {P : (subLang S).Formula (Fin k) → Prop}
    {M N : Type*} [(subLang S).Structure M] [(subLang S).Structure N]
    (a : Fin k → M) (b : Fin k → N)
    (hP : ∀ χ, P χ → (χ.Realize a ↔ χ.Realize b)) :
    ∀ {ψ : (subLang S).Formula (Fin k)}, IsBooleanCombination P ψ → (ψ.Realize a ↔ ψ.Realize b)
  | _, .atom h => hP _ h
  | _, .falsum => Iff.rfl
  | _, .imp h₁ h₂ => by
    simp only [Formula.realize_imp]
    rw [boolean_agree a b hP h₁, boolean_agree a b hP h₂]

/--
---
conclusion: Lax185574.LocalToGlobal.rankType_eq_of_rankType_induced_eq
---
Let `q' = p(α, q, k)` be given by `GaifmanLocality`. A formula of rank at
most `q` uses finitely many relation symbols. Over the sublanguage of these
symbols it is equivalent, on finite structures, to a Boolean combination of
basic `7^q`-local sentences and `7^q`-local formulas of rank at most `q'`.
The sentences have the same truth value for both tuples. A local formula
holds of a tuple in the structure if and only if it holds in the induced
substructure, by `LocalSubstructure`, since the balls of the sublanguage are
contained in those of `L`. In the induced substructures, the two tuples
satisfy the same formulas of rank at most `q'`.
-/
theorem rankType_eq_of_rankType_induced_eq (k q α : ℕ) :
    ∃ q' : ℕ, ∀ (L : Language.{u, v}) [L.IsRelational],
      (∀ l, α < l → IsEmpty (L.Relations l)) →
      ∀ (V : Type z) [Finite V] [L.Structure V] (B B' : Set V)
        (a : Fin k → B) (b : Fin k → B'),
        ball L (7 ^ q) (Subtype.val ∘ a) ⊆ B →
        ball L (7 ^ q) (Subtype.val ∘ b) ⊆ B' →
        @rankType L B (induced B) q' k a = @rankType L B' (induced B') q' k b →
        rankType (L := L) q (Subtype.val ∘ a) = rankType (L := L) q (Subtype.val ∘ b) := by
  obtain ⟨p, hp⟩ := exists_local_equivalent.{u, v, z} α q k
  refine ⟨p, fun L _ hα V _ _ B B' a b ha hb hab => ?_⟩
  -- one direction suffices, by symmetry of the hypotheses
  have key : ∀ (B B' : Set V) (a : Fin k → B) (b : Fin k → B'),
      ball L (7 ^ q) (Subtype.val ∘ a) ⊆ B → ball L (7 ^ q) (Subtype.val ∘ b) ⊆ B' →
      @rankType L B (induced B) p k a = @rankType L B' (induced B') p k b →
      ∀ φ : L.Formula (Fin k), quantifierRank φ ≤ q →
        φ.Realize (Subtype.val ∘ a) → φ.Realize (Subtype.val ∘ b) := by
    intro B B' a b ha hb hab φ hq hφ
    classical
    let S := symbols φ
    have : Finite S := (symbols_finite φ).to_subtype
    let _ : (subLang S).Structure V := subStructure S V
    let φ₀ := restrict S φ
    obtain ⟨ψ, hequiv, hbool⟩ := hp (subLang S) (subLang_arity S hα) k le_rfl φ₀
      (by rw [quantifierRank_restrict]; exact hq)
    have hreal : ∀ x : Fin k → V, φ.Realize x ↔ ψ.Realize x := by
      intro x
      rw [← hequiv V x]
      exact (realize_restrict S φ subset_rfl x default).symm
    rw [hreal] at hφ ⊢
    refine (boolean_agree (Subtype.val ∘ a) (Subtype.val ∘ b) ?_ hbool).mp hφ
    intro χ hχ
    rcases hχ with ⟨hloc, hrank⟩ | ⟨σ, -, -, rfl⟩
    · rw [Lax185574.LocalSubstructure.realize_iff_realize_induced (subLang S) (7 ^ q) k χ hloc V
          B a ((ball_sub_subset S _ _).trans ha),
        Lax185574.LocalSubstructure.realize_iff_realize_induced (subLang S) (7 ^ q) k χ hloc V
          B' b ((ball_sub_subset S _ _).trans hb)]
      have hlift : ∀ (C : Set V) (c : Fin k → C),
          @Formula.Realize (subLang S) C (@induced (subLang S) V (subStructure S V) _ C) _ χ c ↔
            ((incl S).onFormula χ) ∈ @rankType L C (induced C) p k c := by
        intro C c
        let _ : L.Structure C := induced C
        let _ : (subLang S).Structure C := @induced (subLang S) V (subStructure S V) _ C
        have := isExpansionOn_induced S C
        simp only [rankType, Set.mem_ofPred_eq, LHom.onFormula, quantifierRank_onBoundedFormula]
        rw [and_iff_right hrank]
        exact (LHom.realize_onFormula (incl S) χ).symm
      rw [hlift B a, hlift B' b, hab]
    · simp only [Formula.realize_relabel]
      exact iff_of_eq (congrArg _ (funext fun e => e.elim))
  ext φ
  simp only [rankType, Set.mem_ofPred_eq]
  refine and_congr_right fun hq => ⟨key B B' a b ha hb hab φ hq, key B' B b a hb ha hab.symm φ hq⟩

end Lax185574Proofs.LocalToGlobal
