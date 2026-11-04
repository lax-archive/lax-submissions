import Lax185574.FirstOrderTypes
import Lax185574.GaifmanGraph
import Lax185574Proofs.DistanceFormulaRank
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
Naming parameters by relations. For a relational language `L` and a type
`P` of parameters, the language `L⁺` has a relation symbol for every
relation symbol `R` of `L` together with a pattern that fills some
positions of `R` by parameters and the others by the arguments of the new
symbol, every argument being used. It also has a unary symbol `P_u` for
every parameter `u`. A structure `A` with an embedding `e` of the
parameters becomes an `L⁺`-structure `A⁺`, where a lifted symbol holds of a
tuple if `R` holds of the filled tuple, and `P_u` holds of `e u` only.

A formula of `L` with parameters becomes a formula of `L⁺` without
parameters and with the same quantifier rank. The Gaifman graph of `A⁺` is
a subgraph of that of `A`. On a set `B` that contains no parameter and no
neighbor of a parameter, the symbols involving parameters are trivial, so
`L⁺`-formulas over `A⁺[B]` translate back into `L`-formulas over `A[B]`.
This is the expansion `H⁺` in the proof of lem:sep-types, which uses the
symbols `P_u` and `N_u` for graphs.
-/

namespace Lax185574Proofs.ParameterExpansion

open FirstOrder FirstOrder.Language
open Lax185574.FirstOrderTypes Lax185574.GaifmanGraph Lax185574Proofs.DistanceFormulaRank

universe u v w z

/-- A tuple of parameters and other values, presented as a pattern and the
tuple of the other values, so that every position of the pattern is used. -/
structure Split {P T : Type*} {l : ℕ} (c : Fin l → P ⊕ T) where
  /-- The number of positions that are not parameters. -/
  j : ℕ
  /-- The pattern: a parameter or a position of `args`, for every entry. -/
  pat : Fin l → P ⊕ Fin j
  /-- The values that are not parameters. -/
  args : Fin j → T
  surj : ∀ i, ∃ p, pat p = Sum.inr i
  spec : ∀ p, c p = Sum.map id args (pat p)

theorem nonempty_split {P T : Type*} {l : ℕ} (c : Fin l → P ⊕ T) : Nonempty (Split c) := by
  classical
  let S := {p : Fin l // ∃ t, c p = Sum.inr t}
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hleft : ∀ p, ¬ (∃ t, c p = Sum.inr t) → ∃ x, c p = Sum.inl x := by
    intro p hp
    cases hc : c p with
    | inl x => exact ⟨x, rfl⟩
    | inr t => exact absurd ⟨t, hc⟩ hp
  refine ⟨⟨Fintype.card S, fun p => if h : ∃ t, c p = Sum.inr t then Sum.inr (e ⟨p, h⟩)
    else Sum.inl (hleft p h).choose, fun i => (e.symm i).2.choose, fun i => ⟨(e.symm i).1, ?_⟩,
    fun p => ?_⟩⟩
  · simp only [(e.symm i).2, dif_pos]
    simp
  · by_cases h : ∃ t, c p = Sum.inr t
    · simp only [h, dif_pos, Sum.map_inr, Equiv.symm_apply_apply]
      exact h.choose_spec
    · simp only [h, dif_neg, not_false_eq_true, Sum.map_inl, id]
      exact (hleft p h).choose_spec

/-- A chosen split of a tuple. -/
noncomputable def split {P T : Type*} {l : ℕ} (c : Fin l → P ⊕ T) : Split c :=
  Classical.choice (nonempty_split c)

variable (L : Language.{u, v}) (P : Type w)

/-- The relation symbols of `L⁺` of arity `j`. -/
inductive PlusRel : ℕ → Type (max v w)
  /-- The symbol `R` of `L` with some positions filled by parameters. -/
  | lift {l j : ℕ} (R : L.Relations l) (pat : Fin l → P ⊕ Fin j)
      (surj : ∀ i, ∃ p, pat p = Sum.inr i) : PlusRel j
  /-- The unary symbol `P_u` that holds of the parameter `u` only. -/
  | point (u : P) : PlusRel 1

/-- The language `L⁺` naming the parameters `P`. -/
def plusLang : Language.{0, max v w} := ⟨fun _ => Empty, PlusRel L P⟩

instance : (plusLang L P).IsRelational := fun _ => (inferInstance : IsEmpty Empty)

variable {L P}

/-- The structure `A⁺` on a structure `A` with an embedding `e` of the
parameters. -/
@[implicit_reducible]
def plusStructure {M : Type z} [L.Structure M] (e : P → M) : (plusLang L P).Structure M where
  funMap f := Empty.elim f
  RelMap {j} R x := match j, R with
    | _, .lift R pat _ => Structure.RelMap R fun p => Sum.elim e x (pat p)
    | _, .point u => x 0 = e u

theorem plusLang_arity (α : ℕ) (hα : ∀ l, α < l → IsEmpty (L.Relations l)) (h1 : 1 ≤ α) :
    ∀ j, α < j → IsEmpty ((plusLang L P).Relations j) := by
  intro j hj
  refine ⟨fun R => ?_⟩
  change PlusRel L P j at R
  cases R with
  | @lift l j R pat surj =>
    have hl : l ≤ α := by
      by_contra hc
      exact (hα l (by omega)).false R
    -- `pat` hits every position of `Fin j`, so `j ≤ l`
    have hjl : j ≤ l := by
      have hs : Function.Surjective fun p : {p : Fin l // (pat p).isRight} =>
          (pat p.1).getRight p.2 := by
        intro i
        obtain ⟨p, hp⟩ := surj i
        exact ⟨⟨p, by simp [hp]⟩, by simp [hp]⟩
      have := Fintype.card_le_of_surjective _ hs
      simp only [Fintype.card_fin] at this
      exact this.trans ((Fintype.card_subtype_le _).trans (by simp))
    omega
  | point u => omega

/-! ### From formulas with parameters to formulas of `L⁺` -/

variable [L.IsRelational]

/-- A term of `L` over the free variables `x̄`, the parameters and the bound
variables, classified as a parameter or as a variable term of `L⁺`. -/
def classify {k n : ℕ} : L.Term ((Fin k ⊕ P) ⊕ Fin n) → P ⊕ (plusLang L P).Term (Fin k ⊕ Fin n)
  | .var (.inl (.inl i)) => Sum.inr (.var (.inl i))
  | .var (.inl (.inr u)) => Sum.inl u
  | .var (.inr m) => Sum.inr (.var (.inr m))
  | .func f _ => isEmptyElim f

section realize

variable {M : Type z} [L.Structure M] (e : P → M)

theorem realize_classify_inl {k n : ℕ} (t : L.Term ((Fin k ⊕ P) ⊕ Fin n)) (u : P)
    (h : classify t = Sum.inl u) (a : Fin k → M) (xs : Fin n → M) :
    t.realize (Sum.elim (Sum.elim a e) xs) = e u := by
  match t, h with
  | .var (.inl (.inr u')), h =>
    simp only [classify, Sum.inl.injEq] at h
    subst h
    rfl
  | .var (.inl (.inl i)), h => simp [classify] at h
  | .var (.inr m), h => simp [classify] at h
  | .func f _, _ => exact isEmptyElim f

theorem realize_classify_inr {k n : ℕ} (t : L.Term ((Fin k ⊕ P) ⊕ Fin n))
    (t' : (plusLang L P).Term (Fin k ⊕ Fin n))
    (h : classify t = Sum.inr t') (a : Fin k → M) (xs : Fin n → M) :
    t.realize (Sum.elim (Sum.elim a e) xs) =
      @Term.realize (plusLang L P) M (plusStructure e) _ (Sum.elim a xs) t' := by
  match t, h with
  | .var (.inl (.inl i)), h =>
    simp only [classify, Sum.inr.injEq] at h
    subst h
    rfl
  | .var (.inr m), h =>
    simp only [classify, Sum.inr.injEq] at h
    subst h
    rfl
  | .var (.inl (.inr u')), h => simp [classify] at h
  | .func f _, _ => exact isEmptyElim f

end realize

/-- The translation of an equality atom. -/
noncomputable def toPlusEqual {k n : ℕ} :
    P ⊕ (plusLang L P).Term (Fin k ⊕ Fin n) → P ⊕ (plusLang L P).Term (Fin k ⊕ Fin n) →
      (plusLang L P).BoundedFormula (Fin k) n
  | .inr a, .inr b => .equal a b
  | .inr a, .inl u => .rel (PlusRel.point u : (plusLang L P).Relations 1) ![a]
  | .inl u, .inr b => .rel (PlusRel.point u : (plusLang L P).Relations 1) ![b]
  | .inl u, .inl u' => by
    classical
    exact if u = u' then ∼⊥ else ⊥

/-- The translation of a relation atom. -/
noncomputable def toPlusRel {k n l : ℕ} (R : L.Relations l)
    (c : Fin l → P ⊕ (plusLang L P).Term (Fin k ⊕ Fin n)) :
    (plusLang L P).BoundedFormula (Fin k) n :=
  .rel (PlusRel.lift R (split c).pat (split c).surj : (plusLang L P).Relations _)
    (split c).args

/-- The translation of a formula with parameters into a formula of `L⁺`. -/
noncomputable def toPlus {k : ℕ} : {n : ℕ} → L.BoundedFormula (Fin k ⊕ P) n →
    (plusLang L P).BoundedFormula (Fin k) n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => toPlusEqual (classify t₁) (classify t₂)
  | _, .rel R ts => toPlusRel R fun p => classify (ts p)
  | _, .imp φ ψ => .imp (toPlus φ) (toPlus ψ)
  | _, .all φ => .all (toPlus φ)

theorem quantifierRank_toPlus {k : ℕ} : ∀ {n : ℕ} (φ : L.BoundedFormula (Fin k ⊕ P) n),
    quantifierRank (toPlus φ) = quantifierRank φ
  | _, .falsum => rfl
  | _, .equal t₁ t₂ => by
    simp only [toPlus, quantifierRank]
    cases classify t₁ <;> cases classify t₂ <;> simp only [toPlusEqual, quantifierRank]
    split_ifs <;> rfl
  | _, .rel R ts => rfl
  | _, .imp φ ψ => by simp only [toPlus, quantifierRank, quantifierRank_toPlus φ,
      quantifierRank_toPlus ψ]
  | _, .all φ => by simp only [toPlus, quantifierRank, quantifierRank_toPlus φ]

theorem realize_toPlus {M : Type z} [L.Structure M] (e : P → M) (he : Function.Injective e)
    {k : ℕ} : ∀ {n : ℕ} (φ : L.BoundedFormula (Fin k ⊕ P) n) (a : Fin k → M) (xs : Fin n → M),
      (@BoundedFormula.Realize (plusLang L P) M (plusStructure e) _ _ (toPlus φ) a xs ↔
        φ.Realize (Sum.elim a e) xs)
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal t₁ t₂, a, xs => by
    simp only [toPlus, BoundedFormula.Realize]
    rcases h₁ : classify t₁ with u₁ | s₁ <;> rcases h₂ : classify t₂ with u₂ | s₂
    · rw [realize_classify_inl e t₁ u₁ h₁, realize_classify_inl e t₂ u₂ h₂]
      simp only [toPlusEqual]
      split_ifs with hu
      · subst hu; simp
      · simp only [BoundedFormula.realize_bot, false_iff]
        exact fun h => hu (he h)
    · rw [realize_classify_inl e t₁ u₁ h₁, realize_classify_inr e t₂ s₂ h₂]
      simp only [toPlusEqual, BoundedFormula.Realize]
      change _ = e u₁ ↔ _
      simp only [Matrix.cons_val_zero]
      exact eq_comm
    · rw [realize_classify_inr e t₁ s₁ h₁, realize_classify_inl e t₂ u₂ h₂]
      simp only [toPlusEqual, BoundedFormula.Realize]
      change _ = e u₂ ↔ _
      simp only [Matrix.cons_val_zero]
    · rw [realize_classify_inr e t₁ s₁ h₁, realize_classify_inr e t₂ s₂ h₂]
      simp only [toPlusEqual, BoundedFormula.Realize]
  | _, .rel R ts, a, xs => by
    simp only [toPlus, toPlusRel, BoundedFormula.Realize]
    set c := fun p => classify (ts p)
    have hspec := (split c).spec
    change Structure.RelMap R _ ↔ _
    congr! 1
    funext p
    have hp := hspec p
    simp only [c] at hp
    rcases hq : (split c).pat p with u | i
    · rw [hq] at hp
      simp only [Sum.map_inl, id] at hp
      simp only [Sum.elim_inl]
      exact (realize_classify_inl e (ts p) u hp a xs).symm
    · rw [hq] at hp
      simp only [Sum.map_inr] at hp
      simp only [Sum.elim_inr]
      exact (realize_classify_inr e (ts p) _ hp a xs).symm
  | _, .imp φ ψ, a, xs => by
    simp only [toPlus, BoundedFormula.realize_imp]
    rw [realize_toPlus e he φ, realize_toPlus e he ψ]
  | _, .all φ, a, xs => by
    simp only [toPlus, BoundedFormula.realize_all]
    exact forall_congr' fun x => realize_toPlus e he φ a _

/-! ### The Gaifman graph of `A⁺` -/

omit [L.IsRelational] in
theorem gaifman_plus_le {M : Type z} [L.Structure M] (e : P → M) :
    @gaifmanGraph (plusLang L P) M (plusStructure e) ≤ gaifmanGraph L (V := M) := by
  intro a b h
  unfold gaifmanGraph at h ⊢
  rw [SimpleGraph.fromRel_adj] at h ⊢
  obtain ⟨hab, h⟩ := h
  refine ⟨hab, ?_⟩
  have key : ∀ a b : M, (∃ (l : ℕ) (R : (plusLang L P).Relations l) (x : Fin l → M),
      @Structure.RelMap (plusLang L P) M (plusStructure e) l R x ∧ a ∈ Set.range x ∧
        b ∈ Set.range x) → a ≠ b →
      ∃ (l : ℕ) (R : L.Relations l) (x : Fin l → M),
        Structure.RelMap R x ∧ a ∈ Set.range x ∧ b ∈ Set.range x := by
    rintro a b ⟨j, R, x, hx, ⟨i₁, rfl⟩, ⟨i₂, rfl⟩⟩ hne
    change PlusRel L P j at R
    cases R with
    | lift R pat surj =>
      obtain ⟨p₁, hp₁⟩ := surj i₁
      obtain ⟨p₂, hp₂⟩ := surj i₂
      refine ⟨_, R, fun p => Sum.elim e x (pat p), hx, ⟨p₁, by simp [hp₁]⟩, ⟨p₂, by simp [hp₂]⟩⟩
    | point u =>
      exact absurd (congrArg x (Subsingleton.elim i₁ i₂)) hne
  rcases h with h | h
  · exact Or.inl (key a b h hab)
  · exact Or.inr (key b a h (Ne.symm hab))

omit [L.IsRelational] in
theorem withinDist_of_plus {M : Type z} [L.Structure M] (e : P → M) {d : ℕ} {a b : M}
    (h : WithinDist (@gaifmanGraph (plusLang L P) M (plusStructure e)) d a b) :
    WithinDist (gaifmanGraph L (V := M)) d a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.mapLe (gaifman_plus_le e), by rw [SimpleGraph.Walk.length_mapLe]; exact hp⟩

/-! ### Back from `L⁺` to `L` away from the parameters -/

/-- A variable term of `L⁺` as a term of `L`. -/
def termBack {α : Type*} : (plusLang L P).Term α → L.Term α
  | .var s => .var s
  | .func f _ => Empty.elim f

omit [L.IsRelational] in
theorem realize_termBack {α : Type*} {N : Type*} [L.Structure N]
    [(plusLang L P).Structure N] (t : (plusLang L P).Term α) (v : α → N) :
    (termBack t).realize v = t.realize v := by
  cases t with
  | var s => rfl
  | func f _ => exact Empty.elim f

theorem elim_eq_getRight {M : Type z} (e : P → M) {j : ℕ} (f : Fin j → M) (s : P ⊕ Fin j)
    (h : s.isRight) : Sum.elim e f s = f (s.getRight h) := by
  cases s with
  | inl x => simp at h
  | inr i => rfl

section back

variable {M : Type z} [L.Structure M] (e : P → M)

/-- The translation of a relation atom of `L⁺` on a set without parameters
and their neighbors. -/
noncomputable def fromPlusRel {k n : ℕ} : {j : ℕ} → PlusRel L P j →
    (Fin j → (plusLang L P).Term (Fin k ⊕ Fin n)) → L.BoundedFormula (Fin k) n
  | j, .lift R pat _, ts => by
    classical
    exact if hall : ∀ p, (pat p).isRight then
        .rel R fun p => termBack (ts ((pat p).getRight (hall p)))
      else if hj : j = 0 then
        (if Structure.RelMap R (fun p => Sum.elim e (fun i => (Fin.cast hj i).elim0) (pat p))
          then ∼⊥ else ⊥)
      else ⊥
  | _, .point _, _ => ⊥

/-- The translation of a formula of `L⁺` into a formula of `L`, valid on sets
without parameters and their neighbors. -/
noncomputable def fromPlus {k : ℕ} : {n : ℕ} → (plusLang L P).BoundedFormula (Fin k) n →
    L.BoundedFormula (Fin k) n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (termBack t₁) (termBack t₂)
  | _, .rel R ts => fromPlusRel e R ts
  | _, .imp φ ψ => .imp (fromPlus φ) (fromPlus ψ)
  | _, .all φ => .all (fromPlus φ)

omit [L.IsRelational] in
theorem quantifierRank_fromPlus {k : ℕ} : ∀ {n : ℕ} (φ : (plusLang L P).BoundedFormula (Fin k) n),
    quantifierRank (fromPlus e φ) = quantifierRank φ
  | _, .falsum => rfl
  | _, .equal t₁ t₂ => rfl
  | _, .rel R ts => by
    change PlusRel L P _ at R
    cases R with
    | lift R pat surj =>
      simp only [fromPlus, fromPlusRel, quantifierRank]
      split_ifs <;> rfl
    | point u => rfl
  | _, .imp φ ψ => by simp only [fromPlus, quantifierRank, quantifierRank_fromPlus φ,
      quantifierRank_fromPlus ψ]
  | _, .all φ => by simp only [fromPlus, quantifierRank, quantifierRank_fromPlus φ]

omit [L.IsRelational] in
theorem relMap_induced_lift (B : Set M) {l j : ℕ} (R : L.Relations l)
    (pat : Fin l → P ⊕ Fin j) (surj : ∀ i, ∃ p, pat p = Sum.inr i) (x : Fin j → B) :
    @Structure.RelMap (plusLang L P) B (@induced (plusLang L P) M (plusStructure e) _ B) j
        (PlusRel.lift R pat surj) x ↔
      Structure.RelMap R (fun p => Sum.elim e (Subtype.val ∘ x) (pat p)) := Iff.rfl

omit [L.IsRelational] in
theorem relMap_induced_point (B : Set M) (u : P) (x : Fin 1 → B) :
    @Structure.RelMap (plusLang L P) B (@induced (plusLang L P) M (plusStructure e) _ B) 1
        (PlusRel.point u) x ↔ (x 0).val = e u := Iff.rfl

theorem relMap_induced (B : Set M) {l : ℕ} (R : L.Relations l) (x : Fin l → B) :
    @Structure.RelMap L B (induced B) l R x ↔ Structure.RelMap R (Subtype.val ∘ x) := Iff.rfl

theorem realize_fromPlusRel (B : Set M)
    (hfar : ∀ b ∈ B, ∀ u, b ≠ e u ∧ ¬ (gaifmanGraph L (V := M)).Adj b (e u)) {k n j : ℕ}
    (R : PlusRel L P j) (ts : Fin j → (plusLang L P).Term (Fin k ⊕ Fin n)) (a : Fin k → B)
    (xs : Fin n → B) :
    (@BoundedFormula.Realize L B (induced B) _ _ (fromPlusRel e R ts) a xs ↔
      @Structure.RelMap (plusLang L P) B (@induced (plusLang L P) M (plusStructure e) _ B) j R
        (fun i => @Term.realize (plusLang L P) B
          (@induced (plusLang L P) M (plusStructure e) _ B) _ (Sum.elim a xs) (ts i))) := by
  cases R with
  | @lift l j R pat surj =>
    rw [relMap_induced_lift]
    simp only [fromPlusRel]
    split_ifs with hall hj hrel
    · simp only [BoundedFormula.Realize]
      rw [relMap_induced]
      congr! 1
      funext p
      rw [Function.comp_apply, @realize_termBack L P _ B (induced B)
        (@induced (plusLang L P) M (plusStructure e) _ B)]
      rw [elim_eq_getRight e _ (pat p) (hall p)]
      rfl
    · subst hj
      simp only [BoundedFormula.realize_not, BoundedFormula.realize_bot, not_false_eq_true,
        true_iff]
      convert hrel using 3 with p
    · subst hj
      simp only [BoundedFormula.realize_bot, false_iff]
      convert hrel using 3 with p
      congr 1
      funext i
      exact i.elim0
    · simp only [BoundedFormula.realize_bot, false_iff]
      intro hR
      push Not at hall
      obtain ⟨p₀, hp₀⟩ := hall
      obtain ⟨u, hu⟩ : ∃ u, pat p₀ = Sum.inl u := by
        cases hq : pat p₀ with
        | inl u => exact ⟨u, rfl⟩
        | inr i => simp [hq] at hp₀
      obtain ⟨i₀⟩ : Nonempty (Fin j) := ⟨⟨0, Nat.pos_of_ne_zero hj⟩⟩
      obtain ⟨p₁, hp₁⟩ := surj i₀
      set y : Fin j → B := fun i => @Term.realize (plusLang L P) B
          (@induced (plusLang L P) M (plusStructure e) _ B) _ (Sum.elim a xs) (ts i)
      have hb := hfar (y i₀).val (y i₀).2 u
      by_cases heq : (y i₀).val = e u
      · exact hb.1 heq
      · apply hb.2
        unfold gaifmanGraph
        rw [SimpleGraph.fromRel_adj]
        exact ⟨heq, Or.inl ⟨l, R, _, hR, ⟨p₁, by simp [hp₁]⟩, ⟨p₀, by simp [hu]⟩⟩⟩
  | point u =>
    rw [relMap_induced_point]
    simp only [fromPlusRel, BoundedFormula.realize_bot, false_iff]
    exact (hfar _ (Subtype.prop _) u).1

theorem realize_fromPlus (B : Set M)
    (hfar : ∀ b ∈ B, ∀ u, b ≠ e u ∧ ¬ (gaifmanGraph L (V := M)).Adj b (e u)) {k : ℕ} :
    ∀ {n : ℕ} (φ : (plusLang L P).BoundedFormula (Fin k) n) (a : Fin k → B) (xs : Fin n → B),
      (@BoundedFormula.Realize L B (induced B) _ _ (fromPlus e φ) a xs ↔
        @BoundedFormula.Realize (plusLang L P) B
          (@induced (plusLang L P) M (plusStructure e) _ B) _ _ φ a xs)
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal t₁ t₂, a, xs => by
    simp only [fromPlus, BoundedFormula.Realize]
    rw [@realize_termBack L P _ B (induced B) (@induced (plusLang L P) M (plusStructure e) _ B),
      @realize_termBack L P _ B (induced B) (@induced (plusLang L P) M (plusStructure e) _ B)]
  | _, .rel R ts, a, xs => realize_fromPlusRel e B hfar R ts a xs
  | _, .imp φ ψ, a, xs => by
    simp only [fromPlus, BoundedFormula.realize_imp]
    rw [realize_fromPlus B hfar φ, realize_fromPlus B hfar ψ]
  | _, .all φ, a, xs => by
    simp only [fromPlus, BoundedFormula.realize_all]
    exact forall_congr' fun x => realize_fromPlus B hfar φ a _

end back

end Lax185574Proofs.ParameterExpansion
