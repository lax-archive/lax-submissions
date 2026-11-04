import Lax185574.LocalFormulas
import Lax185574.GaifmanLocality
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Tactic.FinCases
import Lax185574.FirstOrderTypes
import Lax185574Proofs.DistanceFormulas
import Lax185574Proofs.DistanceFormulaRank
import Lax185574Proofs.Gaifman.Depth

/-!
Translation between mathlib's first-order logic over a finite relational
language and the syntax of the Gaifman normal form.

The vocabulary of a language `L` with finitely many relation symbols has one
relation symbol for every relation symbol of `L`, in the order of a fixed
enumeration, and in addition a nullary symbol that is interpreted as false
and expresses falsum. Formulas of `L` translate into formulas of the
vocabulary with the same quantifier rank and the same meaning. Local formulas
and basic local sentences of the normal form translate back into local formulas
and basic local sentences in the sense of `Lax185574.LocalFormulas`, where the
ball guards are the dist formulas.
-/

namespace Lax185574Proofs.GaifmanTranslation

open FirstOrder FirstOrder.Language
open Lax185574.FirstOrderTypes Lax185574.GaifmanGraph Lax185574.LocalFormulas
open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.GaifmanNormalForm

universe u v z

variable (L : Language.{u, v}) [Finite (Σ l, L.Relations l)]

/-- The number of relation symbols of `L`. -/
noncomputable def symbolCount : ℕ := Nat.card (Σ l, L.Relations l)

/-- A fixed enumeration of the relation symbols of `L`. -/
noncomputable def enum : (Σ l, L.Relations l) ≃ Fin (symbolCount L) := Finite.equivFin _

/-- The vocabulary of `L`: symbol `0` is a nullary symbol for falsum, and
symbol `i + 1` is the `i`-th relation symbol of `L`. -/
noncomputable def vocab : Vocabulary where
  relationCount := symbolCount L + 1
  relationArity := Fin.cases 0 fun i => ((enum L).symm i).1
  constantCount := 0

variable {L}

theorem vocab_arityLE {α : ℕ} (hα : ∀ l, α < l → IsEmpty (L.Relations l)) :
    Lax185574Proofs.Gaifman.Depth.ArityLE (vocab L) α := by
  intro R
  refine Fin.cases (Nat.zero_le _) (fun i => ?_) R
  change ((enum L).symm i).1 ≤ α
  by_contra h
  exact (hα _ (by omega)).false ((enum L).symm i).2

/-- The structure of the vocabulary on an `L`-structure. -/
def structOf (M : Type z) [L.Structure M] : Structure (vocab L) M where
  relation := Fin.cases (motive := fun R => (Fin ((vocab L).arity R) → M) → Prop)
    (fun _ => False) fun i x => Structure.RelMap ((enum L).symm i).2 x
  constant := Fin.elim0

omit [Finite (Σ l, L.Relations l)] in
theorem relMap_cast {M : Type z} [L.Structure M] {s t : Σ l, L.Relations l} (h : s = t)
    (x : Fin t.1 → M) :
    Structure.RelMap s.2 (x ∘ Fin.cast (congrArg Sigma.fst h)) ↔ Structure.RelMap t.2 x := by
  subst h
  rfl

theorem arity_succ_enum (s : Σ l, L.Relations l) :
    (vocab L).arity ((enum L) s).succ = s.1 := by
  change ((enum L).symm ((enum L) s)).1 = s.1
  rw [Equiv.symm_apply_apply]

theorem relation_succ_enum {M : Type z} [L.Structure M] (s : Σ l, L.Relations l)
    (x : Fin s.1 → M) :
    (structOf (L := L) M).relation ((enum L) s).succ (x ∘ Fin.cast (arity_succ_enum s)) ↔
      Structure.RelMap s.2 x := by
  change Structure.RelMap ((enum L).symm ((enum L) s)).2 _ ↔ _
  exact relMap_cast (Equiv.symm_apply_apply (enum L) s) x

/-! ### Gaifman adjacency and distance -/

theorem adjacent_iff {M : Type z} [L.Structure M] (a b : M) :
    gaifmanAdjacent (structOf (L := L) M) a b ↔ (gaifmanGraph L (V := M)).Adj a b := by
  unfold gaifmanAdjacent gaifmanGraph
  rw [SimpleGraph.fromRel_adj]
  refine and_congr_right fun hab => ?_
  constructor
  · rintro ⟨R, x, hx, i, j, -, rfl, rfl⟩
    induction R using Fin.cases with
    | zero => exact hx.elim
    | succ R =>
      exact Or.inl ⟨_, ((enum L).symm R).2, x, hx, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
  · have key : ∀ a b : M, a ≠ b → (∃ (l : ℕ) (R : L.Relations l) (x : Fin l → M),
        Structure.RelMap R x ∧ a ∈ Set.range x ∧ b ∈ Set.range x) →
        ∃ (R : (vocab L).Relation) (x : Fin ((vocab L).arity R) → M),
          (structOf (L := L) M).relation R x ∧ ∃ i j, i ≠ j ∧ x i = a ∧ x j = b := by
      rintro a b hab ⟨l, R, x, hx, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
      refine ⟨((enum L) ⟨l, R⟩).succ, x ∘ Fin.cast (arity_succ_enum ⟨l, R⟩),
        (relation_succ_enum ⟨l, R⟩ x).2 hx, Fin.cast (arity_succ_enum ⟨l, R⟩).symm i,
        Fin.cast (arity_succ_enum ⟨l, R⟩).symm j, ?_, by simp, by simp⟩
      intro hij
      apply hab
      have := congrArg (Fin.cast (arity_succ_enum ⟨l, R⟩)) hij
      simp only [Fin.cast_cast, Fin.cast_eq_self] at this
      rw [this]
    rintro (h | h)
    · exact key a b hab h
    · obtain ⟨R, x, hx, i, j, hij, hi, hj⟩ := key b a (Ne.symm hab) h
      exact ⟨R, x, hx, j, i, Ne.symm hij, hj, hi⟩

theorem distanceAtMost_iff {M : Type z} [L.Structure M] :
    ∀ (r : ℕ) (a b : M), distanceAtMost (structOf (L := L) M) r a b ↔
      WithinDist (gaifmanGraph L (V := M)) r a b
  | 0, a, b => by
    rw [← DistanceFormulas.stepSeq_iff]
    constructor
    · rintro rfl
      exact ⟨fun _ => a, rfl, rfl, fun i => i.elim0⟩
    · rintro ⟨w, h0, hl, -⟩
      rw [← h0, ← hl]
      rfl
  | r + 1, a, b => by
    rw [← DistanceFormulas.stepSeq_iff, DistanceFormulas.stepSeq_succ]
    simp only [distanceAtMost, DistanceFormulas.stepSeq_iff, distanceAtMost_iff r, adjacent_iff]
    constructor
    · rintro (h | ⟨c, hc, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨c, Or.inr hc, h⟩
    · rintro ⟨c, rfl | hc, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, hc, h⟩

theorem inBallAround_iff {M : Type z} [L.Structure M] (r : ℕ) {k : ℕ} (anchors : Fin k → M)
    (x : M) : inBallAround (structOf (L := L) M) r anchors x ↔
      ∃ i, WithinDist (gaifmanGraph L (V := M)) r (anchors i) x := by
  unfold inBallAround
  simp only [distanceAtMost_iff]
  constructor
  · rintro (h | ⟨c, -⟩)
    · exact h
    · exact c.elim0
  · exact Or.inl

/-! ### From formulas of `L` to formulas of the vocabulary -/

section toLeaf

variable [L.IsRelational]

/-- A term of `L` over the free variables and the bound variables, as a
variable of the vocabulary. -/
def toLeafTerm {n m : ℕ} : L.Term (Fin n ⊕ Fin m) → Gaifman.FirstOrder.Term (vocab L) (n + m)
  | .var (.inl i) => .var (Fin.castAdd m i)
  | .var (.inr j) => .var (Fin.natAdd n j)
  | .func f _ => isEmptyElim f

/-- The translation of a formula of `L` with `n` free and `m` bound variables
into a formula of the vocabulary with `n + m` variables. -/
noncomputable def toLeaf {n : ℕ} : {m : ℕ} → L.BoundedFormula (Fin n) m →
    Gaifman.FirstOrder.Formula (vocab L) (n + m)
  | _, .falsum => .rel (0 : Fin (symbolCount L + 1)) fun i => Fin.elim0 i
  | _, .equal t₁ t₂ => .eq (toLeafTerm t₁) (toLeafTerm t₂)
  | _, .rel R ts => .rel ((enum L) ⟨_, R⟩).succ
      fun i => toLeafTerm (ts (Fin.cast (arity_succ_enum ⟨_, R⟩) i))
  | _, .imp φ ψ => .or (.not (toLeaf φ)) (toLeaf ψ)
  | m, .all φ => .not (.ex (.not (toLeaf (n := n) (m := m + 1) φ)))

theorem eval_toLeafTerm {M : Type z} [L.Structure M] {n m : ℕ} (t : L.Term (Fin n ⊕ Fin m))
    (v : Fin n → M) (xs : Fin m → M) :
    (toLeafTerm t).eval (structOf (L := L) M) (Fin.append v xs) = t.realize (Sum.elim v xs) := by
  match t with
  | .var (.inl i) => simp [toLeafTerm, Gaifman.FirstOrder.Term.eval]
  | .var (.inr j) => simp [toLeafTerm, Gaifman.FirstOrder.Term.eval]
  | .func f _ => exact isEmptyElim f

theorem sat_toLeaf {M : Type z} [L.Structure M] {n : ℕ} :
    ∀ {m : ℕ} (φ : L.BoundedFormula (Fin n) m) (v : Fin n → M) (xs : Fin m → M),
      Gaifman.FirstOrder.Formula.Sat (structOf (L := L) M) (toLeaf φ) (Fin.append v xs) ↔
        φ.Realize v xs
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal t₁ t₂, v, xs => by
    simp only [toLeaf, Gaifman.FirstOrder.Formula.Sat, eval_toLeafTerm, BoundedFormula.Realize]
  | _, .rel R ts, v, xs => by
    simp only [toLeaf, Gaifman.FirstOrder.Formula.Sat, eval_toLeafTerm, BoundedFormula.Realize]
    exact relation_succ_enum ⟨_, R⟩ fun p => (ts p).realize (Sum.elim v xs)
  | _, .imp φ ψ, v, xs => by
    simp only [toLeaf, Gaifman.FirstOrder.Formula.Sat, sat_toLeaf φ, sat_toLeaf ψ,
      BoundedFormula.realize_imp]
    tauto
  | _, .all φ, v, xs => by
    simp only [toLeaf, Gaifman.FirstOrder.Formula.Sat, BoundedFormula.realize_all, not_exists,
      not_not]
    refine forall_congr' fun x => ?_
    rw [← sat_toLeaf φ v (Fin.snoc xs x), Fin.append_snoc]

theorem quantifierRank_toLeaf {n : ℕ} : ∀ {m : ℕ} (φ : L.BoundedFormula (Fin n) m),
    (toLeaf φ).quantifierRank = quantifierRank φ
  | _, .falsum => rfl
  | _, .equal _ _ => rfl
  | _, .rel _ _ => rfl
  | _, .imp φ ψ => by
    simp only [toLeaf, Gaifman.FirstOrder.Formula.quantifierRank, quantifierRank,
      quantifierRank_toLeaf φ, quantifierRank_toLeaf ψ]
  | _, .all φ => by
    simp only [toLeaf, Gaifman.FirstOrder.Formula.quantifierRank, quantifierRank,
      quantifierRank_toLeaf φ]

end toLeaf

/-! ### From local formulas of the vocabulary to local formulas of `L` -/

section fromLeaf

/-- A term of a local formula as a variable of `L`. -/
def fromLeafTerm {k b : ℕ} : LocalTerm (vocab L) k b → L.Term (Fin k ⊕ Fin b)
  | .anchor i => .var (.inl i)
  | .bound j => .var (.inr j)
  | .const c => c.elim0

/-- The translation of a relation atom: the falsum symbol becomes falsum. -/
noncomputable def relBack {k b : ℕ} : (R : (vocab L).Relation) →
    (Fin ((vocab L).arity R) → L.Term (Fin k ⊕ Fin b)) → L.BoundedFormula (Fin k) b :=
  Fin.cases (motive := fun R => (Fin ((vocab L).arity R) → L.Term (Fin k ⊕ Fin b)) →
      L.BoundedFormula (Fin k) b)
    (fun _ => ⊥) fun i ts => .rel ((enum L).symm i).2 ts

/-- The translation of a local formula of radius `r`, where every
quantifier is guarded by `ballGuard`. -/
noncomputable def fromLeaf {k r : ℕ} : {b : ℕ} → LocalFormula (vocab L) k r b →
    L.BoundedFormula (Fin k) b
  | _, .rel R args => relBack R fun i => fromLeafTerm (args i)
  | _, .eq t₁ t₂ => .equal (fromLeafTerm t₁) (fromLeafTerm t₂)
  | _, .not φ => ∼(fromLeaf φ)
  | _, .or φ ψ => fromLeaf φ ⊔ fromLeaf ψ
  | b, .ex φ => ∃' (ballGuard L k r b ⊓ fromLeaf φ)

theorem isLocal_fromLeaf {k r : ℕ} : ∀ {b : ℕ} (φ : LocalFormula (vocab L) k r b),
    IsLocal r (fromLeaf φ)
  | _, .rel R args => by
    simp only [fromLeaf]
    induction R using Fin.cases with
    | zero => exact IsLocal.falsum
    | succ i => exact IsLocal.rel _ _
  | _, .eq _ _ => IsLocal.equal _ _
  | _, .not φ => IsLocal.imp (isLocal_fromLeaf φ) IsLocal.falsum
  | _, .or φ ψ => IsLocal.imp (IsLocal.imp (isLocal_fromLeaf φ) IsLocal.falsum) (isLocal_fromLeaf ψ)
  | _, .ex φ => IsLocal.ex (le_refl r) (isLocal_fromLeaf φ)

omit [Finite (Σ l, L.Relations l)] in
theorem isLocal_mono [Finite (Σ l, L.Relations l)] {r r' k : ℕ} (hr : r ≤ r') {n : ℕ}
    {φ : L.BoundedFormula (Fin k) n} (h : IsLocal r φ) : IsLocal r' φ := by
  induction h with
  | falsum => exact IsLocal.falsum
  | equal => exact IsLocal.equal _ _
  | rel => exact IsLocal.rel _ _
  | imp _ _ ih₁ ih₂ => exact IsLocal.imp ih₁ ih₂
  | all hs _ ih => exact IsLocal.all (hs.trans hr) ih
  | ex hs _ ih => exact IsLocal.ex (hs.trans hr) ih

theorem realize_fromLeafTerm {M : Type z} [L.Structure M] {k b : ℕ}
    (t : LocalTerm (vocab L) k b) (anchors : Fin k → M) (bound : Fin b → M) :
    (fromLeafTerm t).realize (Sum.elim anchors bound) = t.eval (structOf (L := L) M) anchors bound := by
  cases t with
  | anchor i => rfl
  | bound j => rfl
  | const c => exact c.elim0

theorem realize_fromLeaf {M : Type z} [L.Structure M] {k r : ℕ} (anchors : Fin k → M) :
    ∀ {b : ℕ} (φ : LocalFormula (vocab L) k r b) (bound : Fin b → M),
      (fromLeaf φ).Realize anchors bound ↔ φ.Sat (structOf (L := L) M) anchors bound
  | _, .rel R args, bound => by
    simp only [fromLeaf, LocalFormula.Sat]
    induction R using Fin.cases with
    | zero =>
      simp only [relBack, Fin.cases_zero, BoundedFormula.realize_bot, false_iff]
      exact fun h => h
    | succ i =>
      simp only [relBack, Fin.cases_succ]
      show Structure.RelMap _ (fun j => (fromLeafTerm (args j)).realize (Sum.elim anchors bound)) ↔ _
      simp only [realize_fromLeafTerm]
      rfl
  | _, .eq t₁ t₂, bound => by
    simp only [fromLeaf, LocalFormula.Sat, BoundedFormula.Realize, realize_fromLeafTerm]
  | _, .not φ, bound => by
    simp only [fromLeaf, LocalFormula.Sat, BoundedFormula.realize_not, realize_fromLeaf anchors φ]
  | _, .or φ ψ, bound => by
    simp only [fromLeaf, LocalFormula.Sat, BoundedFormula.realize_sup, realize_fromLeaf anchors φ,
      realize_fromLeaf anchors ψ]
  | b, .ex φ, bound => by
    simp only [fromLeaf, LocalFormula.Sat, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      DistanceFormulas.realize_ballGuard, Fin.snoc_last, realize_fromLeaf anchors φ,
      inBallAround_iff]

theorem qr_ballGuard {α : ℕ} (hα : ∀ l, α < l → IsEmpty (L.Relations l)) (k s n : ℕ) :
    quantifierRank (ballGuard L k s n) ≤ s + α := by
  unfold ballGuard
  refine DistanceFormulaRank.qr_iSup_le _ _ fun i => ?_
  rw [DistanceFormulaRank.qr_instantiate]
  have := DistanceFormulaRank.qr_distFormula α hα s
  omega

theorem qr_fromLeaf {α : ℕ} (hα : ∀ l, α < l → IsEmpty (L.Relations l)) {k r : ℕ} :
    ∀ {b : ℕ} (φ : LocalFormula (vocab L) k r b),
      quantifierRank (fromLeaf φ) ≤ Gaifman.Depth.depth φ + r + α
  | _, .rel R args => by
    simp only [fromLeaf]
    induction R using Fin.cases with
    | zero => exact Nat.zero_le _
    | succ i => exact Nat.zero_le _
  | _, .eq _ _ => Nat.zero_le _
  | _, .not φ => by
    simp only [fromLeaf, DistanceFormulaRank.qr_not, Gaifman.Depth.depth]
    exact qr_fromLeaf hα φ
  | _, .or φ ψ => by
    simp only [fromLeaf, DistanceFormulaRank.qr_sup, Gaifman.Depth.depth]
    have := qr_fromLeaf hα φ
    have := qr_fromLeaf hα ψ
    omega
  | b, .ex φ => by
    simp only [fromLeaf, DistanceFormulaRank.qr_ex, DistanceFormulaRank.qr_inf,
      Gaifman.Depth.depth]
    have := qr_fromLeaf hα φ
    have := qr_ballGuard hα k r b
    omega

end fromLeaf

/-! ### Basic local sentences and normal forms -/

section normalForms

/-- The translation of a basic local sentence. -/
noncomputable def toBasic {r : ℕ} (β : BasicLocalSentence (vocab L) r) : L.Sentence :=
  basicLocalSentence L r β.witnessCount (fromLeaf β.property)

theorem withinDist_symm {W : Type*} {G : SimpleGraph W} {d : ℕ} {a b : W}
    (h : WithinDist G d a b) : WithinDist G d b a := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by rw [SimpleGraph.Walk.length_reverse]; exact hp⟩

theorem realize_toBasic {M : Type z} [L.Structure M] {r : ℕ}
    (β : BasicLocalSentence (vocab L) r) (w : Empty → M) :
    Formula.Realize (toBasic β) w ↔ β.Sat (structOf (L := L) M) := by
  unfold toBasic basicLocalSentence BasicLocalSentence.Sat
  rw [BoundedFormula.realize_exs]
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_iInf, BoundedFormula.realize_not,
    DistanceFormulas.realize_instantiate]
  refine exists_congr fun xs => ?_
  have hpair : ∀ (i j : Fin β.witnessCount),
      (fun m => ((![Term.var (Sum.inr i), Term.var (Sum.inr j)] :
        Fin 2 → L.Term (Empty ⊕ Fin β.witnessCount)) m).realize (Sum.elim w xs)) = ![xs i, xs j] := by
    intro i j
    funext m
    fin_cases m <;> rfl
  have hone : ∀ i : Fin β.witnessCount,
      (fun m => ((![Term.var (Sum.inr i)] :
        Fin 1 → L.Term (Empty ⊕ Fin β.witnessCount)) m).realize (Sum.elim w xs)) = fun _ => xs i := by
    intro i
    funext m
    fin_cases m
    rfl
  simp only [hpair, hone, DistanceFormulas.realize_distFormula, distanceAtMost_iff]
  have hprop : ∀ i, Formula.Realize (fromLeaf β.property) (fun _ => xs i) ↔
      β.property.Sat (structOf (L := L) M) (fun _ => xs i) Fin.elim0 := by
    intro i
    unfold Formula.Realize
    rw [realize_fromLeaf]
    congr! 1
  simp only [hprop]
  rw [and_comm]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h i j hij hd
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h ⟨(i, j), hlt⟩ hd
    · exact h ⟨(j, i), hgt⟩ (withinDist_symm hd)
  · rintro h ⟨⟨i, j⟩, hij⟩
    exact h i j (ne_of_lt hij)

theorem qr_toBasic {α : ℕ} (hα : ∀ l, α < l → IsEmpty (L.Relations l)) {r : ℕ}
    (β : BasicLocalSentence (vocab L) r) :
    quantifierRank (toBasic β) ≤
      β.witnessCount + Gaifman.Depth.depth β.property + 2 * r + α := by
  unfold toBasic basicLocalSentence
  rw [DistanceFormulaRank.qr_exs, DistanceFormulaRank.qr_inf]
  have h1 : quantifierRank (BoundedFormula.iInf fun p : {p : Fin β.witnessCount ×
      Fin β.witnessCount // p.1 < p.2} =>
        ∼(instantiate (distFormula L (2 * r))
          ![Term.var (Sum.inr p.1.1), Term.var (Sum.inr p.1.2)] :
            L.BoundedFormula Empty β.witnessCount)) ≤ 2 * r + α := by
    refine DistanceFormulaRank.qr_iInf_le _ _ fun p => ?_
    rw [DistanceFormulaRank.qr_not, DistanceFormulaRank.qr_instantiate]
    have := DistanceFormulaRank.qr_distFormula α hα (2 * r)
    omega
  have h2 : quantifierRank (BoundedFormula.iInf fun i : Fin β.witnessCount =>
      (instantiate (fromLeaf β.property) ![Term.var (Sum.inr i)] :
        L.BoundedFormula Empty β.witnessCount)) ≤ Gaifman.Depth.depth β.property + r + α := by
    refine DistanceFormulaRank.qr_iInf_le _ _ fun i => ?_
    rw [DistanceFormulaRank.qr_instantiate]
    exact qr_fromLeaf hα β.property
  omega

/-- The formula of `L` for a Boolean combination of normal-form atoms. -/
noncomputable def nfFormula {n : ℕ} :
    Gaifman.GaifmanNormalForm.BooleanCombination (NormalAtom (vocab L) n) → L.Formula (Fin n)
  | .atom (.local _ φ) => fromLeaf φ
  | .atom (.basic _ β) => (toBasic β).relabel Empty.elim
  | .truth => ∼⊥
  | .not b => ∼(nfFormula b)
  | .and b c => nfFormula b ⊓ nfFormula c

theorem realize_nfFormula {M : Type z} [L.Structure M] {n : ℕ} (v : Fin n → M) :
    ∀ b : Gaifman.GaifmanNormalForm.BooleanCombination (NormalAtom (vocab L) n),
      (nfFormula b).Realize v ↔ b.eval (fun atom => match atom with
        | .local _ ψ => ψ.Sat (structOf (L := L) M) v Fin.elim0
        | .basic _ β => β.Sat (structOf (L := L) M))
  | .atom (.local _ φ) => by
    simp only [nfFormula, Gaifman.GaifmanNormalForm.BooleanCombination.eval]
    unfold Formula.Realize
    rw [realize_fromLeaf]
    congr! 1
  | .atom (.basic _ β) => by
    simp only [nfFormula, Gaifman.GaifmanNormalForm.BooleanCombination.eval,
      Formula.realize_relabel]
    exact realize_toBasic β _
  | .truth => by
    simp [nfFormula, Gaifman.GaifmanNormalForm.BooleanCombination.eval]
  | .not b => by
    simp only [nfFormula, Formula.realize_not, realize_nfFormula v b,
      Gaifman.GaifmanNormalForm.BooleanCombination.eval]
  | .and b c => by
    simp only [nfFormula, Formula.realize_inf, realize_nfFormula v b, realize_nfFormula v c,
      Gaifman.GaifmanNormalForm.BooleanCombination.eval]

theorem isBooleanCombination_nfFormula {n : ℕ}
    (P : L.Formula (Fin n) → Prop) :
    ∀ b : Gaifman.GaifmanNormalForm.BooleanCombination (NormalAtom (vocab L) n),
      (∀ atom ∈ b.atoms, P (nfFormula (.atom atom))) →
        Lax185574.GaifmanLocality.IsBooleanCombination P (nfFormula b)
  | .atom a, h => .atom (h a (by simp [Gaifman.GaifmanNormalForm.BooleanCombination.atoms]))
  | .truth, _ => .imp .falsum .falsum
  | .not b, h => .imp (isBooleanCombination_nfFormula P b h) .falsum
  | .and b c, h => by
    have hb := isBooleanCombination_nfFormula P b fun a ha => h a (by
      simp [Gaifman.GaifmanNormalForm.BooleanCombination.atoms, ha])
    have hc := isBooleanCombination_nfFormula P c fun a ha => h a (by
      simp [Gaifman.GaifmanNormalForm.BooleanCombination.atoms, ha])
    exact .imp (.imp hb (.imp hc .falsum)) .falsum

theorem realize_nfFormula_body {M : Type z} [L.Structure M] {n : ℕ} (v : Fin n → M)
    (nf : NormalForm (vocab L) n) :
    (nfFormula nf.body).Realize v ↔ nf.Sat (structOf (L := L) M) v := by
  rw [realize_nfFormula]
  unfold NormalForm.Sat
  apply Gaifman.BooleanCombination.eval_congr
  intro atom _
  cases atom <;> rfl

end normalForms

end Lax185574Proofs.GaifmanTranslation
