import Lax185574.FirstOrderTypes
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Set.Card

/-!
Finite back-and-forth codes for tuples in structures over a relational
language with finitely many relation symbols. The code of rank `0` records
the atomic formulas that hold of the tuple. The code of rank `q + 1`
records the code of rank `q` and the set of codes of rank `q` of all
one-point extensions. Tuples with equal codes of rank `q` have equal types
of quantifier rank `q`, and there are finitely many codes. So the number of
types of quantifier rank `q` of `k`-tuples is bounded independently of the
structure.

Adapted from an earlier formalization that treats colored graphs, see
PROVENANCE.md.
-/

namespace Lax185574Proofs.TypeCodes

open FirstOrder FirstOrder.Language Lax185574.FirstOrderTypes

universe u v w w'

/-- If `f` factors through `h` on `S`, then `f` takes at most as many values
on `S` as `h`, provided `S` is finite. -/
theorem ncard_image_le_of_factor {α β γ : Type*} {S : Set α} (hS : S.Finite)
    (f : α → β) (h : α → γ) (hfac : ∀ a ∈ S, ∀ b ∈ S, h a = h b → f a = f b) :
    (f '' S).ncard ≤ (h '' S).ncard := by
  classical
  rcases S.eq_empty_or_nonempty with hempty | ⟨a₀, -⟩
  · simp [hempty]
  let g : γ → β := fun t => if ht : ∃ a ∈ S, h a = t then f ht.choose else f a₀
  have hfg : f '' S = g '' (h '' S) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨h a, ⟨a, ha, rfl⟩, ?_⟩
      have hex : ∃ b ∈ S, h b = h a := ⟨a, ha, rfl⟩
      simp only [g, dif_pos hex]
      exact hfac _ hex.choose_spec.1 _ ha hex.choose_spec.2
    · rintro ⟨t, ⟨a, ha, rfl⟩, rfl⟩
      have hex : ∃ b ∈ S, h b = h a := ⟨a, ha, rfl⟩
      refine ⟨a, ha, ?_⟩
      simp only [g, dif_pos hex]
      exact hfac _ ha _ hex.choose_spec.1 hex.choose_spec.2.symm
  rw [hfg]
  exact Set.ncard_image_le (hS.image h)

variable (L : Language.{u, v})

/-- The atomic code of a `k`-tuple: which entries are equal, and which
relation atoms hold of which choices of entries. -/
abbrev AtomCode (k : ℕ) : Type v :=
  (Fin k → Fin k → Bool) × ((R : Σ l, L.Relations l) → (Fin R.1 → Fin k) → Bool)

/-- The codes of rank `q` of `k`-tuples. -/
def Code : ℕ → ℕ → Type v
  | 0, k => AtomCode L k
  | q + 1, k => Code q k × Set (Code q (k + 1))

theorem code_finite [Finite (Σ l, L.Relations l)] : ∀ q k, Finite (Code L q k)
  | 0, k => inferInstanceAs (Finite (AtomCode L k))
  | q + 1, k => by
    have := code_finite q k
    have := code_finite q (k + 1)
    exact inferInstanceAs (Finite (Code L q k × Set (Code L q (k + 1))))

instance [Finite (Σ l, L.Relations l)] (q k : ℕ) : Finite (Code L q k) := code_finite L q k

variable {L}

/-- The truth value of a proposition as a Boolean. -/
noncomputable def truth (p : Prop) : Bool := @decide p (Classical.propDecidable p)

theorem truth_eq_iff {p r : Prop} : truth p = truth r ↔ (p ↔ r) := decide_eq_decide

variable {M : Type w} [L.Structure M]

variable (L) in
/-- The code of rank `q` of the tuple `a`. -/
noncomputable def code : (q : ℕ) → {k : ℕ} → (Fin k → M) → Code L q k
  | 0, _, a =>
    ((fun i j => truth (a i = a j)), fun R t => truth (Structure.RelMap R.2 (a ∘ t)))
  | q + 1, _, a => (code q a, Set.range fun x => code q (Fin.snoc a x))

variable {N : Type w'} [L.Structure N]

theorem code_mono {k : ℕ} {a : Fin k → M} {b : Fin k → N} :
    ∀ {q r : ℕ}, r ≤ q → code L q a = code L q b → code L r a = code L r b
  | 0, r, hr, h => by
    obtain rfl : r = 0 := by omega
    exact h
  | q + 1, r, hr, h => by
    rcases Nat.eq_or_lt_of_le hr with rfl | hlt
    · exact h
    · have h' := congrArg Prod.fst h
      simp only [code] at h'
      exact code_mono (q := q) (by omega) h'

theorem code_forth {k q : ℕ} {a : Fin k → M} {b : Fin k → N}
    (h : code L (q + 1) a = code L (q + 1) b) (x : M) :
    ∃ y, code L q (Fin.snoc a x) = code L q (Fin.snoc b y) := by
  have hext := congrArg Prod.snd h
  simp only [code] at hext
  have hx : code L q (Fin.snoc a x) ∈ Set.range (fun y => code L q (Fin.snoc b y)) := by
    rw [← hext]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy.symm⟩

variable [L.IsRelational]

/-- The position, in the combined tuple `ā x̄`, of a variable term. -/
def termIndex {k n : ℕ} : L.Term (Fin k ⊕ Fin n) → Fin (k + n)
  | .var s => finSumFinEquiv s
  | .func f _ => isEmptyElim f

theorem realize_term {k n : ℕ} (t : L.Term (Fin k ⊕ Fin n)) (v : Fin k → M)
    (xs : Fin n → M) : t.realize (Sum.elim v xs) = Fin.append v xs (termIndex t) := by
  cases t with
  | var s =>
    rcases s with i | i
    · simp [termIndex]
    · simp [termIndex]
  | func f _ => exact isEmptyElim f

/-- Tuples with equal codes of rank `q` satisfy the same formulas of
quantifier rank at most `q`. -/
theorem realize_iff_of_code_eq {k : ℕ} :
    ∀ {n : ℕ} (φ : L.BoundedFormula (Fin k) n) (q : ℕ), quantifierRank φ ≤ q →
      ∀ (v : Fin k → M) (xs : Fin n → M) (w : Fin k → N) (ys : Fin n → N),
        code L q (Fin.append v xs) = code L q (Fin.append w ys) →
          (φ.Realize v xs ↔ φ.Realize w ys)
  | _, .falsum, _, _, _, _, _, _, _ => Iff.rfl
  | _, .equal t₁ t₂, q, _, v, xs, w, ys, h => by
    have h0 := code_mono (Nat.zero_le q) h
    have := congrArg (fun c : Code L 0 _ => c.1 (termIndex t₁) (termIndex t₂)) h0
    simp only [code] at this
    simp only [BoundedFormula.Realize, realize_term]
    exact truth_eq_iff.mp this
  | _, .rel R ts, q, _, v, xs, w, ys, h => by
    have h0 := code_mono (Nat.zero_le q) h
    have := congrArg (fun c : Code L 0 _ => c.2 ⟨_, R⟩ (fun p => termIndex (ts p))) h0
    simp only [code] at this
    simp only [BoundedFormula.Realize, realize_term]
    exact truth_eq_iff.mp this
  | _, .imp φ ψ, q, hq, v, xs, w, ys, h => by
    simp only [quantifierRank] at hq
    simp only [BoundedFormula.realize_imp]
    rw [realize_iff_of_code_eq φ q (le_of_max_le_left hq) v xs w ys h,
      realize_iff_of_code_eq ψ q (le_of_max_le_right hq) v xs w ys h]
  | _, .all φ, q, hq, v, xs, w, ys, h => by
    simp only [quantifierRank] at hq
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [BoundedFormula.realize_all]
    constructor
    · intro hall y
      obtain ⟨x, hx⟩ := code_forth h.symm y
      rw [← Fin.append_snoc, ← Fin.append_snoc] at hx
      exact (realize_iff_of_code_eq φ q' (by omega) _ _ _ _ hx.symm).mp (hall x)
    · intro hall x
      obtain ⟨y, hy⟩ := code_forth h x
      rw [← Fin.append_snoc, ← Fin.append_snoc] at hy
      exact (realize_iff_of_code_eq φ q' (by omega) _ _ _ _ hy).mpr (hall y)

/-- Tuples with equal codes of rank `q` have equal types of quantifier
rank `q`. -/
theorem rankType_eq_of_code_eq {k q : ℕ} (a : Fin k → M) (b : Fin k → N)
    (h : code L q a = code L q b) : rankType (L := L) q a = rankType (L := L) q b := by
  ext φ
  simp only [rankType, Set.mem_ofPred_eq]
  refine and_congr_right fun hq => ?_
  have ha : Fin.append a (default : Fin 0 → M) = a := funext fun i => Fin.append_left a _ i
  have hb : Fin.append b (default : Fin 0 → N) = b := funext fun i => Fin.append_left b _ i
  refine realize_iff_of_code_eq φ q hq a default b default ?_
  rw [ha, hb]
  exact h

end Lax185574Proofs.TypeCodes
