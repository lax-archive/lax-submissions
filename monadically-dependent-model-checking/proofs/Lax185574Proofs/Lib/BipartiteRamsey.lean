import Lax185574Proofs.Lib.BipartiteRamseyDefs
import Lax185574Proofs.Lib.HomogeneousMatrix

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


/-!
Proof of Theorem 11.11. Repeatedly split a family of distinct rows, keeping
a larger side and one discarded row. This produces a staircase whose
diagonal opposes every entry below it. A pigeonhole argument fixes the
diagonal, and ordinary finite Ramsey fixes the entries above it.

The remaining four Boolean matrices are a matching, co-matching, weak
half-graph, and strict reverse half-graph. Deleting one row and one column
and reversing the order changes the last pattern into the required weak
half-graph. All bounds are explicit; optimization is immaterial here.
-/

namespace Lax185574Proofs.Lib.BipartiteRamsey

open Lax185574Proofs.Lib.BipartiteRamsey

universe u v

theorem classify_matrix {L : Type u} {R : Type v} {ℓ : ℕ}
    (E : L → R → Prop) (a : Fin (ℓ + 1) → L) (b : Fin (ℓ + 1) → R)
    (t d : Bool) (ha : Function.Injective a) (hb : Function.Injective b)
    (hdiag : ∀ i, E (a i) (b i) ↔ t = false)
    (hlower : ∀ i j, j < i → (E (a i) (b j) ↔ t = true))
    (hupper : ∀ i j, i < j → (E (a i) (b j) ↔ d = true)) :
    ∃ (a' : Fin ℓ → L) (b' : Fin ℓ → R),
      Function.Injective a' ∧ Function.Injective b' ∧ AtomicallyMatched E a' b' := by
  have hmatrix (i j : Fin (ℓ + 1)) :
      E (a i) (b j) ↔ (if i < j then d = true else if i = j then t = false else t = true) := by
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte]
      exact hupper i j hij
    · by_cases heq : i = j
      · subst j
        simpa using hdiag i
      · simp only [hij, heq, ↓reduceIte]
        exact hlower i j (lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm heq))
  cases t <;> cases d
  · refine ⟨a ∘ Fin.castSucc, b ∘ Fin.castSucc,
      ha.comp (Fin.castSucc_injective ℓ), hb.comp (Fin.castSucc_injective ℓ), Or.inl ?_⟩
    intro i j
    have h := hmatrix i.castSucc j.castSucc
    dsimp only [Function.comp_apply]
    rcases lt_trichotomy i j with hij | hij | hij
    · simpa [hij, hij.ne, Fin.castSucc_lt_castSucc_iff] using h
    · subst j
      simpa using h
    · simpa [not_lt.mpr hij.le, hij.ne.symm, Fin.castSucc_lt_castSucc_iff] using h
  · refine ⟨a ∘ Fin.castSucc, b ∘ Fin.castSucc,
      ha.comp (Fin.castSucc_injective ℓ), hb.comp (Fin.castSucc_injective ℓ), Or.inr (Or.inr ?_)⟩
    intro i j
    have h := hmatrix i.castSucc j.castSucc
    dsimp only [Function.comp_apply]
    rcases lt_trichotomy i j with hij | hij | hij
    · simpa [hij, hij.ne, hij.le, Fin.castSucc_lt_castSucc_iff] using h
    · subst j
      simpa using h
    · simpa [not_lt.mpr hij.le, hij.ne.symm, not_le.mpr hij,
        Fin.castSucc_lt_castSucc_iff] using h
  · let f : Fin ℓ → Fin (ℓ + 1) := fun i => (Fin.rev i).succ
    let g : Fin ℓ → Fin (ℓ + 1) := fun i => (Fin.rev i).castSucc
    have hf : Function.Injective f := (Fin.succ_injective ℓ).comp Fin.rev_injective
    have hg : Function.Injective g := (Fin.castSucc_injective ℓ).comp Fin.rev_injective
    refine ⟨a ∘ f, b ∘ g, ha.comp hf, hb.comp hg, Or.inr (Or.inr ?_)⟩
    intro i j
    have h := hmatrix (f i) (g j)
    dsimp only [Function.comp_apply]
    have hord : g j < f i ↔ i ≤ j := by
      simp only [f, g, Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.rev]
      omega
    rcases lt_trichotomy (f i) (g j) with hij | hij | hij
    · have hn : ¬ i ≤ j := by rw [← hord]; exact not_lt_of_ge hij.le
      simpa [hij, hn] using h
    · have hn : ¬ i ≤ j := by rw [← hord, hij]; exact lt_irrefl _
      simpa [hij, hn] using h
    · have hy : i ≤ j := hord.mp hij
      simpa [not_lt.mpr hij.le, hij.ne.symm, hy] using h
  · refine ⟨a ∘ Fin.castSucc, b ∘ Fin.castSucc,
      ha.comp (Fin.castSucc_injective ℓ), hb.comp (Fin.castSucc_injective ℓ), Or.inr (Or.inl ?_)⟩
    intro i j
    have h := hmatrix i.castSucc j.castSucc
    dsimp only [Function.comp_apply]
    rcases lt_trichotomy i j with hij | hij | hij
    · simpa [hij, hij.ne, Fin.castSucc_lt_castSucc_iff] using h
    · subst j
      simpa using h
    · simpa [not_lt.mpr hij.le, hij.ne.symm, Fin.castSucc_lt_castSucc_iff] using h

def patternBound (ℓ : ℕ) : ℕ := 2 ^ (2 * 3 ^ ((ℓ + 1) + (ℓ + 1)))

theorem patternBound_computable : Computable patternBound := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact (hpow.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (Primrec.const 2)
      (hpow.comp (Primrec.const 3)
        (Primrec.nat_add.comp Primrec.succ Primrec.succ)))).to_comp

/--
A computable threshold for matching, co-matching, or half-graph extraction
from distinct neighborhoods. No Lax assumptions are needed.
-/
theorem exists_computable_pattern_bound :
    ∃ Q : ℕ → ℕ, Computable Q ∧ ∀ ℓ : ℕ,
      ∀ (L : Type u) (R : Type v) [Fintype L] [Fintype R] [DecidableEq R]
        (E : L → R → Prop) [DecidableRel E],
        Q ℓ ≤ (neighborhoodFamily E).card →
        ∃ (a : Fin ℓ → L) (b : Fin ℓ → R),
          Function.Injective a ∧ Function.Injective b ∧ AtomicallyMatched E a b := by
  classical
  refine ⟨patternBound, patternBound_computable, ?_⟩
  intro ℓ L R _ _ _ E _ h
  obtain ⟨A, b, t, d, hA, hb, hmem, hdiag, hlower, hupper⟩ :=
    HomogeneousMatrix.extract_matrix (ℓ + 1) (neighborhoodFamily E) h
  have hrep (i : Fin (ℓ + 1)) : ∃ x : L, Finset.univ.filter (E x) = A i := by
    simpa [neighborhoodFamily] using hmem i
  choose a ha using hrep
  have hainj : Function.Injective a := by
    intro i j hij
    apply hA
    rw [← ha i, ← ha j, hij]
  have hrel (i j : Fin (ℓ + 1)) : E (a i) (b j) ↔ b j ∈ A i := by
    rw [← ha i]
    simp
  exact classify_matrix E a b t d hainj hb
    (fun i => (hrel i i).trans (hdiag i))
    (fun i j hij => (hrel i j).trans (hlower i j hij))
    (fun i j hij => (hrel i j).trans (hupper i j hij))

end Lax185574Proofs.Lib.BipartiteRamsey
