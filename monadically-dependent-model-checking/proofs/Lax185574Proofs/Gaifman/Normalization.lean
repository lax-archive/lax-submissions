import Lax185574Proofs.Gaifman.ExistentialNormalForm
import Mathlib.Tactic

/-!
The structural translation and the final proof of Gaifman's normal-form
theorem.  We maintain the slightly stronger intermediate radius
`7^q - 1`. This absorbs the one-edge gap needed when separating relational
tuples and yields the advertised `7^q` bound immediately.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/Normalization.lean`.
-/

namespace Lax185574Proofs.Gaifman.Normalization

noncomputable section

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.FirstOrder
open Lax185574Proofs.Gaifman.Locality Lax185574Proofs.Gaifman.GaifmanNormalForm
open Lax185574Proofs.Gaifman.NormalFormOps
open Lax185574Proofs.Gaifman.ExistentialNormalForm

/-- Common local radius maintained at quantifier rank `q`. -/
def rankRadius (q : ℕ) : ℕ := 7 ^ q - 1

/-- Separation/scatter radius used when eliminating the next quantifier. -/
def splitRadius (q : ℕ) : ℕ := 2 * rankRadius q + 1

theorem rankRadius_mono {p q : ℕ} (h : p ≤ q) :
    rankRadius p ≤ rankRadius q := by
  have hp : 7 ^ p ≤ 7 ^ q := pow_le_pow_right₀ (by omega) h
  simp only [rankRadius]
  omega

theorem rankRadius_le_pow (q : ℕ) : rankRadius q ≤ 7 ^ q := by
  simp [rankRadius]

/-- All numerical inequalities required by the local elimination module. -/
theorem stepBounds (q : ℕ) :
    let R := rankRadius q
    let T := splitRadius q
    let S := rankRadius (q + 1)
    T = 2 * R + 1 ∧ R ≤ S ∧ R ≤ T ∧ T ≤ S ∧
      T + R ≤ S ∧ 2 * T ≤ S ∧ 3 * T ≤ S ∧ 3 * T + R ≤ S := by
  have hx : 0 < 7 ^ q := pow_pos (by omega) q
  refine ⟨rfl, rankRadius_mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [rankRadius, splitRadius, pow_succ]
  all_goals omega

theorem radiiBounded_mono {σ : Vocabulary} {k r s : ℕ}
    {nf : NormalForm σ k} (h : nf.RadiiBounded r) (hrs : r ≤ s) :
    nf.RadiiBounded s := by
  intro atom ha
  rcases atom with ⟨radius, φ⟩ | ⟨radius, β⟩
  · exact le_trans (h _ ha) hrs
  · exact le_trans (h _ ha) hrs

theorem witnessesBounded_mono {σ : Vocabulary} {k r s : ℕ}
    {nf : NormalForm σ k} (h : nf.WitnessesBounded r) (hrs : r ≤ s) :
    nf.WitnessesBounded s := by
  intro radius basic ha
  exact le_trans (h radius basic ha) hrs

/-- The uniform structural translation. -/
def normalize {σ : Vocabulary} : {k : ℕ} → Formula σ k → NormalForm σ k
  | _, .rel R args => relationAtomNormalForm R args
  | _, .eq left right => equalityAtomNormalForm left right
  | _, .not φ => NormalForm.neg (normalize φ)
  | _, .or φ ψ => NormalForm.disj (normalize φ) (normalize ψ)
  | k, .ex φ =>
      let q := φ.quantifierRank
      eliminateNormalForm (rankRadius q) (splitRadius q)
        (rankRadius (q + 1)) (normalize φ)

/-- Strong induction invariant for `normalize`: all radii are at most
`7^q-1`, witnesses are bounded by `q+k`, and satisfaction is preserved. -/
theorem normalize_spec {σ : Vocabulary} {k : ℕ} (φ : Formula σ k) :
    (normalize φ).RadiiBounded (rankRadius φ.quantifierRank) ∧
    (normalize φ).WitnessesBounded (φ.quantifierRank + k) ∧
    ∀ {M : Type*} [Fintype M] (A : Structure σ M) (env : Fin k → M),
      φ.Sat A env ↔ (normalize φ).Sat A env := by
  induction φ with
  | rel R args =>
      refine ⟨?_, ?_, ?_⟩
      · change (relationAtomNormalForm R args).RadiiBounded 0
        exact NormalForm.radiiBounded_ofLocal _ (le_refl 0)
      · exact NormalForm.witnessesBounded_ofLocal _
      · intro M inst A env
        exact (sat_relationAtomNormalForm A env R args).symm
  | eq left right =>
      refine ⟨?_, ?_, ?_⟩
      · change (equalityAtomNormalForm left right).RadiiBounded 0
        exact NormalForm.radiiBounded_ofLocal _ (le_refl 0)
      · exact NormalForm.witnessesBounded_ofLocal _
      · intro M inst A env
        exact (sat_equalityAtomNormalForm A env left right).symm
  | not φ ih =>
      refine ⟨NormalForm.radiiBounded_neg ih.1,
        NormalForm.witnessesBounded_neg ih.2.1, ?_⟩
      intro M inst A env
      simp only [Formula.Sat, normalize, NormalForm.sat_neg]
      exact not_congr (ih.2.2 A env)
  | or φ ψ ihφ ihψ =>
      let qφ := φ.quantifierRank
      let qψ := ψ.quantifierRank
      let q := max qφ qψ
      have hφq : rankRadius qφ ≤ rankRadius q :=
        rankRadius_mono (Nat.le_max_left _ _)
      have hψq : rankRadius qψ ≤ rankRadius q :=
        rankRadius_mono (Nat.le_max_right _ _)
      refine ⟨?_, ?_, ?_⟩
      · exact NormalForm.radiiBounded_disj
          (radiiBounded_mono ihφ.1 hφq)
          (radiiBounded_mono ihψ.1 hψq)
      · apply NormalForm.witnessesBounded_disj
        · apply witnessesBounded_mono ihφ.2.1
          simpa [Formula.quantifierRank] using
            (Nat.le_max_left φ.quantifierRank ψ.quantifierRank)
        · apply witnessesBounded_mono ihψ.2.1
          simpa [Formula.quantifierRank] using
            (Nat.le_max_right φ.quantifierRank ψ.quantifierRank)
      · intro M inst A env
        simp only [Formula.Sat, normalize, NormalForm.sat_disj]
        exact or_congr (ihφ.2.2 A env) (ihψ.2.2 A env)
  | @ex k φ ih =>
      let q := φ.quantifierRank
      let R := rankRadius q
      let T := splitRadius q
      let S := rankRadius (q + 1)
      have hb := stepBounds q
      dsimp only at hb
      rcases hb with ⟨hT, hRS, hRT, hTS, hTRS, h2TS, h3TS, h3TRS⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [normalize, Formula.quantifierRank, q, R, T, S] using
          (radiiBounded_eliminateNormalForm
            (R := R) (T := T) (S := S) (normalize φ) ih.1 hRS hTS)
      · have hw := witnessesBounded_eliminateNormalForm
          (R := R) (T := T) (S := S)
          (normalize φ) ih.2.1 (by omega : k + 1 ≤ q + (k + 1))
        simpa [normalize, Formula.quantifierRank, q, R, T, S,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw
      · intro M inst A env
        simp only [Formula.Sat, normalize]
        rw [sat_eliminateNormalForm A env (normalize φ) ih.1 hT hRS hRT
          hTS hTRS h2TS h3TS h3TRS]
        apply exists_congr
        intro y
        exact ih.2.2 A (Fin.snoc env y)

end

end Lax185574Proofs.Gaifman.Normalization
