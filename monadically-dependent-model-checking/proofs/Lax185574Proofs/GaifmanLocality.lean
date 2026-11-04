import Lax185574.GaifmanLocality
import Lax185574Proofs.Gaifman.Translation

/-!
Proof of Gaifman's locality theorem with a rank bound that does not depend
on the signature, from the Gaifman normal form adapted from lax-512892.
-/

namespace Lax185574Proofs.GaifmanLocality

open FirstOrder FirstOrder.Language
open Lax185574.FirstOrderTypes Lax185574.LocalFormulas Lax185574.GaifmanLocality
open Lax185574Proofs.GaifmanTranslation

universe u v z

theorem depthBound_mono_k (A q : ℕ) {k k' : ℕ} (h : k ≤ k') :
    Gaifman.Depth.depthBound A q k ≤ Gaifman.Depth.depthBound A q k' :=
  Nat.mul_le_mul_left _ (by omega)

/--
---
conclusion: Lax185574.GaifmanLocality.exists_local_equivalent
---
The formula is translated into the syntax of the normal form of lax-512892,
over a vocabulary with one symbol for each relation symbol and a nullary
symbol for falsum. Its normal form has radii at most `7^q − 1` and at most
`q + k` witnesses in each basic local sentence. Every local formula in it
has quantifier depth at most `q · (k + q + 2 + 6 · 7^q + 4α)`, a bound that
depends on the arity `α` of the vocabulary but not on its symbols. Back in
mathlib's syntax, each ball-restricted quantifier gets a dist-formula guard
of quantifier rank at most `7^q + α`, which gives the rank bound
`p = q · (k + q + 2 + 6 · 7^q + 4α) + q + k + 2 · 7^q + 2α`.
-/
theorem exists_local_equivalent (α q k : ℕ) :
    ∃ p : ℕ, ∀ (L : Language.{u, v}) [L.IsRelational] [Finite (Σ l, L.Relations l)],
      (∀ l, α < l → IsEmpty (L.Relations l)) →
      ∀ (n : ℕ), n ≤ k → ∀ φ : L.Formula (Fin n), quantifierRank φ ≤ q →
        ∃ ψ : L.Formula (Fin n), FinitelyEquivalent.{u, v, z, 0} φ ψ ∧
          IsBooleanCombination (IsLocalConstituent (7 ^ q) p) ψ := by
  refine ⟨Gaifman.Depth.depthBound α q k + (q + k) + 2 * 7 ^ q + 2 * α,
    fun L _ _ hα n hn φ hq => ?_⟩
  let φ' : Gaifman.FirstOrder.Formula (vocab L) n := toLeaf φ
  have hqr : φ'.quantifierRank = quantifierRank φ := quantifierRank_toLeaf φ
  obtain ⟨hradii, hwit, hsat⟩ := Gaifman.Normalization.normalize_spec.{z} φ'
  have hdepth := Gaifman.Depth.depthBounded_normalize (vocab_arityLE hα) φ'
  have hD : Gaifman.Depth.depthBound α φ'.quantifierRank n ≤ Gaifman.Depth.depthBound α q k :=
    (Gaifman.Depth.depthBound_mono α n (by omega)).trans (depthBound_mono_k α q hn)
  have hpow : 7 ^ φ'.quantifierRank ≤ 7 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
  have hR : Gaifman.Normalization.rankRadius φ'.quantifierRank ≤ 7 ^ q :=
    (Gaifman.Normalization.rankRadius_le_pow _).trans hpow
  refine ⟨nfFormula (Gaifman.Normalization.normalize φ').body, ?_, ?_⟩
  · intro M _ _ x
    let _ : Fintype M := Fintype.ofFinite M
    have h1 := sat_toLeaf (M := M) φ x default
    have hx : Fin.append x (default : Fin 0 → M) = x := funext fun i => Fin.append_left x _ i
    rw [hx] at h1
    unfold Formula.Realize
    rw [← h1]
    change Gaifman.FirstOrder.Formula.Sat (structOf (L := L) M) φ' x ↔ _
    rw [hsat (structOf (L := L) M) x]
    exact (realize_nfFormula_body (L := L) x (Gaifman.Normalization.normalize φ')).symm
  · apply isBooleanCombination_nfFormula
    intro atom hatom
    have hr := hradii atom hatom
    have hd := hdepth atom hatom
    rcases atom with ⟨r, ψ⟩ | ⟨r, β⟩
    · simp only at hr
      simp only [Gaifman.Depth.atomDepth] at hd
      refine Or.inl ⟨isLocal_mono (hr.trans hR) (isLocal_fromLeaf ψ), ?_⟩
      have := qr_fromLeaf hα ψ
      simp only [nfFormula]
      have := hr.trans hR
      omega
    · simp only at hr
      simp only [Gaifman.Depth.atomDepth] at hd
      have hw := hwit r β hatom
      refine Or.inr ⟨toBasic β, ⟨r, hr.trans hR, β.witnessCount, fromLeaf β.property,
        isLocal_fromLeaf _, rfl⟩, ?_, rfl⟩
      have := qr_toBasic hα β
      have := hr.trans hR
      omega

end Lax185574Proofs.GaifmanLocality
