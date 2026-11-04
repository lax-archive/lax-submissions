import Lax185574.ChainConstructionSequences
import Lax185574.MergeToConstruction
import Lax185574.BetterMergeSequences
import Lax185574Proofs.Legacy
import Lax185574Proofs.Interface.Shim.BetterMergeSequences
import Lax185574Proofs.Interface.Shim.MergeToConstruction

/-!
The mathematical half of lem:better-definable-mw-from-sets
(`ChainConstructionSequences`). Its proof composes lem:better-mw
(`BetterMergeSequences`) with cl:from-merge-to-construction
(`MergeToConstruction`). The functions of the two lemmas compose to a
function with all properties that `ChainConstructionSequences` asks of
its output. What remains for its proof is a program that runs the two
programs one after the other.

The only point beyond the paper is the bound max(1, w_r) of
`MergeToConstruction`: it is at most w_r = k_r · π_G(k_r) on graphs with
at least one vertex, and on the empty graph both widths vanish and the
definability condition is empty.
-/

namespace Lax185574Proofs.Conversions.ChainComposition

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.Partitions Lax185574.Flips Lax185574.MergeSequences
open Lax185574.BetterMergeSequences Lax185574.Chains Lax185574.VCDimension
open Lax185574.ConstructionSequences Lax185574.ConstructionWidth
open Lax185574.SequenceEncoding Lax185574.LocalDefinability Lax185574.FirstOrderTypes
open Lax185574.ChainConstructionSequences

/-- A chain on at least one vertex has radius-`r` width at least one. -/
theorem one_le_chainWidth {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (S : List (Finset (Fin n))) (hS : IsChain S) (r : ℕ) : 1 ≤ chainWidth G r S := by
  obtain ⟨hne, hhead, hlast, -⟩ := hS
  have hlen : 1 < S.length := by
    rcases S with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exact absurd rfl hne
    · simp only [List.head_cons] at hhead
      simp only [List.getLast_singleton] at hlast
      rw [hhead] at hlast
      have : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
      rw [← hlast] at this
      simp at this
    · simp
  let v : Fin n := ⟨0, hn⟩
  have hmem : partCount (atomicTypes G (S[0 + 1] : Set (Fin n)))
      (flipBall G (atomicTypes G (S[0] : Set (Fin n))) r v) ∈
      {K | ∃ (t : ℕ) (ht : t + 1 < S.length) (v : Fin n),
        K = partCount (atomicTypes G (S[t + 1] : Set (Fin n)))
          (flipBall G (atomicTypes G (S[t] : Set (Fin n))) r v)} := ⟨0, hlen, v, rfl⟩
  have hbdd : BddAbove {K | ∃ (t : ℕ) (ht : t + 1 < S.length) (v : Fin n),
      K = partCount (atomicTypes G (S[t + 1] : Set (Fin n)))
        (flipBall G (atomicTypes G (S[t] : Set (Fin n))) r v)} := by
    refine ⟨n, ?_⟩
    rintro K ⟨t, ht, w, rfl⟩
    unfold partCount
    exact (Set.ncard_image_le (Set.toFinite _)).trans
      ((Set.ncard_le_card _).trans (by simp))
  refine le_trans ?_ (le_csSup hbdd hmem)
  unfold partCount
  rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (Set.toFinite _)]
  refine Set.Nonempty.ne_empty ⟨Quotient.mk _ v, v, ?_, rfl⟩
  intro H _
  exact ⟨SimpleGraph.Walk.nil, by simp⟩

/-- On a nonempty vertex type, the neighborhood complexity is at least
one. -/
theorem one_le_neighborhoodComplexity {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (k : ℕ) : 1 ≤ neighborhoodComplexity G k := by
  have hbdd : BddAbove {m | ∃ S : Finset (Fin n), S.card ≤ k ∧
      m = Lax199508.NeighborhoodComplexity.traceCount G (S : Set (Fin n))} := by
    refine ⟨Nat.card (Set (Fin n)), ?_⟩
    rintro m ⟨S, -, rfl⟩
    exact Set.ncard_le_card _
  refine le_trans ?_ (le_csSup hbdd ⟨∅, by simp, rfl⟩)
  unfold Lax199508.NeighborhoodComplexity.traceCount
  rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (Set.toFinite _)]
  exact Set.Nonempty.ne_empty ⟨∅, ⟨0, hn⟩, by simp⟩

/-- On a nonempty vertex type, `w_r ≥ 1`. -/
theorem one_le_chainBound {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (S : List (Finset (Fin n))) (hS : IsChain S) (r : ℕ) : 1 ≤ chainBound G S r :=
  Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero
    (Nat.one_le_iff_ne_zero.1 (one_le_chainWidth hn G S hS _))
    (Nat.one_le_iff_ne_zero.1 (one_le_neighborhoodComplexity hn G _)))

/-- Every sequence of partial graphs on the empty vertex type has width
zero. -/
theorem constructionWidth_fin_zero (r : ℕ) (s : List (Lax185574.PartialGraphs.PartialGraph (Fin 0))) :
    constructionWidth r s = 0 := by
  unfold constructionWidth
  have : {K | ∃ (t : ℕ) (ht : t < s.length) (v : Fin 0),
      K = ((s[t]).color '' (s[t]).ball r v).ncard} = ∅ := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨t, ht, v, -⟩
    exact v.elim0
  rw [this, csSup_empty]; rfl

/-- **Composition.** The output of `MergeToConstruction` on the output of
`BetterMergeSequences` has the properties that
`ChainConstructionSequences` asks for, with the same constant `A`. -/
theorem properties_of_composition {n : ℕ} (G : SimpleGraph (Fin n))
    (S : List (Finset (Fin n))) (hS : IsChain S)
    (φeq φR : (withColors Language.graph 2).Formula (Fin 2))
    (hφeq : quantifierRank φeq ≤ 5) (hφR : quantifierRank φR ≤ 5)
    (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))) (σ : Script n) (A : ℕ)
    (hms : IsMergeSequence G ms ∧ ms.length = S.length ∧ StagesDefinable G ms φeq φR ∧
      ∀ r : ℕ, 1 ≤ r →
        mergeWidth r ms ≤ chainWidth G (5 * r + 1) S *
          neighborhoodComplexity G (chainWidth G (5 * r + 1) S))
    (hσ : IsConstructionSequence G σ.run ∧
      (∀ v ∈ toWord σ, v ≤ wordLength σ + n) ∧
      σ.run.length ≤ A * (n + 1) * (mergeWidth 1 ms + 1) ∧
      ∀ r : ℕ, 1 ≤ r →
        constructionWidth r σ.run ≤ max 1 (mergeWidth r ms) ∧
        ((∃ φeq φR : (withColors Language.graph 2).Formula (Fin 2),
            quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
              StagesDefinable G ms φeq φR) →
          IsRadiusDefinable G σ.run r (2 * ms.length + 1) (max 1 (mergeWidth r ms)) 7)) :
    IsConstructionSequence G σ.run ∧
      (∀ v ∈ toWord σ, v ≤ wordLength σ + n) ∧
      σ.run.length ≤ A * (n + 1) * (chainBound G S 1 + 1) ∧
      ∀ r : ℕ, 1 ≤ r →
        constructionWidth r σ.run ≤ chainBound G S r ∧
          IsRadiusDefinable G σ.run r (2 * S.length + 1) (chainBound G S r) 7 := by
  obtain ⟨-, hlen, hdef, hw⟩ := hms
  obtain ⟨hcs, hword, hlength, hσw⟩ := hσ
  refine ⟨hcs, hword, hlength.trans ?_, fun r hr => ?_⟩
  · have := hw 1 le_rfl
    unfold chainBound
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right this 1)
  obtain ⟨hcw, hrd⟩ := hσw r hr
  have hrd := hrd ⟨φeq, φR, hφeq, hφR, hdef⟩
  rw [hlen] at hrd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨by rw [constructionWidth_fin_zero]; exact Nat.zero_le _, ?_⟩
    intro t ht v
    exact v.elim0
  · have hmax : max 1 (mergeWidth r ms) ≤ chainBound G S r :=
      max_le (one_le_chainBound hn G S hS r) (hw r hr)
    refine ⟨hcw.trans hmax, fun t ht v => ?_⟩
    obtain ⟨colors, T, hT, hD⟩ := hrd t ht v
    exact ⟨colors, T, hT.trans hmax, hD⟩

/-- The functions and programs of `BetterMergeSequences` and
`MergeToConstruction`, composed. The composed function has all
properties of `ChainConstructionSequences`, the first program runs in
time `c₁ · (m+1) · (n+1)³` on the chain, and the second in time
`c₂ · (m+1) · (n+1)²` on the merge sequence, which has length `m`. -/
theorem exists_composition :
    ∃ (p₁ : Program) (e₁ : ℕ)
      (M₁ : ∀ n : ℕ, SimpleGraph (Fin n) → List (Finset (Fin n)) →
        List (Setoid (Fin n) × SimpleGraph (Fin n)))
      (p₂ : Program) (e₂ A : ℕ)
      (M₂ : ∀ n : ℕ, SimpleGraph (Fin n) → List (Setoid (Fin n) × SimpleGraph (Fin n)) →
        Script n),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        IsMergeSequence G (M₁ n G S) ∧ (M₁ n G S).length = S.length ∧
        IsConstructionSequence G (M₂ n G (M₁ n G S)).run ∧
        (∀ v ∈ toWord (M₂ n G (M₁ n G S)), v ≤ wordLength (M₂ n G (M₁ n G S)) + n) ∧
        (M₂ n G (M₁ n G S)).run.length ≤ A * (n + 1) * (chainBound G S 1 + 1) ∧
        ∀ r : ℕ, 1 ≤ r →
          constructionWidth r (M₂ n G (M₁ n G S)).run ≤ chainBound G S r ∧
            IsRadiusDefinable G (M₂ n G (M₁ n G S)).run r (2 * S.length + 1)
              (chainBound G S r) 7) ∧
      (∃ c₁ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        Computes p₁ e₁ c₁ (G, S) (M₁ n G S) (fun _ => c₁ * (S.length + 1) * (n + 1) ^ 3)) ∧
      (∃ c₂ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n))
        (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))), IsMergeSequence G ms →
          Computes p₂ e₂ c₂ (G, ms) (M₂ n G ms) (fun _ => c₂ * (ms.length + 1) * (n + 1) ^ 2)) := by
  obtain ⟨φeq, φR, hφeq, hφR, p₁, e₁, M₁, h₁, hc₁⟩ :=
    Lax185574Proofs.Shim.BetterMergeSequences.exists_mergeSequence_of_chain
  obtain ⟨p₂, e₂, A, M₂, h₂, hc₂⟩ :=
    Lax185574Proofs.Shim.MergeToConstruction.exists_constructionSequence_of_mergeSequence
  refine ⟨p₁, e₁, M₁, p₂, e₂, A, M₂, fun n G S hS => ?_, hc₁, hc₂⟩
  have hm := h₁ n G S hS
  have hc := h₂ n G (M₁ n G S) hm.1
  exact ⟨hm.1, hm.2.1, properties_of_composition G S hS φeq φR hφeq hφR _ _ A hm hc⟩

end Lax185574Proofs.Conversions.ChainComposition
