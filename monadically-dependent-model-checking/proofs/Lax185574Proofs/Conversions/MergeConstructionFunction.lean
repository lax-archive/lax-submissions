import Lax185574Proofs.Conversions.MergeConstructionDefinable

/-!
The mathematical half of cl:from-merge-to-construction
(`MergeToConstruction`): the construction script of the proof, as a
function of the graph and the merge sequence, has all properties that
the lemma asks of its output, with the constant `A = 3` of the length
bound. What remains for its proof is a program that computes the script
within the time bound.
-/

namespace Lax185574Proofs.Conversions.MergeConstruction

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.WordEncoding Lax185574.MergeSequences Lax185574.BetterMergeSequences
open Lax185574.ConstructionSequences Lax185574.ConstructionWidth
open Lax185574.SequenceEncoding Lax185574.LocalDefinability Lax185574.FirstOrderTypes

/-- **The properties of the construction script** of
cl:from-merge-to-construction, in the form of
`MergeToConstruction.exists_constructionSequence_of_mergeSequence`, with
`A = 3`. -/
theorem script_properties (n : ℕ) (G : SimpleGraph (Fin n))
    (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))) (hm : IsMergeSequence G ms) :
    IsConstructionSequence G (script G ms).run ∧
      (∀ v ∈ toWord (script G ms), v ≤ wordLength (script G ms) + n) ∧
      (script G ms).run.length ≤ 3 * (n + 1) * (mergeWidth 1 ms + 1) ∧
      ∀ r : ℕ, 1 ≤ r →
        constructionWidth r (script G ms).run ≤ max 1 (mergeWidth r ms) ∧
        ((∃ φeq φR : (withColors Language.graph 2).Formula (Fin 2),
            quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
              StagesDefinable G ms φeq φR) →
          IsRadiusDefinable G (script G ms).run r (2 * ms.length + 1)
            (max 1 (mergeWidth r ms)) 7) :=
  ⟨isConstructionSequence hm, entries_le, length_run_le hm,
    fun r _ => ⟨constructionWidth_le hm r, isRadiusDefinable hm r⟩⟩

end Lax185574Proofs.Conversions.MergeConstruction
