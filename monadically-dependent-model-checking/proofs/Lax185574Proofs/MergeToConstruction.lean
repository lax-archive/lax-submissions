import Lax185574Proofs.Conversions.Ram.ConsProgram
import Lax185574Proofs.Conversions.MergeConstructionFunction
import Lax185574Proofs.Interface.KitG3

/-!
cl:from-merge-to-construction (`Lax185574.MergeToConstruction`): the
construction script `Lax185574Proofs.Conversions.MergeConstruction.script`
has all the required properties, and the program
`Lax185574Proofs.Conversions.Ram.consProg` writes its word in time
`O(m · n²)`.
-/

namespace Lax185574Proofs.MergeToConstruction

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.Partitions Lax185574.MergeSequences Lax185574.BetterMergeSequences
open Lax185574.ConstructionSequences Lax185574.ConstructionWidth
open Lax185574.SequenceEncoding Lax185574.LocalDefinability Lax185574.FirstOrderTypes
open Lax185574Proofs.Conversions.MergeConstruction Lax185574Proofs.Conversions.Ram
open Lax185574Proofs.Words

/-- The statement for simple graphs on `Fin n` and the older
`Lax185574.Computing.Computes`.

The script is `script G ms` with `A = 3`, and its properties are
`script_properties`. The program reads the graph into an adjacency
matrix and then the stages one at a time. Stage `j` holds the labels of
`𝒫_j`, the least vertices of the parts, and reads those of `𝒫_{j+1}`
from the word of the partition, where the first member of every part is
its least vertex, together with the adjacency matrix of `R_{j+1}`. After
the last stage it uses one part and all pairs. Three flag matrices,
indexed by the ordered pair of labels, record for every pair of parts
whether some pair of distinct vertices of their rectangle lies outside
`R_{j+1}`, is unresolved, or is unresolved and an edge. From them the
resolves are emitted in lexicographic order of the least vertices, the
resolved pairs are updated by the blocks, and the merges are emitted.
The steps go to a buffer, since their number is written before them.
Every stage takes `O(n²)` steps. Values stay below
`8 · (|x| + M + 1)³`, so word-length exponent `3` suffices.
-/
theorem exists_constructionSequence_of_mergeSequence_old :
    ∃ (p : Program) (e A : ℕ)
      (M : ∀ n : ℕ, SimpleGraph (Fin n) → List (Setoid (Fin n) × SimpleGraph (Fin n)) →
        Script n),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))),
        IsMergeSequence G ms →
          IsConstructionSequence G (M n G ms).run ∧
          (∀ v ∈ toWord (M n G ms), v ≤ wordLength (M n G ms) + n) ∧
          (M n G ms).run.length ≤ A * (n + 1) * (mergeWidth 1 ms + 1) ∧
          ∀ r : ℕ, 1 ≤ r →
            constructionWidth r (M n G ms).run ≤ max 1 (mergeWidth r ms) ∧
            ((∃ φeq φR : (withColors Language.graph 2).Formula (Fin 2),
                quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
                  StagesDefinable G ms φeq φR) →
              IsRadiusDefinable G (M n G ms).run r (2 * ms.length + 1)
                (max 1 (mergeWidth r ms)) 7)) ∧
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n))
        (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))), IsMergeSequence G ms →
          Computes p e c (G, ms) (M n G ms) (fun _ => c * (ms.length + 1) * (n + 1) ^ 2) := by
  refine ⟨Lax808846Proofs.Compile.compileProgram consLayout consProg, 3, 3,
    fun n G ms => script G ms, fun n G ms hm => script_properties n G ms hm, 20001,
    fun n G ms _ => ?_⟩
  refine computes_of_run_le consProg_ok (A := 8) (by norm_num) (by norm_num)
    (by simp [layoutConst, consLayout]) ?_ ?_
  · change toWord G ++ toWord ms ≠ []
    rw [toWord_graph_nbhds]; simp
  · obtain ⟨σ', hr, hout⟩ := consProg_run G ms
    refine ⟨consExt n ms.length, σ', _, hr, hout, ?_⟩
    simp only [Lax808846Proofs.Compile.Layout.const]
    have : 1 ≤ (ms.length + 1) * (n + 1) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith

open Lax185574.Graphs Lax185574.Algorithms Lax185574Proofs.Interface
open Lax185574Proofs.Interface.KitG3

/--
---
conclusion: Lax185574.MergeToConstruction.exists_constructionSequence_of_mergeSequence
---
The statement for graphs and `Algorithm.Computes`, from
the version for simple graphs: the algorithm is the
program with its exponent, the script of a graph is that of its simple
graph, and the constants stay the same.
-/
theorem exists_constructionSequence_of_mergeSequence :
    ∃ (A : Algorithm) (c K : ℕ) (script : (G : Graph) →
        List (Setoid (Fin G.n) × SimpleGraph (Fin G.n)) → Script G.n),
      ∀ (G : Graph) (ms : List (Setoid (Fin G.n) × SimpleGraph (Fin G.n))),
        IsMergeSequence G.toSimpleGraph ms →
          let σ := script G ms
          IsConstructionSequence G.toSimpleGraph σ.run ∧ σ.HasSmallNumbers ∧
          σ.run.length ≤ K * (G.n + 1) * (mergeWidth 1 ms + 1) ∧
          (∀ r : ℕ, 1 ≤ r →
            constructionWidth r σ.run ≤ max 1 (mergeWidth r ms) ∧
            ((∃ φeq φR : (withColors Language.graph 2).Formula (Fin 2),
                quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
                  StagesDefinable G.toSimpleGraph ms φeq φR) →
              IsRadiusDefinable G.toSimpleGraph σ.run r (2 * ms.length + 1)
                (max 1 (mergeWidth r ms)) 7)) ∧
          A.Computes c (G, ms) σ ((ms.length + 1) * (G.n + 1) ^ 2) := by
  obtain ⟨p, e, K, M, hM, c, hc⟩ := exists_constructionSequence_of_mergeSequence_old
  refine ⟨⟨p, e⟩, c, K, fun G ms => M G.n G.toSimpleGraph ms, fun G ms hm => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hM G.n G.toSimpleGraph ms hm
  refine ⟨a1, a2, a3, a4, computes_congr (encode_graph_pair G ms).symm rfl
    (computes_of_old le_rfl ?_ (hc G.n G.toSimpleGraph ms hm))⟩
  have := one_le_succ_mul_succ_pow ms.length G.n 2
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  nlinarith

end Lax185574Proofs.MergeToConstruction
