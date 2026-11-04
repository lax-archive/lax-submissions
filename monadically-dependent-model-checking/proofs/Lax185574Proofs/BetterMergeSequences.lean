import Lax185574Proofs.Conversions.Ram.MergeProgram
import Lax185574Proofs.Interface.KitG3

/-!
lem:better-mw (`Lax185574.BetterMergeSequences`): the merge sequence of
`Lax185574Proofs.Conversions.BetterMerge.mergeSeq` has all the required
properties, and the program of
`Lax185574Proofs.Conversions.Ram.mergeProg` computes it in time
`O(m · n³)`.
-/

namespace Lax185574Proofs.BetterMergeSequences

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.Partitions Lax185574.MergeSequences Lax185574.Chains
open Lax185574.VCDimension Lax185574.Colorings Lax185574.FirstOrderTypes
open Lax185574.BetterMergeSequences Lax185574Proofs.Conversions.BetterMerge
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Words

/-- The statement for simple graphs on `Fin n` and the older
`Lax185574.Computing.Computes`.

The merge sequence takes, for the chain sets in reverse order, the
partition into atomic types split along its least vertices and the pair
relation of the partition into atomic types. Its properties apart from
the running time are those of `exists_formulas_mergeSeq`. The program
reads the graph into an adjacency matrix and the chain into a membership
matrix. For every stage it labels each vertex by the least vertex of its
atomic type and of its part of the split, by scans over all pairs and a
third vertex. It computes the pair relation from the five alternating
layers of the bipartite graphs between parts, kept for all parts at
once, from every vertex and in both polarities. It then writes the
partition, its parts by size and least vertex, and the pair relation as
neighborhood lists. Each stage takes `O(n³)` steps. Every value is below
`4 · (|x| + M + 1)²` for the input `x` with largest entry `M`, so
word-length exponent `2` suffices.
-/
theorem exists_mergeSequence_of_chain_old :
    ∃ (φeq φR : (withColors Language.graph 2).Formula (Fin 2)),
      quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
      ∃ (p : Program) (e : ℕ)
        (M : ∀ n : ℕ, SimpleGraph (Fin n) → List (Finset (Fin n)) →
          List (Setoid (Fin n) × SimpleGraph (Fin n))),
        (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
          IsMergeSequence G (M n G S) ∧ (M n G S).length = S.length ∧
            StagesDefinable G (M n G S) φeq φR ∧
            ∀ r : ℕ, 1 ≤ r →
              mergeWidth r (M n G S) ≤
                chainWidth G (5 * r + 1) S *
                  neighborhoodComplexity G (chainWidth G (5 * r + 1) S)) ∧
        ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
          Computes p e c (G, S) (M n G S) (fun _ => c * (S.length + 1) * (n + 1) ^ 3) := by
  obtain ⟨φeq, φR, h1, h2, hM⟩ := exists_formulas_mergeSeq
  refine ⟨φeq, φR, h1, h2, Lax808846Proofs.Compile.compileProgram mergeLayout mergeProg, 2,
    mergeSeq, hM, 30001, fun n G S _ => ?_⟩
  refine computes_of_run_le mergeProg_ok (A := 4) (by norm_num) (by norm_num)
    (by simp [layoutConst, mergeLayout]) ?_ ?_
  · change toWord G ++ toWord S ≠ []
    rw [toWord_graph_nbhds]; simp
  · obtain ⟨σ', hr, hout⟩ := mergeProg_run G S
    refine ⟨mergeExt n S.length, σ', _, hr, hout, ?_⟩
    simp only [Lax808846Proofs.Compile.Layout.const]
    have : 1 ≤ (S.length + 1) * (n + 1) ^ 3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith

open Lax185574.Graphs Lax185574.Algorithms Lax185574Proofs.Interface
open Lax185574Proofs.Interface.KitG3

/--
---
conclusion: Lax185574.BetterMergeSequences.exists_mergeSequence_of_chain
---
The statement for graphs and `Algorithm.Computes`, from
the version for simple graphs: the algorithm is the program with
its exponent, the merge sequence of a graph is that of its simple graph,
and the constant stays the same.
-/
theorem exists_mergeSequence_of_chain :
    ∃ (φeq φR : (withColors Language.graph 2).Formula (Fin 2)),
      quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
      ∃ (A : Algorithm) (c : ℕ) (M : (G : Graph) → List (Finset (Fin G.n)) →
          List (Setoid (Fin G.n) × SimpleGraph (Fin G.n))),
        ∀ (G : Graph) (S : List (Finset (Fin G.n))), IsChain S →
          IsMergeSequence G.toSimpleGraph (M G S) ∧ (M G S).length = S.length ∧
          (∀ r : ℕ, 1 ≤ r →
            mergeWidth r (M G S) ≤ chainWidth G.toSimpleGraph (5 * r + 1) S *
              neighborhoodComplexity G.toSimpleGraph (chainWidth G.toSimpleGraph (5 * r + 1) S)) ∧
          StagesDefinable G.toSimpleGraph (M G S) φeq φR ∧
          A.Computes c (G, S) (M G S) ((S.length + 1) * (G.n + 1) ^ 3) := by
  obtain ⟨φeq, φR, h1, h2, p, e, M, hM, c, hc⟩ := exists_mergeSequence_of_chain_old
  refine ⟨φeq, φR, h1, h2, ⟨p, e⟩, c, fun G S => M G.n G.toSimpleGraph S, fun G S hS => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hM G.n G.toSimpleGraph S hS
  refine ⟨a1, a2, a4, a3, computes_congr (encode_graph_pair G S).symm rfl
    (computes_of_old le_rfl ?_ (hc G.n G.toSimpleGraph S hS))⟩
  have := one_le_succ_mul_succ_pow S.length G.n 3
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  nlinarith

end Lax185574Proofs.BetterMergeSequences
