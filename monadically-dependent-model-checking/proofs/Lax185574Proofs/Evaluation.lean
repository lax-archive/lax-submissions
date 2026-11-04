import Lax185574Proofs.EvalRam.Run
import Lax185574.Evaluation
import Lax185574Proofs.Interface.Poly

/-!
Evaluation of a formula on a type tree, on the word RAM (lem:eval).

The program is `Lax185574Proofs.EvalRam.prog`. It reads the tree and the
formula, lists the nodes of the tree, and fills a table indexed by the
positions of the code of the formula and the nodes. Its run is
`Lax185574Proofs.EvalRam.prog_run`, and the answer is the semantic core
`Lax185574Proofs.TreeAlgo.evalNode`.
-/

namespace Lax185574Proofs.Evaluation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574.PartialGraphs
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

open Classical in
/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_eval_old :
    ∃ (p : Lax808846.Ram.Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
        (φ : DistFO ℓ), ℓ ≤ k → DRank k q φ →
        Lax185574.Computing.Computes p e c (tree G k q u, φ) (decide (Sat G u φ))
          (fun m => c * (m + 1) ^ a) := by
  refine ⟨Lax808846Proofs.Compile.compileProgram layout prog, 2, fun k q =>
    ⟨bridgeConst layout 8 2000, 3, fun n G ℓ u φ _ hφ => ?_⟩⟩
  refine computes_of_run prog_ok (by norm_num) (by norm_num) (by simp; exact List.cons_ne_nil _ _) ?_
  have hx : toWord (tree G k q u, φ) = inWord k q ℓ (node G k q u) φ := by
    show _ ++ toWord φ = _ ++ code φ
    rw [Lax185574Proofs.Legacy.encode_eq_code]
    rfl
  obtain ⟨σ', hr, hout⟩ := prog_run k q ℓ (node G k q u) φ
  rw [← hx] at hr
  refine ⟨_, σ', hr, ?_⟩
  rw [hout]
  have hev := evalNode_node G hφ u
  rw [Lax185574Proofs.Legacy.toWord_bool]
  by_cases hs : Sat G u φ
  · rw [decide_eq_true hs, (hev.2 hs)]; rfl
  · have : evalNode (node G k q u) φ = false := Bool.eq_false_iff.mpr fun h => hs (hev.1 h)
    rw [decide_eq_false hs, this]; rfl

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.Evaluation.exists_program_eval
---
The program reads the tree, copies the word of its root into an array,
reads the code of the formula into a second array, and lists the nodes
of the tree in breadth-first order. It fills a table with a row for
every position of the code and a column for every node, from the last
position to the first. At a position where a subformula starts, the
entry of a node is the value of the subformula at the node: an atom is
looked up among the atom codes of the node, a negation or a conjunction
is read off the rows of its subformulas, and `∃ y (dist(xᵢ, y) ≤ s ∧ ψ)`
holds if some extension of the node with guard `i` has a child where `ψ`
holds, read off the row of `ψ`. A second table records where every
subformula ends, which locates the second conjunct of a conjunction.
This is the recursion of the proof of the evaluation lemma over pairs of
a subformula and a node. The answer is the entry of the first position
at the root, which is the semantic core `evalNode`, whose correctness is
`evalNode_node`. A cell takes time linear in the length of the input, so
the time is a polynomial of degree three. Every value is at most a
constant times the square of the input length, so word-length exponent
`2` suffices.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_eval :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n) (φ : DistFO ℓ),
        ℓ ≤ k → DRank k q φ →
          A.Decides c (tree G k q u, φ) (Sat G u φ)
            (((encode (tree G k q u)).length + (encode φ).length + 1) ^ a) := by
  obtain ⟨p, e, h⟩ := exists_program_eval_old
  refine ⟨⟨p, e⟩, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := h k q
  refine ⟨c, a, fun n G ℓ u φ hℓ hφ => ?_⟩
  unfold Algorithm.Decides
  convert computes_of_poly
    (N := ((encode (tree G k q u)).length : ℝ) + (encode φ).length)
    (by rw [length_encode_prod]; push_cast; rfl) (h n G ℓ u φ hℓ hφ)

end Lax185574Proofs.Evaluation
