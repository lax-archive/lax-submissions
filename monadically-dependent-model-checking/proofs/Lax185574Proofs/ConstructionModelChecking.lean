import Lax185574Proofs.MC.Asm.Final
import Lax185574Proofs.MC.Glue.Spec
import Lax185574Proofs.MC.Brute.Prog
import Lax185574Proofs.RamPar2
import Lax185574.ConstructionModelChecking
import Lax185574Proofs.LegacyInputs
import Lax185574Proofs.Interface.KitG3
import Lax185574Proofs.Interface.SeqBridge

/-!
Model checking along a construction sequence (thm:mc), on the word RAM.

The program runs two threads in parallel: the pipeline of the proof of
thm:mc, which follows the construction sequence with the merge lift, the
resolve lift and the evaluation as callees, and a brute-force evaluator
for short inputs and graphs without vertices. The assembly is
`Lax185574Proofs.MC.mc_of_parts`, with the parallel combinator
`Lax185574Proofs.MC.par2_spec`, the brute force
`Lax185574Proofs.MC.Brute.bruteSpec` and the glue program of the pipeline
`Lax185574Proofs.MC.Glue.glueHyp`.
-/

namespace Lax185574Proofs.ConstructionModelChecking

open Lax3.FirstOrder Lax271696.GraphEncoding
open Lax808846.Ram Lax808846.RamComputes
open Lax185574.WordEncoding Lax185574.InstanceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.SequenceEncoding Lax185574.Width
open Lax185574.ConstructionModelChecking

open Classical in
/-- The statement for the older input format and the older notion of computing. -/
theorem exists_program_modelChecking_sequence_old :
    ∃ (p : Program) (e : ℕ), ∀ φ : FO 0, ∃ r d c b : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : List (PartialGraph (Fin n)))
        (K w : ℕ),
        IsConstructionSequence G s → width r d s ≤ K →
          ComputesInTime w p
            {x | EncodesInput x n G s φ ∧
              ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
            (fun _ => if Sat G Fin.elim0 φ then [1] else [0])
            (fun _ => c * s.length * (n + 1) ^ 2 * (K + 1) ^ b) := by
  obtain ⟨par, K, hpar⟩ := Lax185574Proofs.MC.par2_spec
  exact Lax185574Proofs.MC.mc_of_parts hpar Lax185574Proofs.MC.Brute.bruteSpec
    Lax185574Proofs.MC.Glue.glueHyp


open Lax185574.Graphs Lax185574.FirstOrderLogic Lax185574.Algorithms Lax185574.Encoding
  Lax185574Proofs.Interface in
/--
---
conclusion: Lax185574.ConstructionModelChecking.exists_program_modelChecking_sequence
---
Two threads run in parallel at a word length a constant below the given
one. The first thread removes the graph from the input and runs a loop
that alternates a glue program with a callee. The glue program follows
the construction sequence step by step. It keeps the current partial
graph with its matrix of distances and the type trees of all vertices,
and issues one call per step and finally one call of the evaluation on
the tree of a vertex and the localized sentence. For a merge step the
callee maps the merge lift over the trees of all vertices, for a resolve
step it runs the resolve lift, which also returns the new matrix of
distances. Each query is guarded for the word length of its callee, so
every halting run of the pipeline is right, and the pipeline halts
within `c · m · (n + 1)² · (K + 1) ^ b` steps when the input is long
enough. The
second thread evaluates the sentence by brute force, which is fast for
short inputs and for graphs without vertices. The combinator outputs the
answer of a thread that halts.

The proof is carried out for the input format with the graph in
compressed sparse row form and the notion `Lax185574.Computing.Computes`,
with a time bound that holds for every bound on the width. The algorithm converts the word of the graph
into compressed sparse rows (`Interface.nbr_bridge`) and runs the
program for that format with the width itself as the bound. The conversion takes time
linear in the length of the input, which is `O(λ · (n+1)²)` for a fixed
sentence.
-/
theorem exists_program_modelChecking_sequence :
    ∃ A : Algorithm, ∀ φ : Sentence, ∃ r d c b : ℕ,
      ∀ (G : Graph) (σ : Script G.n), IsConstructionSequence G.toSimpleGraph σ.run →
        A.Decides c (G, σ, φ) (G ⊨ φ)
          (σ.run.length * (G.n + 1) ^ 2 * (width r d σ.run + 1) ^ b) := by
  obtain ⟨p, e, hp⟩ := exists_program_modelChecking_sequence_old
  obtain ⟨q, K, hq⟩ := nbr_bridge 0 p
  refine ⟨⟨q, e + 1⟩, fun φ => ?_⟩
  obtain ⟨r, d, c, b, hc⟩ := hp (Formula.toFO φ)
  obtain ⟨L, hL⟩ : ∃ L, L = (toWord (Formula.toFO φ)).length := ⟨_, rfl⟩
  refine ⟨r, d, K * (c + L + 7) + 4 * c * 3 ^ e + K, b, fun G σ hcs => ?_⟩
  set ls := nbLists G.toSimpleGraph with hls
  set R := encode σ ++ toWord (Formula.toFO φ) with hR
  have ha : encode (G, σ, φ) = [] ++ nbWord ls ++ R := by
    simp only [KitG3.encode_pair, encode_graph, toWord_graph_eq, encode_formula, List.nil_append,
      hR, hls]
  have henc : EncodesInput ([] ++ csrWord ls ++ R) G.n G.toSimpleGraph σ.run (Formula.toFO φ) :=
    ⟨csrWord ls, encode σ, encodesGraph_csrWord _, ⟨σ, rfl, rfl⟩, by
      simp only [List.nil_append, hR, List.append_assoc]⟩
  unfold Algorithm.Decides
  refine nbr_wrap (c := c) (e := e) (P := []) (R := R) hq rfl G.toSimpleGraph ha
    (c * σ.run.length * (G.n + 1) ^ 2 * (width r d σ.run + 1) ^ b) (fun w hw => ?_)
    (by omega) ?_
  · rw [decide_models_word]
    exact hc G.n G.toSimpleGraph σ.run (width r d σ.run) w hcs le_rfl _ ⟨henc, hw⟩
  -- the time
  set S := ls.flatten.length with hS
  have hSn : S ≤ G.n * G.n := length_flatten_nbLists_le G.toSimpleGraph
  have hlsl : ls.length = G.n := length_nbLists _
  have hσ := length_encode_script_le σ
  have hl1 := one_le_length_run σ
  set M := σ.run.length * (G.n + 1) ^ 2 with hM
  set Tn := M * (width r d σ.run + 1) ^ b with hTn
  have hB : 1 ≤ (width r d σ.run + 1) ^ b := Nat.one_le_pow _ _ (by omega)
  have hnM : (G.n + 1) ^ 2 ≤ M := Nat.le_mul_of_pos_left _ hl1
  have hlM : σ.run.length ≤ M := Nat.le_mul_of_pos_right _ (by positivity)
  have hMT : M ≤ Tn := Nat.le_mul_of_pos_right _ hB
  have hxl : (encode (G, σ, φ)).length = 1 + G.n + 2 * S + (encode σ).length + L := by
    rw [ha, List.nil_append, List.length_append, length_nbWord, hlsl, hR, List.length_append, hL]
    ring
  have h1 : (encode (G, σ, φ)).length + 1 ≤ (L + 5) * M := by
    have : 2 + 2 * G.n + 2 * S ≤ 2 * (G.n + 1) ^ 2 := by nlinarith
    have : L ≤ L * M := Nat.le_mul_of_pos_right _ (by omega)
    have e5 : (L + 5) * M = L * M + 2 * M + 3 * M := by ring
    omega
  have h2 : c * σ.run.length * (G.n + 1) ^ 2 * (width r d σ.run + 1) ^ b = c * Tn := by
    rw [hTn, hM]; ring
  have h3 : K * (c * σ.run.length * (G.n + 1) ^ 2 * (width r d σ.run + 1) ^ b +
      (encode (G, σ, φ)).length + 1) ≤ (K * (c + L + 7) + 4 * c * 3 ^ e + K) * Tn := by
    rw [h2]
    have : c * Tn + (encode (G, σ, φ)).length + 1 ≤ (c + L + 7) * Tn := by
      have : (L + 5) * M ≤ (L + 5) * Tn := Nat.mul_le_mul_left _ hMT
      have e7 : (c + L + 7) * Tn = c * Tn + (L + 5) * Tn + 2 * Tn := by ring
      omega
    calc K * (c * Tn + (encode (G, σ, φ)).length + 1) ≤ K * ((c + L + 7) * Tn) :=
          Nat.mul_le_mul_left _ this
      _ = K * (c + L + 7) * Tn := by ring
      _ ≤ (K * (c + L + 7) + 4 * c * 3 ^ e + K) * Tn := Nat.mul_le_mul_right _ (by omega)
  have h4 : ((K * (c * σ.run.length * (G.n + 1) ^ 2 * (width r d σ.run + 1) ^ b +
      (encode (G, σ, φ)).length + 1) : ℕ) : ℝ) ≤
      ((K * (c + L + 7) + 4 * c * 3 ^ e + K : ℕ) : ℝ) * (Tn : ℝ) := by exact_mod_cast h3
  have hT : (Tn : ℝ) = σ.run.length * ((G.n : ℝ) + 1) ^ 2 * ((width r d σ.run : ℝ) + 1) ^ b := by
    rw [hTn, hM]; push_cast; ring
  rw [hT] at h4
  have h0 : (0 : ℝ) ≤ ((K * (c + L + 7) + 4 * c * 3 ^ e + K : ℕ) : ℝ) := Nat.cast_nonneg _
  push_cast at h4 h0 ⊢
  linarith

end Lax185574Proofs.ConstructionModelChecking
