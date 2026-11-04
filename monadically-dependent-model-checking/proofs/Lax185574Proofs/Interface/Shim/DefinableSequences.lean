import Lax185574.DefinableSequences
import Lax185574Proofs.LegacyInputs
import Lax185574Proofs.Interface.SeqBridge
import Lax185574Proofs.Compose.Basic
import Lax185574Proofs.Interface.KitG3
import Lax808846.RamComputes
import Lax710763.MonadicDependence
import Lax185574Proofs.Compose.Monotone

/-!
The statement of `Lax185574.DefinableSequences` for a program that reads
the pair `(r, ε)` followed by the graph in compressed sparse row form,
graph classes of the archive, and the time bound
`⌊c · (n+1)^(3+η)⌋ + c · |x|` at every admissible word length, derived
from the concept.

The program is the pipe `csr_bridge` of the converter from compressed
sparse rows to the word of the graph into the algorithm of the concept.
Its output on a word that encodes `(r, ε)` and a graph is the encoding
of the script of the concept. The algorithm is used with the time
`n^(3 + min η 1)`, whose degree is bounded. So the condition on the word
length of the older statement, with the exponent `3e + 4`, makes this
time fit into a word, and the program halts at every such word length.
-/

namespace Lax185574Proofs.Shim.DefinableSequences

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax808846.Ram Lax808846.RamComputes Lax271696.GraphEncoding
open Lax185574.PartialGraphs Lax185574.ConstructionSequences
open Lax185574.Encoding Lax185574.LocalDefinability Lax185574.WordEncoding
open Lax185574.DefinableSequences (EncodesInput)
open Lax185574Proofs.Interface

theorem exists_program_definableSequence :
    ∃ (p : Program) (f : List ℕ → List ℕ) (e A : ℕ),
      (∀ (r : ℕ) (ε : ℚ) (n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
        1 ≤ r → 0 < ε → EncodesInput x r ε n G →
          (∃ s, EncodesSequence (f x) s ∧ IsConstructionSequence G s) ∧
            ∀ v ∈ f x, v ≤ (f x).length + n) ∧
      ∀ (C : GraphClass), MonadicallyDependent C →
        ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
          ∀ η : ℝ, 0 < η → ∃ c : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
            (∀ w : ℕ, ComputesInTime w p
              {x | EncodesInput x r ε n G ∧
                ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
              f (fun x => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * x.length)) ∧
            ∀ (x : List ℕ) (s : List (PartialGraph (Fin n))),
              EncodesInput x r ε n G → EncodesSequence (f x) s →
                (s.length : ℝ) ≤ c * ((n : ℝ) + 1) ^ (1 + (a₀ : ℝ) * ε) ∧
                IsRadiusDefinable G s r (⌈(A : ℚ) * r / ε⌉₊ + A)
                  ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((a₀ : ℝ) * ε)⌋₊ 7 := by
  obtain ⟨A, K, script, hcorr, hclass⟩ :=
    Lax185574.DefinableSequences.exists_program_definableSequence
  obtain ⟨q, Kq, hq⟩ := csr_bridge 4 A.program
  set F : ℕ × ℚ → (Σ n, SimpleGraph (Fin n)) → List ℕ :=
    fun a H => encode (script a.1 a.2 (Lax185574.Graphs.Graph.ofSimpleGraph H.2)) with hF
  refine ⟨q, decodePre F, 3 * A.wordExponent + 4, K, ?_, ?_⟩
  · intro r ε n G x hr hε ⟨g, hg, hx⟩
    rw [decodePre_eq F hg hx]
    obtain ⟨hcs, hsm⟩ := hcorr r ε (Lax185574.Graphs.Graph.ofSimpleGraph G) hr hε
    exact ⟨⟨_, ⟨_, rfl, rfl⟩, hcs⟩, hsm⟩
  · intro C hC
    obtain ⟨a, ha1, ha⟩ := hclass (ofOld C) ((monadicallyDependent_ofOld_iff C).mpr hC)
    refine ⟨a, ha1, fun r ε hr hε η hη => ?_⟩
    obtain ⟨c, hc⟩ := ha r ε hr hε (min η 1) (lt_min hη one_pos)
    obtain ⟨c', hc'⟩ : ∃ c', c' = 4 * 8 ^ A.wordExponent * c + 8 * c + Kq * (c + 2) + Kq + c :=
      ⟨_, rfl⟩
    refine ⟨c', fun n G hG => ⟨fun w x ⟨⟨g, hg, hx⟩, hadm⟩ => ?_, fun x s ⟨g, hg, hx⟩ hs => ?_⟩⟩
    · obtain ⟨hcomp, -, -⟩ := hc (Lax185574.Graphs.Graph.ofSimpleGraph G) hG
      rw [decodePre_eq F hg hx]
      subst hx
      have ha' : encode (r, ε, Lax185574.Graphs.Graph.ofSimpleGraph G) =
          encode (r, ε) ++ toWord G := by
        simp only [KitG3.encode_pair, encode_graph, List.append_assoc]; rfl
      exact seq_shim hq (length_encode_nat_rat r ε) hg ha' hη hcomp (by omega) w hadm
    · obtain ⟨-, hlen, hdef⟩ := hc (Lax185574.Graphs.Graph.ofSimpleGraph G) hG
      rw [decodePre_eq F hg hx] at hs
      have hs' := Lax185574Proofs.Compose.encodesSequence_unique hs ⟨_, rfl, rfl⟩
      subst hs'
      have hcc : (c : ℝ) ≤ c' := by exact_mod_cast (show c ≤ c' by omega)
      refine ⟨le_trans hlen (mul_le_mul_of_nonneg_right hcc (by positivity)),
        Lax185574Proofs.Compose.isRadiusDefinable_mono le_rfl (Nat.floor_le_floor ?_) hdef⟩
      exact mul_le_mul_of_nonneg_right hcc (by positivity)

end Lax185574Proofs.Shim.DefinableSequences
