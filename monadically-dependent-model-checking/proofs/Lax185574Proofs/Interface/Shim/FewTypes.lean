import Lax185574.FewTypes
import Lax185574Proofs.LegacyInputs
import Lax185574Proofs.Interface.SeqBridge
import Lax185574Proofs.Compose.Basic
import Lax185574Proofs.Interface.KitG3
import Lax808846.RamComputes
import Lax710763.MonadicDependence

/-!
The statement of `Lax185574.FewTypes` for a program that reads the
triple `(r, q, ε)` followed by the graph in compressed sparse row form,
graph classes of the archive, and the time bound
`⌊c · (n+1)^(3+η)⌋ + c · |x|` at every admissible word length, derived
from the concept as in `Lax185574Proofs.Shim.DefinableSequences`.
-/

namespace Lax185574Proofs.Shim.FewTypes

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax808846.Ram Lax808846.RamComputes Lax271696.GraphEncoding
open Lax185574.PartialGraphs Lax185574.ConstructionSequences
open Lax185574.Encoding Lax185574.Width Lax185574.WordEncoding
open Lax185574.FewTypes (EncodesInput)
open Lax185574Proofs.Interface

theorem exists_program_fewTypes :
    ∃ (p : Program) (f : List ℕ → List ℕ) (e : ℕ),
      (∀ (r q : ℕ) (ε : ℚ) (n : ℕ) (G : SimpleGraph (Fin n)) (x : List ℕ),
        0 < ε → EncodesInput x r q ε n G →
          (∃ s, EncodesSequence (f x) s ∧ IsConstructionSequence G s) ∧
            ∀ v ∈ f x, v ≤ (f x).length + n) ∧
      ∀ (C : GraphClass), MonadicallyDependent C → ∀ q : ℕ,
        ∃ a : ℕ, 1 ≤ a ∧ ∀ (r : ℕ) (ε : ℚ), 0 < ε → ∀ η : ℝ, 0 < η → ∃ c : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
            (∀ w : ℕ, ComputesInTime w p
              {x | EncodesInput x r q ε n G ∧
                ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
              f (fun x => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * x.length)) ∧
            ∀ (x : List ℕ) (s : List (PartialGraph (Fin n))),
              EncodesInput x r q ε n G → EncodesSequence (f x) s →
                (s.length : ℝ) ≤ c * ((n : ℝ) + 1) ^ (1 + (a : ℝ) * ε) ∧
                (width r q s : ℝ) ≤ c * ((n : ℝ) + 1) ^ ((a : ℝ) * ε) := by
  obtain ⟨A, script, hcorr, hclass⟩ := Lax185574.FewTypes.exists_program_fewTypes
  obtain ⟨p, Kq, hq⟩ := csr_bridge 5 A.program
  set F : ℕ × ℕ × ℚ → (Σ n, SimpleGraph (Fin n)) → List ℕ :=
    fun a H => encode (script a.1 a.2.1 a.2.2 (Lax185574.Graphs.Graph.ofSimpleGraph H.2)) with hF
  refine ⟨p, decodePre F, 3 * A.wordExponent + 4, ?_, ?_⟩
  · intro r q ε n G x hε ⟨g, hg, hx⟩
    rw [decodePre_eq F hg hx]
    obtain ⟨hcs, hsm⟩ := hcorr r q ε (Lax185574.Graphs.Graph.ofSimpleGraph G) hε
    exact ⟨⟨_, ⟨_, rfl, rfl⟩, hcs⟩, hsm⟩
  · intro C hC q
    obtain ⟨a, ha1, ha⟩ := hclass (ofOld C) ((monadicallyDependent_ofOld_iff C).mpr hC) q
    refine ⟨a, ha1, fun r ε hε η hη => ?_⟩
    obtain ⟨c, hc⟩ := ha r ε hε (min η 1) (lt_min hη one_pos)
    obtain ⟨c', hc'⟩ : ∃ c', c' = 4 * 8 ^ A.wordExponent * c + 8 * c + Kq * (c + 2) + Kq + c :=
      ⟨_, rfl⟩
    refine ⟨c', fun n G hG => ⟨fun w x ⟨⟨g, hg, hx⟩, hadm⟩ => ?_, fun x s ⟨g, hg, hx⟩ hs => ?_⟩⟩
    · obtain ⟨hcomp, -, -⟩ := hc (Lax185574.Graphs.Graph.ofSimpleGraph G) hG
      rw [decodePre_eq F hg hx]
      subst hx
      have ha' : encode (r, q, ε, Lax185574.Graphs.Graph.ofSimpleGraph G) =
          encode (r, q, ε) ++ toWord G := by
        simp only [KitG3.encode_pair, encode_graph, List.append_assoc]; rfl
      exact seq_shim hq (length_encode_nat_nat_rat r q ε) hg ha' hη hcomp (by omega) w hadm
    · obtain ⟨-, hlen, hwid⟩ := hc (Lax185574.Graphs.Graph.ofSimpleGraph G) hG
      rw [decodePre_eq F hg hx] at hs
      have hs' := Lax185574Proofs.Compose.encodesSequence_unique hs ⟨_, rfl, rfl⟩
      subst hs'
      have hcc : (c : ℝ) ≤ c' := by exact_mod_cast (show c ≤ c' by omega)
      exact ⟨le_trans hlen (mul_le_mul_of_nonneg_right hcc (by positivity)),
        le_trans hwid (mul_le_mul_of_nonneg_right hcc (by positivity))⟩

end Lax185574Proofs.Shim.FewTypes
