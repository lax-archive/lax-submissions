import Lax185574Proofs.CompRam.GTop
import Lax185574Proofs.CompRam.Far
import Lax185574Proofs.Interface.Shim.CanonicalForm
import Lax185574Proofs.Interface.Shim.RankShift
import Lax185574Proofs.Interface.Shim.Restriction
import Lax185574Proofs.Interface.Poly

/-!
Far composition on the word RAM (lem:compose).
-/

namespace Lax185574Proofs.FarComposition

open Lax808846.Ram Lax185574.Computing Lax185574.WordEncoding Lax185574.TypeTrees
open Lax185574.PartialGraphs Lax185574.GaifmanGraph
open Lax3.DistFO (rhoMinus)

/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_compose_old :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ₁ ℓ₂ : ℕ) (u₁ : Fin ℓ₁ → Fin n)
        (u₂ : Fin ℓ₂ → Fin n),
        1 ≤ ℓ₁ → 1 ≤ ℓ₂ → ℓ₁ + ℓ₂ ≤ k →
        (∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) →
        Computes p e c (tree G k q u₁, tree G k q u₂) (tree G k q (Fin.append u₁ u₂))
          (fun m => c * (m + 1) ^ a) :=
  Lax185574Proofs.CompRam.far_of_glue Lax185574Proofs.CompRam.glue_hyp
    Lax185574Proofs.Shim.Restriction.exists_program_restrict
    Lax185574Proofs.Shim.RankShift.exists_program_shift
    Lax185574Proofs.Shim.CanonicalForm.exists_program_canonical

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.FarComposition.exists_program_compose
---
The program runs a glue program and the three programs of the
restriction lemma, the rank shift lemma and the canonical form
observation in the loop driver. The glue program runs the recursion of
the far composition with an explicit stack of frames: each round reads
the stack and the answer to its last question, does one step of the
recursion and asks the next question, a rank shift, a restriction or a
canonical form, or writes the type tree of the concatenation. Before it
halts, every round checks that the question is admissible for the
program that answers it, that the round counter is small against the
word length of its region, and that its output fits, so every halting
run inside the driver is right.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_compose :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ₁ ℓ₂ : ℕ) (u₁ : Fin ℓ₁ → Fin n)
        (u₂ : Fin ℓ₂ → Fin n), 1 ≤ ℓ₁ → 1 ≤ ℓ₂ → ℓ₁ + ℓ₂ ≤ k →
        (∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) →
          A.Computes c (tree G k q u₁, tree G k q u₂) (tree G k q (Fin.append u₁ u₂))
            (((encode (tree G k q u₁)).length + (encode (tree G k q u₂)).length + 1) ^ a) := by
  obtain ⟨p, e, h⟩ := exists_program_compose_old
  refine ⟨⟨p, e⟩, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := h k q
  exact ⟨c, a, fun n G ℓ₁ ℓ₂ u₁ u₂ h₁ h₂ h₃ hfar =>
    computes_of_poly
      (N := ((encode (tree G k q u₁)).length : ℝ) + (encode (tree G k q u₂)).length)
      (by rw [length_encode_prod]; push_cast; rfl) (h n G ℓ₁ ℓ₂ u₁ u₂ h₁ h₂ h₃ hfar)⟩

end Lax185574Proofs.FarComposition
