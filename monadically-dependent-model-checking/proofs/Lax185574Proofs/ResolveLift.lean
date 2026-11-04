import Lax185574Proofs.ResolveRam.Glue.Assemble
import Lax185574.ResolveLift
import Lax185574Proofs.Interface.Poly

/-!
Computing the partial graph after a resolve and the type trees of all its
vertices on the word RAM (lem:resolve-lift).
-/

namespace Lax185574Proofs.ResolveLift

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ResolveLift Lax185574.PartialGraphEncoding
open Lax185574.DistanceMatrix

/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_resolveLift_old :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
        Computes p e c (G, distMatrix G, P, Q, s, family G k q)
          (resolveBy G s P Q, distMatrix (resolveBy G s P Q), family (resolveBy G s P Q) k q)
          (fun _ => c * (n + 1) ^ 2 *
            (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a) ∧
        ∀ b : Fin n, wordLength (tree (resolveBy G s P Q) k q ![b]) ≤
          c * (treeCount G (resolveBy G s P Q) k q + 1) ^ a :=
  Lax185574Proofs.ResolveRam.resolve_of_glue Lax185574Proofs.ResolveRam.rglueHyp

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.ResolveLift.exists_program_resolveLift
---
The program is the loop driver of the glue program of the resolve lift
with the switch of its five callees: the rank shift (the rank shift
lemma), the far tree (the far tree lemma), the far composition (the far
composition lemma), the canonical form (the canonical form observation)
and the scatter type (the lemma on computing scatter types). The glue
program first computes the scatter type of the input, then walks down
the levels of the items, asking for the shift, the far tree and the
compositions of each item, and walks up again, asking for the canonical
forms of the atoms and of the children of each item. Its last round
builds the resolved graph and its distance matrix, by the formula for
distances after a resolve, and writes the output. Every round runs within a constant times `(n + 1)
Y^a` steps, with `Y = M + T + 1`, except the first two and the last
round, which read the input or write the output and run within a
constant times `(n + 1)² Y^a` steps. With at most a constant times `(n +
1)(T + 1)^(q + 1)` rounds, the total time of the glue program is within
the bound. The sizes of the output trees are those of the type trees of
the resolved graph.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_resolveLift :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
        let H := resolveBy G s P Q
        let T := treeCount G H k q
        A.Computes c (G, distMatrix G, P, Q, s, family G k q) (H, distMatrix H, family H k q)
            (n ^ 2 * (maxTreeSize G k q + T + 1) ^ a) ∧
          ∀ b : Fin n, (encode (tree H k q ![b])).length ≤ c * (T + 1) ^ a := by
  obtain ⟨p, e, h⟩ := exists_program_resolveLift_old
  refine ⟨⟨p, e⟩, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := h k q
  refine ⟨4 * c, a, fun n G P Q s hk => ?_⟩
  intro H T
  obtain ⟨hc, hsize⟩ := h n G P Q s hk
  refine ⟨?_, fun b => le_trans (hsize b) (Nat.mul_le_mul_right _ (by omega))⟩
  refine computes_of_old_nat (n ^ 2 * (maxTreeSize G k q + T + 1) ^ a) (by push_cast; rfl)
    (by omega) ?_ hc
  show c * (n + 1) ^ 2 * (maxTreeSize G k q + T + 1) ^ a ≤ _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hM : maxTreeSize G k q = 0 := by simp [maxTreeSize]
    have hT : T = 0 := by simp [T, treeCount]
    rw [hM, hT]
    simp
    omega
  · refine le_trans ?_ (Nat.le_add_right _ _)
    have h4 : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith
    calc c * (n + 1) ^ 2 * (maxTreeSize G k q + T + 1) ^ a
        ≤ c * (4 * n ^ 2) * (maxTreeSize G k q + T + 1) ^ a := by gcongr
      _ = 4 * c * (n ^ 2 * (maxTreeSize G k q + T + 1) ^ a) := by ring

end Lax185574Proofs.ResolveLift
