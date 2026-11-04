import Lax185574Proofs.ResolveRam.LenBounds
import Lax185574Proofs.StpRam.Bounds
import Lax185574Proofs.StpRam.FinalRead
import Lax185574Proofs.ResolveRam.Glue.Input

/-!
The length of the word of a partial graph, linear in its size.

The word of a graph on `Fin n` is `n` followed by one block per vertex,
the number of its neighbors and the frame `[1, z]` of every neighbor
`z`. So it has length `1 + n + 2 Σ_v deg(v)`. The word of a partial
graph is `n` and its colors, then the word of its edges and the word of
its non-edges. Since every resolved pair is an edge or a non-edge, the
degrees add up to at most `2 ‖G‖` (`offL_add_le`), and the word has
length at most `7 (‖G‖ + 1)`. The input of lem:resolve-lift also holds
the distance matrix, `1 + n (n + 1)` entries, and the family of the
trees of the vertices, at most `n M` entries.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.PartialGraphEncoding Lax185574.ResolveLift
open Lax185574Proofs.TypeTreeSizes Lax185574Proofs.MC Lax185574.DistanceMatrix

variable {n : ℕ}

theorem length_vblk (l : List ℕ) : (StpRam.vblk l).length = 1 + 2 * l.length := by
  unfold StpRam.vblk
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.length_append,
      List.length_nil] at ih ⊢
    omega

theorem length_blocks (H : SimpleGraph (Fin n)) (L : List ℕ) :
    ((L.map fun w => StpRam.vblk (StpRam.nbrL H w)).flatten).length =
      L.length + 2 * (L.map fun w => (StpRam.nbrL H w).length).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      List.sum_cons, length_vblk, ih]
    ring

/-- **The word of a graph.** -/
theorem length_toWord_sgraph (H : SimpleGraph (Fin n)) :
    (toWord H).length = 1 + n + 2 * StpRam.offL H n := by
  rw [StpRam.toWord_graph_blocks, List.length_cons, StpRam.blocksFrom, Nat.sub_zero,
    ← List.range_eq_range', length_blocks, List.length_range, StpRam.offL]
  omega

/-- **The word of a partial graph is linear in its size.** -/
theorem length_toWord_pg_le (G : PartialGraph (Fin n)) : (toWord G).length ≤ 7 * (G.size + 1) := by
  rw [StpRam.toWord_pg, List.length_append, List.length_append, List.length_cons, List.length_ofFn,
    length_toWord_sgraph, length_toWord_sgraph]
  have h1 := StpRam.offL_add_le G
  have h2 : n ≤ G.size := le_size G
  omega

/-- The input of lem:resolve-lift is at most `(n + 1)²` times `M + 1`. -/
theorem xIn_len_le (k₀ q₀ : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) :
    (xIn G k₀ q₀ P Q s).length ≤ 11 * (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) := by
  have h1 := toWord_pgraph_le G
  have hD := Lax185574Proofs.DistMatrix.length_toWord_distMatrix G
  have h2 : (toWord (family G k₀ q₀)).length ≤ 1 + n * maxTreeSize G k₀ q₀ :=
    length_toWord_fun (family G k₀ q₀) (ℓ := maxTreeSize G k₀ q₀)
      (fun i => Finset.le_sup (f := fun a : Fin n => wordLength (family G k₀ q₀ a)) (Finset.mem_univ i))
  rw [Glue.toWord_xIn]
  simp only [List.length_append, List.length_cons, List.length_nil]
  have h4 : n * maxTreeSize G k₀ q₀ ≤ (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) := by
    have : n ≤ (n + 1) * (n + 1) := by nlinarith
    exact Nat.mul_le_mul this (by omega)
  have h5 : (n + 1) * (n + 1) ≤ (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have e : 11 * (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) =
      11 * ((n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1)) := by ring
  rw [e]
  nlinarith

/-- The input of lem:resolve-lift, as used by the time bounds. -/
theorem xIn_len_le' (k₀ q₀ : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) :
    (xIn G k₀ q₀ P Q s).length ≤ 11 * (n + 1) * (n + 1) * (maxTreeSize G k₀ q₀ + 1) :=
  xIn_len_le k₀ q₀ G P Q s

end Lax185574Proofs.ResolveRam
