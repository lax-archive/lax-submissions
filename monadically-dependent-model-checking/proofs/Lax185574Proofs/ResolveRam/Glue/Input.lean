import Lax185574Proofs.ResolveRam.GlueSpec
import Lax185574Proofs.StpRam.FinalRead
import Lax185574Proofs.Lib.DistMatrix

/-!
The input of lem:resolve-lift and the query of the scatter type.

The input is the word of `G`, then the word of its distance matrix, `P`,
`Q`, the sign, and the family of the trees (`toWord_xIn`). The word of a
matrix of distances is `matWord` of the codes of its entries, of
length `1 + n (n + 1)` (`Lib/DistMatrix`). The family is `n`
followed by the words of the trees, and every tree starts with its rank,
so for `n ≥ 1` the entries `1` and `2` of the word of the family are
`k₀` and `q₀` (`family_rank`). The query of the scatter type is the word
of `G`, then `k₀`, `q₀`, the matrix and the family (`qF_stp`), so round
0 assembles it from pieces of its input. For `n = 0` the output is
`[0, 0, 0, 0, 0]` (`zOut_zero`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

theorem toWord_xIn (P Q : ℕ) (s : Bool) :
    xIn G k₀ q₀ P Q s = toWord G ++ toWord (distMatrix G) ++ [P, Q, if s then 1 else 0] ++
      toWord (family G k₀ q₀) := by
  simp only [xIn]
  change toWord G ++ (toWord (distMatrix G) ++ ([P] ++ ([Q] ++ (toWord s ++
    toWord (family G k₀ q₀))))) = _
  rw [Lax185574Proofs.Legacy.toWord_bool]
  simp

theorem toWord_family :
    toWord (family G k₀ q₀) = n :: (List.ofFn fun b => toWord (family G k₀ q₀ b)).flatten := by
  change (List.ofFn (family G k₀ q₀)).length :: ((List.ofFn (family G k₀ q₀)).map toWord).flatten = _
  rw [List.length_ofFn, List.map_ofFn]
  rfl

/-- **The rank in the word of the family.** -/
theorem family_rank (hn : 1 ≤ n) :
    (toWord (family G k₀ q₀)).getD 1 0 = k₀ ∧ (toWord (family G k₀ q₀)).getD 2 0 = q₀ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [toWord_family, List.ofFn_succ, List.flatten_cons]
  have : toWord (family G k₀ q₀ 0) = k₀ :: q₀ :: 1 :: toWord (family G k₀ q₀ 0).root := rfl
  rw [this]
  exact ⟨rfl, rfl⟩

/-- **The query of the scatter type.** -/
theorem qF_stp : qF G k₀ q₀ .stp =
    toWord G ++ [k₀, q₀] ++ toWord (distMatrix G) ++ toWord (family G k₀ q₀) := by
  simp only [qF]
  change toWord G ++ ([k₀] ++ ([q₀] ++ (toWord (distMatrix G) ++ toWord (family G k₀ q₀)))) = _
  simp

/-- **The output for the empty graph.** -/
theorem zOut_zero (G : PartialGraph (Fin 0)) (P Q : ℕ) (s : Bool) :
    zOut G k₀ q₀ P Q s = [0, 0, 0, 0, 0] := by
  simp only [zOut]
  change toWord (resolveBy G s P Q) ++ (toWord (distMatrix (resolveBy G s P Q)) ++
    toWord (family (resolveBy G s P Q) k₀ q₀)) = _
  rw [StpRam.toWord_pg, toWord_family, toWord_distMatrix]
  have e1 : toWord (resolveBy G s P Q).edge = [0] := rfl
  have e2 : toWord (resolveBy G s P Q).nonEdge = [0] := rfl
  rw [e1, e2]
  simp [matWord]

end Lax185574Proofs.ResolveRam.Glue
