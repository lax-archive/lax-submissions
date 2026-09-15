import Lax199508.WeakColoringBound
import Lax199508Proofs.OrderBridge
import Lax199508Proofs.OrderedParameterBounds

/-!
Lemma 2.6 of Chapter 2 of the notes, transported to the submitted
concepts: the weak coloring number is bounded by a power of the strong
coloring number.
-/

namespace Lax199508Proofs.WeakColoringBound

open Lax199508.ColoringNumbers
open Lax199508Proofs.OrderBridge

/--
---
conclusion: Lax199508.WeakColoringBound.wcol_le_of_scol
---
The weak `r`-coloring number of a graph is at most
`1 + r * (scol_r - 1) ^ r`, where `scol_r` is its strong `r`-coloring
number.

# Proof strategy

The internal development proves the inequality for a fixed linear order.
The submitted parameters are minima over vertex permutations, so it is
enough to run the internal bound under one well-chosen order: take a
permutation witnessing `scol G r` and order the vertices by their
positions under it.  Every vertex strongly reachable in the internal sense
is strongly reachable in the submitted sense — a path is a walk — so the
internal `scol` under that order is at most `scol G r`; and every vertex
weakly reachable in the submitted sense is weakly reachable in the internal
sense — a walk bypasses to a path with a smaller support — so the
submitted `wcol`, being the minimum over permutations, is at most the
internal one.  The right-hand side is monotone in the strong coloring
number, which closes the chain.

# Attribution

The statement is Lemma 2.6 of Chapter 2 of the sparsity lecture notes of
Pilipczuk and Siebertz (numbering of the 2019/20 edition).  The internal
per-order version is `Lax199508Proofs.OrderedParameterBounds.wcol_le_of_scol`.
-/
theorem wcol_le_of_scol {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    wcol G r ≤ 1 + r * (scol G r - 1) ^ r := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin n), ∀ v, (sreach G π r v).ncard ≤ scol G r :=
    Nat.sInf_mem (exists_scol_bound G r)
  letI := orderOfPerm π
  have h1 : Lax199508Proofs.OrderedParameters.scol G r ≤ scol G r :=
    catalog_scol_le π G r (scol G r) hπ
  have h2 : wcol G r ≤ Lax199508Proofs.OrderedParameters.wcol G r :=
    wcol_le_catalog (orderOfPerm π) G r
  have h3 : Lax199508Proofs.OrderedParameters.wcol G r ≤
      1 + r * (Lax199508Proofs.OrderedParameters.scol G r - 1) ^ r :=
    Lax199508Proofs.OrderedParameterBounds.wcol_le_of_scol G r
  have h4 : (Lax199508Proofs.OrderedParameters.scol G r - 1) ^ r ≤ (scol G r - 1) ^ r :=
    Nat.pow_le_pow_left (Nat.sub_le_sub_right h1 1) r
  have h5 : r * (Lax199508Proofs.OrderedParameters.scol G r - 1) ^ r ≤
      r * (scol G r - 1) ^ r := Nat.mul_le_mul_left r h4
  omega

end Lax199508Proofs.WeakColoringBound
