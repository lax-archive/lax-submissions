import Lax185574Proofs.ResolveRam.Core
import Lax185574Proofs.EncodingInjectivity
import Lax185574Proofs.Words.PrefixFree
import Lax185574.ToFarTree
import Lax185574Proofs.Interface.Shim.ToFarTree

/-!
A program determines its output: if one program computes `b` and `b'`
from the same input, then `b = b'`. Applied to the program of
lem:to-ftree, the far tree of a tuple is a function of its type tree,
since the scatter type does not depend on the tuple. This gives a far
tree map `farMapOf G` with `FarSpec G (farMapOf G)`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes Lax185574.FarTrees

/-- A word length at which `x` is admissible and the bound `N` fits. -/
theorem exists_admissible_fits (e c N : ℕ) (x : List ℕ) :
    ∃ w, WordAdmissible e c w x ∧ N ≤ 2 ^ w := by
  refine ⟨c * (x.length + x.sum + 1) ^ e + N, fun v hv => ?_, ?_⟩
  · have hv' : v ≤ x.sum := List.le_sum_of_mem hv
    have h1 : c * (x.length + v + 1) ^ e ≤ c * (x.length + x.sum + 1) ^ e :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have h2 := (Nat.lt_two_pow_self (n := c * (x.length + x.sum + 1) ^ e + N)).le
    omega
  · have h2 := (Nat.lt_two_pow_self (n := c * (x.length + x.sum + 1) ^ e + N)).le
    omega

/-- One program computes at most one output from an input. -/
theorem computes_word_eq {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c : ℕ} {a : α} {b b' : β} {T T' : ℕ → ℕ} (h : Computes p e c a b T)
    (h' : Computes p e c a b' T') : toWord b = toWord b' := by
  obtain ⟨w, hadm, hfit⟩ := exists_admissible_fits e c (T (wordLength a)) (toWord a)
  obtain ⟨t, -, hrun⟩ := (h w hadm).2 hfit (toWord a) rfl
  exact (h' w hadm).1 _ t hrun

variable {n : ℕ} (G : PartialGraph (Fin n))

/-- **The far tree is a function of the type tree**, by lem:to-ftree. -/
theorem ftree_congr {k q ℓ : ℕ} {u u' : Fin ℓ → Fin n} (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k)
    (h : node G k (q + 1) u = node G k (q + 1) u') :
    ftree G k (q + 1) u = ftree G k (q + 1) u' := by
  have := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
  obtain ⟨p, e, hp⟩ := Lax185574Proofs.Shim.ToFarTree.exists_program_ftree
  obtain ⟨c, a, hc⟩ := hp k q
  have hx := hc n G ℓ u h1 hk
  have hx' := hc n G ℓ u' h1 hk
  have ht : tree G k (q + 1) u = tree G k (q + 1) u' := by
    simp only [tree, h]
  rw [ht] at hx
  exact Lax185574Proofs.Words.toWord_injective (computes_word_eq hx hx')

open Classical in
/-- The far tree map of `G`: the far tree of any tuple with the given
tree. -/
noncomputable def farMapOf : FarMap := fun k q ℓ t _ =>
  if h : ∃ u : Fin ℓ → Fin n, 1 ≤ ℓ ∧ ℓ ≤ k ∧ node G k (q + 1) u = t then
    ftree G k (q + 1) h.choose
  else ∅

theorem farSpec_farMapOf : FarSpec G (farMapOf G) := by
  intro k q ℓ u h1 hk
  have hex : ∃ u' : Fin ℓ → Fin n, 1 ≤ ℓ ∧ ℓ ≤ k ∧ node G k (q + 1) u' = node G k (q + 1) u :=
    ⟨u, h1, hk, rfl⟩
  simp only [farMapOf, dif_pos hex]
  exact ftree_congr G h1 hk hex.choose_spec.2.2

end Lax185574Proofs.ResolveRam
