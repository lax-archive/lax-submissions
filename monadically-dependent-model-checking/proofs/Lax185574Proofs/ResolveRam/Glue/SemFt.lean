import Lax185574Proofs.ResolveRam.Glue.SemDn
import Lax185574Proofs.ResolveRam.CountT

/-!
The trees of the items and of the answers of their rank shifts.

An item of level `d` carries the tree of a `(d + 1)`-tuple at rank
`(k₀ + d, q₀ - d)` (`itm_tree`), so the answer of its rank shift is the
tree at rank `(k₀ + d + 1, q₀ - d - 1)` (`sh_itm`), whose radius bound is
at most the radius bound `rhoPlus (k₀ + 1) q₀` of the round (`rho_sh`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.Words
open Lax3.DistFO (rhoPlus)

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

theorem itm_tree (hk : 1 ≤ k₀) {d i : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    ∃ w : Fin (d + 1) → Fin n, (itm G P Q s k₀ q₀ d i).2 = tree G (k₀ + d) (q₀ - d) w := by
  obtain ⟨w, -, hw⟩ := lvR_goodH G P Q s k₀ q₀ hk d hd _ (List.getElem_mem hi)
  exact ⟨w, by rw [itm_eq G P Q s k₀ q₀ hi]; exact hw⟩

theorem sh_itm (hk : 1 ≤ k₀) {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    ∃ w : Fin (d + 1) → Fin n, shOf G (itm G P Q s k₀ q₀ d i).2 = tree G (k₀ + d + 1) (q₀ - d - 1) w := by
  obtain ⟨w, hw⟩ := itm_tree G P Q s k₀ q₀ hk hd.le hi
  refine ⟨w, ?_⟩
  obtain ⟨e, he⟩ : ∃ e, q₀ - d = e + 1 := ⟨q₀ - d - 1, by omega⟩
  rw [hw, he, shOf_tree G w (by omega) (by omega), Nat.add_sub_cancel]

theorem rho_sh {d : ℕ} (hd : d < q₀) : rhoPlus (k₀ + d + 1) (q₀ - d - 1) ≤ rhoPlus (k₀ + 1) q₀ := by
  unfold rhoPlus
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul (by omega) (by omega))

end Lax185574Proofs.ResolveRam.Glue
