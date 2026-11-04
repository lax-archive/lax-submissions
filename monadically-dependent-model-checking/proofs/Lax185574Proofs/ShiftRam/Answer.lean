import Lax185574Proofs.Restriction
import Lax185574Proofs.TreeAlgo.RankShift

/-!
The query and the answer of the rank shift.

The tree `tree_{k,q+1}(u)` of a nonempty tuple has an extension with
guard `0`. Its child is `tree_{k+1,q}(u b)` for a vertex `b`, and its
restriction to the first `ℓ` positions is `tree_{k+1,q}(u)`, as in the
proof of lem:shift. The word of the answer is not longer than the word of
the child plus three, and its entries are entries of the child, positions
below `ℓ`, or the header.
-/

namespace Lax185574Proofs.ShiftRam

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574Proofs.RestrictionRam
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

theorem exists_guard_zero (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (u : Fin ℓ → Fin n) : ∃ a ∈ Node.exts (node G k (q + 1) u), a.1.val = 0 :=
  ⟨(⟨0, hℓ⟩, node G (k + 1) q (Fin.snoc u (u ⟨0, hℓ⟩))),
    (mem_exts_node G k q u _).2 ⟨⟨0, hℓ⟩, u ⟨0, hℓ⟩, ⟨.nil, Nat.zero_le _⟩, rfl⟩, rfl⟩

theorem child_eq (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n)
    {a : Fin ℓ × Node q (ℓ + 1)} (ha : a ∈ Node.exts (node G k (q + 1) u)) :
    ∃ b, a.2 = node G (k + 1) q (Fin.snoc u b) := by
  obtain ⟨i, b, -, rfl⟩ := (mem_exts_node G k q u a).1 ha
  exact ⟨b, rfl⟩

/-- The first `ℓ` positions of a tuple of length `ℓ + 1`. -/
def initJ (ℓ : ℕ) : List (Fin (ℓ + 1)) := (List.finRange ℓ).map Fin.castSucc

theorem initJ_length (ℓ : ℕ) : (initJ ℓ).length = ℓ := by simp [initJ]

theorem initJ_nodup (ℓ : ℕ) : (initJ ℓ).Nodup :=
  (List.nodup_finRange ℓ).map (Fin.castSucc_injective ℓ)

theorem toWord_initJ (ℓ : ℕ) : toWord (initJ ℓ) = ℓ :: List.range ℓ := by
  rw [toWord_listFin, initJ_length]
  congr 1
  apply List.ext_getElem (by simp [initJ])
  intro i h1 h2
  simp [initJ]

theorem tree_cast {V : Type*} [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ m : ℕ} (hm : m = ℓ)
    (f : Fin m → V) (u : Fin ℓ → V) (hf : ∀ i, f i = u (Fin.cast hm i)) :
    tree G k q f = tree G k q u := by
  subst hm
  congr 1
  funext i
  exact hf i

theorem restrict_answer (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (b : Fin n) :
    tree G k q (fun i => (Fin.snoc u b : Fin (ℓ + 1) → Fin n) ((initJ ℓ).get i)) = tree G k q u :=
  tree_cast G k q (initJ_length ℓ) _ u fun i => by
    obtain ⟨j, hj⟩ := i
    have hj' : j < ℓ := by rw [initJ_length] at hj; exact hj
    have this : (initJ ℓ).get ⟨j, hj⟩ = Fin.castSucc (Fin.cast (initJ_length ℓ) ⟨j, hj⟩) := by
      apply Fin.ext
      simp [initJ]; rfl
    rw [this, Fin.snoc_castSucc]

/-- The word of the query. -/
theorem toWord_query (T : TypeTree) (ℓ : ℕ) :
    toWord (T, initJ ℓ) = [T.k, T.q, T.ℓ] ++ toWord T.root ++ (ℓ :: List.range ℓ) := by
  rw [toWord_tree_pair, toWord_initJ]

/-- **The size of the answer.** -/
theorem answer_bound (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (b : Fin n)
    (Bz : ℕ) (hc : ∀ v ∈ toWord (node G k q (Fin.snoc u b)), v < Bz)
    (hl : (toWord (node G k q (Fin.snoc u b))).length < Bz) (hℓ : ℓ + 1 < Bz) (hk : k < Bz)
    (hq : q < Bz) :
    (toWord (tree G k q u)).length ≤ (toWord (node G k q (Fin.snoc u b))).length + 3 ∧
      ∀ v ∈ toWord (tree G k q u), v < Bz := by
  set μ := node G k q (Fin.snoc u b) with hμ
  have hz : tree G k q u = restrictTree k q (ℓ + 1) μ (initJ ℓ) := by
    rw [restrictTree_tree G k q _ _ (initJ_nodup ℓ), restrict_answer]
  have hw : toWord (tree G k q u) = [k, q, (initJ ℓ).length] ++
      treeOut (rsub (initJ ℓ)) (rgsub (initJ ℓ)) q 0 (toWord μ) 0 := by
    rw [hz, treeOut_restrict (initJ ℓ) (toWord μ) q 0 μ 0 [] (by simp)]
    rfl
  have hJ := initJ_length ℓ
  rw [hw]
  refine ⟨?_, ?_⟩
  · have := length_treeOut_le (rsub (initJ ℓ)) (rgsub (initJ ℓ)) q 0 (ℓ + 1) (toWord μ) 0 μ []
      (by simp)
    simp; omega
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · simp at h; rcases h with rfl | rfl | rfl <;> omega
    · refine treeOut_lt _ _ (toWord μ) hc hl q 0 (ℓ + 1) 0 μ [] (by simp) ?_ ?_ ?_ v h
      · intro tg k' v' r hv' hr
        rcases rsub_le (initJ ℓ) (by omega) hr with h' | h'
        · have := hc v' hv'; omega
        · omega
      · intro dd _ _ tg k' v' r hv' hr
        rcases rsub_le (initJ ℓ) (by omega) hr with h' | h'
        · have := hc v' hv'; omega
        · omega
      · intro dd i r _ _ hi hr
        rcases gmap_le (initJ ℓ) (by omega) hr with h' | h'
        · have := hc i hi; omega
        · omega

end Lax185574Proofs.ShiftRam
