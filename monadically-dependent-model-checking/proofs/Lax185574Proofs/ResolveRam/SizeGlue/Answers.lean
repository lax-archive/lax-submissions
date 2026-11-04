import Lax185574Proofs.ResolveRam.SizeGlue.Calls

/-!
Answers of the calls of lem:resolve-lift whose size does not grow with `n`.

Let `x` be an item of a level `d < q₀`, the tree of a tuple `u` at the
rank `(k₀ + d, q₀ − d)`. Its rank shift is the tree of `u` one rank
lower, no longer than the time bound of the shift on `x` (`shift_ans_le`).
Every member of the far tree of `x`, filtered or not, is the tree of a
single far vertex (`faOf_tree`), so `single_le_all` bounds it
(`faOf_mem_le`). The composition of the shifted item with such a member
is the tree of `u` extended by the vertex, no longer than the time bound
of the composition (`compose_ans_le`). The bounds are a constant times
`(M + 1)^A`. The outputs of a level are the lifts of its items
(`outR_eq_lift`), each at most `kidB T` (`outW_mem_le`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574Proofs.TypeTreeSizes Lax185574Proofs.MC
open Lax3.DistFO (rhoMinus rhoPlus)

variable {k₀ q₀ : ℕ}

/-- The members of the unfiltered far tree of an item are trees of far
vertices. -/
theorem faOf_tree {n : ℕ} (G : PartialGraph (Fin n)) {d : ℕ} (hd : d < q₀) {ℓ : ℕ}
    {u : Fin ℓ → Fin n} (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k₀ + d) {ν : TypeTree}
    (hν : ν ∈ faOf G (tree G (k₀ + d) (q₀ - d - 1 + 1) u)) :
    ∃ b, (∀ i, ¬ WithinDist G.resolved (rhoMinus (k₀ + d + 1) (q₀ - d - 1)) (u i) b) ∧
      ν = tree G (k₀ + d + 1) (q₀ - d - 1) ![b] := by
  have hfa := (ansOK_of G k₀ q₀).fa (k₀ + d) (q₀ - d - 1) ℓ u h1 hk (by omega) (by omega) ν
  exact (mem_ftree (G := G) (k₀ + d) (q₀ - d - 1) u ν).1 (hfa.1 hν)

/-- **The rank shift of an item.** -/
theorem shift_ans_le (hk : 1 ≤ k₀) : ∃ c a : ℕ, ∀ d < q₀, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), ∀ x ∈ lvR G P Q s k₀ q₀ d,
      wordLength x.2 + wordLength (shOf G x.2) ≤ c * (maxTreeSize G k₀ q₀ + 1) ^ a := by
  obtain ⟨c0, a0, hI⟩ := item_le_all k₀ q₀ hk
  refine ⟨c0 + cU k₀ q₀ * (c0 + 1) ^ aU k₀ q₀, a0 + a0 * aU k₀ q₀,
    fun d hd n G P Q s x hx => ?_⟩
  obtain ⟨hcS, -, -, haS, -, -⟩ := le_cU (k₀ := k₀) hd
  obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd.le hx
  have hτ := hI d hd.le n G P Q s x hx
  set m := q₀ - d - 1
  rw [show q₀ - d = m + 1 by omega] at hu
  rw [hu] at hτ ⊢
  rw [shOf_tree G u h1 hℓ]
  have tS := wordLength_le_time' (hSh' (k₀ + d) m n G ℓ u h1 hℓ)
  have h2 := le_trans tS (le_trans (cpow_le hcS haS) (pc_comp hτ))
  exact pc_add hτ h2

/-- **The members of the far tree of an item.** -/
theorem faOf_mem_le (hk : 1 ≤ k₀) : ∃ c a : ℕ, ∀ d < q₀, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), ∀ x ∈ lvR G P Q s k₀ q₀ d, ∀ ν ∈ faOf G x.2,
      wordLength ν ≤ c * (maxTreeSize G k₀ q₀ + 1) ^ a := by
  obtain ⟨c1, a1, hV⟩ := single_le_all k₀ q₀ hk
  refine ⟨c1, a1, fun d hd n G P Q s x hx ν hν => ?_⟩
  obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd.le hx
  rw [show q₀ - d = q₀ - d - 1 + 1 by omega] at hu
  rw [hu] at hν
  obtain ⟨b, -, rfl⟩ := faOf_tree G hd h1 hℓ hν
  have := hV (d + 1) hd n G b
  rwa [show k₀ + (d + 1) = k₀ + d + 1 by omega, show q₀ - (d + 1) = q₀ - d - 1 by omega] at this

/-- **The compositions of an item.** The composition of the shifted item
with a member of its far tree, and the query of the composition. -/
theorem compose_ans_le (hk : 1 ≤ k₀) : ∃ c a : ℕ, ∀ d < q₀, ∀ (n : ℕ) (G : PartialGraph (Fin n))
    (P Q : ℕ) (s : Bool), ∀ x ∈ lvR G P Q s k₀ q₀ d, ∀ ν ∈ faOf G x.2,
      wordLength (shOf G x.2, ν) + wordLength (coOf G (shOf G x.2) ν) ≤
        c * (maxTreeSize G k₀ q₀ + 1) ^ a := by
  obtain ⟨cs, as, hS⟩ := shift_ans_le (q₀ := q₀) hk
  obtain ⟨c1, a1, hV⟩ := faOf_mem_le (q₀ := q₀) hk
  set cq := cs + c1
  set aq := as + a1
  set cco := cU k₀ q₀ * (cq + 1) ^ aU k₀ q₀
  set aco := aq * aU k₀ q₀
  refine ⟨cq + cco, aq + aco, fun d hd n G P Q s x hx ν hν => ?_⟩
  obtain ⟨-, -, hcC, -, -, haC⟩ := le_cU (k₀ := k₀) hd
  have hq : wordLength (shOf G x.2, ν) ≤ cq * (maxTreeSize G k₀ q₀ + 1) ^ aq := by
    rw [wordLength_prod]
    have h1 := hS d hd n G P Q s x hx
    have h2 := hV d hd n G P Q s x hx ν hν
    exact pc_add (by omega) h2
  refine pc_add hq ?_
  obtain ⟨ℓ, u, hu, h1, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk hd.le hx
  set m := q₀ - d - 1
  rw [show q₀ - d = m + 1 by omega] at hu
  rw [hu] at hν hq ⊢
  obtain ⟨b, hb, rfl⟩ := faOf_tree G hd h1 hℓ hν
  rw [shOf_tree G u h1 hℓ] at hq ⊢
  rw [coOf_tree G u b h1 hℓ hb]
  have tC := wordLength_le_time' (hCo' (k₀ + d + 1) m n G ℓ 1 u ![b] h1 le_rfl (by omega)
    (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb i))
  rw [Fin.append_right_eq_snoc] at tC
  exact le_trans tC (le_trans (cpow_le hcC haC) (pc_comp hq))

/-! ### The outputs -/

/-- **The outputs of a level are the lifts of its items.** -/
theorem outR_eq_lift {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (hk : 1 ≤ k₀)
    {d : ℕ} (hd : d ≤ q₀) :
    outR G P Q s k₀ q₀ (q₀ - d) d =
      (lvR G P Q s k₀ q₀ d).map fun x => liftT (dataOf G P Q s k₀ q₀) (farMapOf G) x.2 := by
  refine outsAt_eq _ (farMapOf G) (dataOf_spec G P Q s k₀ q₀) (farSpec_farMapOf G)
    (expandOK_exR G P Q s k₀ q₀) ?_ _ _ (by omega)
  intro x hx
  simp only [famItems, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  exact ⟨1, ![b], by simp [family], le_rfl, hk⟩

/-- **The outputs of the items.** -/
theorem outR_mem_le {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (hk : 1 ≤ k₀)
    {d : ℕ} (hd : d ≤ q₀) :
    ∀ τ ∈ outR G P Q s k₀ q₀ (q₀ - d) d,
      wordLength τ ≤ kidB k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  intro τ hτ
  rw [outR_eq_lift G P Q s hk hd] at hτ
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hτ
  exact lift_le G P Q s k₀ q₀ hk hd hx

end Lax185574Proofs.ResolveRam
