import Lax185574Proofs.TreeAlgo.ToFarTree
import Lax185574Proofs.Legacy
import Mathlib.Order.Interval.Finset.Nat

/-!
The semantic core of lem:compute-stp. The partial graph enters through
the lists of resolved neighbors of its vertices, as read off its encoding.
Balls are computed by `ballFrom`, which adds the neighbors of the current
set `r` times, the breadth-first search of the proof. The domain is
obtained by `i` rank shifts of the tree of every vertex, for `1 ≤ i ≤ q`,
with the radii `1, …, 9^(k+i) ρ⁻(k+i, q−i)`. The value at `(r, ν)` is the
length of the greedy scan, which tests membership in `[ν]` by comparing
the shifted trees with `ν` and marks the ball of radius `r` of every
chosen vertex, capped at `k + q`.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.PartialGraphEncoding
open Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ}

/-- The vertices within distance `s` of `u`, given the lists of
neighbors. -/
def ballFrom (adj : Fin n → List (Fin n)) (u : Fin n) : ℕ → Finset (Fin n)
  | 0 => {u}
  | s + 1 => ballFrom adj u s ∪ (ballFrom adj u s).biUnion fun w => (adj w).toFinset

/-- The greedy scan for `S_r([ν])`, with the shifted trees `shifted v` of
the vertices. -/
def greedyCore (adj : Fin n → List (Fin n)) (shifted : Fin n → TypeTree) (r : ℕ)
    (ν : TypeTree) : List (Fin n) :=
  (List.finRange n).foldl
    (fun S v => if shifted v = ν ∧ ∀ u ∈ S, v ∉ ballFrom adj u r then S ++ [v] else S) []

/-- The domain of the scatter type, computed from the family. -/
def domainCore (fam : Fin n → TypeTree) (k q : ℕ) : Finset (ℕ × TypeTree) :=
  (Finset.range q).biUnion fun i' =>
    Finset.univ.biUnion fun b : Fin n =>
      (Finset.Icc 1 (9 ^ (k + (i' + 1)) * rhoMinus (k + (i' + 1)) (q - (i' + 1)))).image
        fun r => (r, shiftTree^[i' + 1] (fam b))

/-- The scatter type, computed from the neighbor lists and the family. -/
def stpCore (adj : Fin n → List (Fin n)) (fam : Fin n → TypeTree) (k q : ℕ) :
    Finset ((ℕ × TypeTree) × ℕ) :=
  (domainCore fam k q).image fun d =>
    (d, min (greedyCore adj (fun v => shiftTree^[d.2.k - k] (fam v)) d.1 d.2).length (k + q))

/-! ### Correctness -/

variable {G : PartialGraph (Fin n)}

/-- A walk of length at most `s + 1` ends with a step from a vertex within
distance `s`. -/
theorem withinDist_succ_iff' {W : Type*} {H : SimpleGraph W} {s : ℕ} {u v : W} :
    WithinDist H (s + 1) u v ↔ WithinDist H s u v ∨ ∃ w, WithinDist H s u w ∧ H.Adj w v := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := withinDist_symm h
    cases p with
    | nil => exact Or.inl (withinDist_refl _ _ _)
    | cons hvw p' =>
      simp only [SimpleGraph.Walk.length_cons] at hp
      exact Or.inr ⟨_, withinDist_symm ⟨p', by omega⟩, hvw.symm⟩
  · rintro (h | ⟨w, ⟨p, hp⟩, hw⟩)
    · exact withinDist_mono (Nat.le_succ s) h
    · exact ⟨p.concat hw, by simp; omega⟩

theorem mem_ballFrom {adj : Fin n → List (Fin n)} (hadj : ∀ u v, v ∈ adj u ↔ G.resolved.Adj u v)
    (u : Fin n) : ∀ s v, v ∈ ballFrom adj u s ↔ WithinDist G.resolved s u v
  | 0, v => by
    simp only [ballFrom, Finset.mem_singleton, withinDist_zero]
    exact eq_comm
  | s + 1, v => by
    simp only [ballFrom, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, hadj,
      mem_ballFrom hadj u s, withinDist_succ_iff']

theorem greedyCore_eq {adj : Fin n → List (Fin n)} (hadj : ∀ u v, v ∈ adj u ↔ G.resolved.Adj u v)
    (shifted : Fin n → TypeTree) (r : ℕ) (ν : TypeTree)
    (hX : ∀ v, shifted v = ν ↔ v ∈ realizations G ν) :
    greedyCore adj shifted r ν = greedyScattered G r (realizations G ν) := by
  unfold greedyCore greedyScattered
  congr 1
  funext S v
  have : (shifted v = ν ∧ ∀ u ∈ S, v ∉ ballFrom adj u r) ↔
      (v ∈ realizations G ν ∧ ∀ u ∈ S, ¬ WithinDist G.resolved r u v) := by
    simp only [hX, mem_ballFrom hadj]
  by_cases h : shifted v = ν ∧ ∀ u ∈ S, v ∉ ballFrom adj u r
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]

theorem shift_family (k q : ℕ) (b : Fin n) {i : ℕ} (hi : i ≤ q) :
    shiftTree^[i] (family G k q b) = tree G (k + i) (q - i) ![b] :=
  shiftTree_iterate_tree G le_rfl ![b] i k q hi

theorem mem_domainCore (k q : ℕ) (d : ℕ × TypeTree) :
    d ∈ domainCore (family G k q) k q ↔ d ∈ domain G k q := by
  simp only [domainCore, Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨i', hi', b, r, ⟨hr1, hr2⟩, rfl⟩
    refine ⟨i' + 1, b, by omega, by omega, hr1, hr2, ?_⟩
    exact shift_family k q b (by omega)
  · rintro ⟨i, b, hi1, hiq, hr1, hr2, hd⟩
    refine ⟨i - 1, by omega, b, d.1, ⟨hr1, by rwa [show i - 1 + 1 = i by omega]⟩, ?_⟩
    rw [show i - 1 + 1 = i by omega, shift_family k q b hiq, ← hd]

/-- **lem:compute-stp, semantic form.** Given the neighbor lists of the
resolved pairs and the family of type trees, `stpCore` is the scatter
type. -/
theorem stpCore_eq {adj : Fin n → List (Fin n)} (hadj : ∀ u v, v ∈ adj u ↔ G.resolved.Adj u v)
    (k q : ℕ) : stpCore adj (family G k q) k q = stp G k q := by
  ext ⟨d, m⟩
  rw [mem_stp, stpCore, Finset.mem_image]
  constructor
  · rintro ⟨d', hd', he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨(mem_domainCore k q d').1 hd', ?_⟩
    obtain ⟨i, b, hi1, hiq, -, -, hν⟩ := (mem_domainCore k q d').1 hd'
    simp only [value]
    congr 2
    refine greedyCore_eq hadj _ _ _ fun v => ?_
    rw [hν]
    simp only [tree, realizations, Set.mem_ofPred_eq, show k + i - k = i by omega,
      shift_family k q v hiq]
  · rintro ⟨hd, hm⟩
    refine ⟨d, (mem_domainCore k q d).2 hd, ?_⟩
    simp only at hm
    rw [hm]
    obtain ⟨i, b, hi1, hiq, -, -, hν⟩ := hd
    simp only [value, Prod.mk.injEq, true_and]
    congr 2
    refine greedyCore_eq hadj _ _ _ fun v => ?_
    rw [hν]
    simp only [tree, realizations, Set.mem_ofPred_eq, show k + i - k = i by omega,
      shift_family k q v hiq]

/-! ### Size -/

/-- The domain has at most `q · n · R` entries, where `R` bounds the radii.
So `|D_{k,q}| = O_{k,q}(n)`, and the scan runs once per entry. -/
theorem card_domainCore_le (fam : Fin n → TypeTree) (k q : ℕ) :
    (domainCore fam k q).card ≤ q * (n * (9 ^ (k + q) * rhoMinus (k + q) q)) := by
  unfold domainCore
  refine Finset.card_biUnion_le.trans ?_
  have hR : ∀ i' ∈ Finset.range q, 9 ^ (k + (i' + 1)) * rhoMinus (k + (i' + 1)) (q - (i' + 1)) ≤
      9 ^ (k + q) * rhoMinus (k + q) q := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    refine Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) ?_
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (by omega) (by omega))
  calc ∑ i' ∈ Finset.range q, (Finset.univ.biUnion fun b : Fin n =>
        (Finset.Icc 1 (9 ^ (k + (i' + 1)) * rhoMinus (k + (i' + 1)) (q - (i' + 1)))).image
          fun r => (r, shiftTree^[i' + 1] (fam b))).card
      ≤ ∑ _i' ∈ Finset.range q, n * (9 ^ (k + q) * rhoMinus (k + q) q) := by
        refine Finset.sum_le_sum fun i' hi' => Finset.card_biUnion_le.trans ?_
        calc _ ≤ ∑ _b : Fin n, 9 ^ (k + q) * rhoMinus (k + q) q :=
              Finset.sum_le_sum fun b _ => Finset.card_image_le.trans (by
                rw [Nat.card_Icc]; have := hR i' hi'; omega)
          _ = _ := by simp
    _ = _ := by simp

end Lax185574Proofs.TreeAlgo
