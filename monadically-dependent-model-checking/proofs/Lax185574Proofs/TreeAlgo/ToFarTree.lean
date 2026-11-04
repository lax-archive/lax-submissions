import Lax185574Proofs.TreeAlgo.RankShift
import Lax185574Proofs.TreeAlgo.Greedy
import Lax185574.ToFarTree
import Lax185574.Clustering

/-!
The semantic core of lem:to-ftree. From the tree `τ = tree_{k,q+1}(ā)` and
the scatter type `σ = stp_{k,q+1}`, with `r = ρ⁻(k+1, q)` and
`H = ρ⁺(k+1, q)`:

* a radius `ρ` and a partition `β` that are admissible in the sense of
  lem:clustering are found by trying `ρ = r, r+1, …, 9^(ℓ−1) r` with the
  canonical partition of the test `dist(aᵢ, aⱼ) ≤ 4ρ − 2r`, all tests being
  binary distance atoms of the root of `τ`;
* `𝓝` collects the trees `μ ↾ (ℓ+1)` of the extensions `(i, μ)` of `τ`
  whose root has no atom `dist(xⱼ, x_{ℓ+1}) ≤ r`;
* for a candidate `ν`, the blocks met by `ν` are the blocks of the
  positions `j` such that some extension `(i, μ)` with `μ ↾ (ℓ+1) = ν` has
  the atom `dist(xⱼ, x_{ℓ+1}) ≤ r` in its root;
* the far tree consists of the trees `ν` of the entries `((4ρ, ν), m)` of
  `σ` of rank `(k+1, q)` with `ν ∈ 𝓝` or fewer blocks met than `m`.

The correctness proof follows the proof of lem:to-ftree and applies the
concept `Lax185574.Clustering.clustering` to `X = [ν]` and the greedy
scattered set `S_{4ρ}([ν])`.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.Clustering
open Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The test `dist(xᵢ, xⱼ) ≤ s`, read off the root label. -/
def distTest {q ℓ : ℕ} (t : Node q ℓ) (s : ℕ) (i j : Fin ℓ) : Bool :=
  decide (DistFO.distLe s i j ∈ Node.atoms t)

/-- The canonical block of a position: the first position that passes the
test `dist(xᵢ, xⱼ) ≤ s`. -/
def canonBlock {q ℓ : ℕ} (t : Node q ℓ) (s : ℕ) (i : Fin ℓ) : Fin ℓ :=
  ((List.finRange ℓ).find? (fun j => distTest t s i j)).getD i

/-- The admissibility of `ρ` and `β` at radius `r`, read off the root
label. -/
def admissibleB {q ℓ : ℕ} (t : Node q ℓ) (r ρ : ℕ) (β : Fin ℓ → Fin ℓ) : Bool :=
  decide (∀ i j, (β i = β j → distTest t (4 * ρ - 2 * r) i j = true) ∧
    (β i ≠ β j → distTest t (4 * ρ + 2 * r) i j = false))

/-- The first admissible radius between `r` and `9^(ℓ−1) r`, with the
canonical partition. -/
def findRadius {q ℓ : ℕ} (t : Node q ℓ) (r : ℕ) : ℕ :=
  ((List.range' r (9 ^ (ℓ - 1) * r - r + 1)).find?
    (fun ρ => admissibleB t r ρ (canonBlock t (4 * ρ - 2 * r)))).getD r

/-- The partial inverse of the map sending the only position to the last. -/
def lastPInv (ℓ : ℕ) : Fin (ℓ + 1) → Option (Fin 1) := Fin.lastCases (some 0) fun _ => none

theorem isPInv_lastPInv (ℓ : ℕ) : IsPInv (fun _ : Fin 1 => Fin.last ℓ) (lastPInv ℓ) := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [lastPInv, Fin.fin_one_eq_zero j]
  · simp [lastPInv, (Fin.castSucc_ne_last i).symm]

/-- The tree `μ ↾ (ℓ+1)` of the new vertex of an extension. -/
def lastTree (k q ℓ : ℕ) (μ : Node q (ℓ + 1)) : TypeTree :=
  ⟨k + 1, q, 1, restrictNode (lastPInv ℓ) μ⟩

/-- The new vertex of an extension is far from all old positions. -/
def isFarExt {q ℓ : ℕ} (r : ℕ) (μ : Node q (ℓ + 1)) : Bool :=
  decide (∀ j : Fin ℓ, DistFO.distLe r j.castSucc (Fin.last ℓ) ∉ Node.atoms μ)

/-- `𝓝`: the trees of the vertices at distance more than `r` from the
tuple and at most `H` from some entry. -/
def nearFarSet (k q ℓ r : ℕ) (t : Node (q + 1) ℓ) : Finset TypeTree :=
  ((Node.exts t).filter fun e => isFarExt r e.2).image fun e => lastTree k q ℓ e.2

/-- The positions within distance `r` of a vertex with tree `ν`. -/
def metPositions (k q ℓ r : ℕ) (t : Node (q + 1) ℓ) (ν : TypeTree) : Finset (Fin ℓ) :=
  ((Node.exts t).filter fun e => lastTree k q ℓ e.2 = ν).biUnion fun e =>
    Finset.univ.filter fun i => DistFO.distLe r i.castSucc (Fin.last ℓ) ∈ Node.atoms e.2

/-- The far tree computed from a tree of rank `(k, q+1)` and arity `ℓ` and
a scatter type. -/
def farTreeNode (k q ℓ : ℕ) (t : Node (q + 1) ℓ) (σ : Finset ((ℕ × TypeTree) × ℕ)) :
    Finset TypeTree :=
  let r := rhoMinus (k + 1) q
  let ρ := findRadius t r
  let β := canonBlock t (4 * ρ - 2 * r)
  (σ.filter fun p => p.1.1 = 4 * ρ ∧ p.1.2.k = k + 1 ∧ p.1.2.q = q ∧
      (p.1.2 ∈ nearFarSet k q ℓ r t ∨ ((metPositions k q ℓ r t p.1.2).image β).card < p.2)).image
    fun p => p.1.2

/-- The core of lem:to-ftree on type trees. -/
def farTree (τ : TypeTree) (σ : Finset ((ℕ × TypeTree) × ℕ)) : Finset TypeTree :=
  match τ with
  | ⟨k, q + 1, ℓ, t⟩ => farTreeNode k q ℓ t σ
  | _ => ∅

/-! ### Correctness -/

section Correctness

variable {n : ℕ} (G : PartialGraph (Fin n))

theorem rhoPlus_eq (k q : ℕ) : rhoPlus k q = 9 ^ k * rhoMinus k q := by
  rw [Lax3.DistFO.rhoPlus, Lax3.DistFO.rhoMinus, ← pow_add]
  congr 1
  ring

theorem one_le_rhoMinus (k q : ℕ) : 1 ≤ rhoMinus k q := Nat.one_le_pow _ _ (by norm_num)

/-- The radius bounds of the proof of lem:to-ftree. -/
theorem radius_bounds {k q ℓ ρ : ℕ} (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k)
    (hρ : ρ ≤ 9 ^ (ℓ - 1) * rhoMinus (k + 1) q) :
    4 * ρ + 2 * rhoMinus (k + 1) q ≤ rhoMinus k (q + 1) ∧
      4 * ρ + rhoMinus (k + 1) q ≤ rhoPlus (k + 1) q ∧
      4 * ρ ≤ 9 ^ (k + 1) * rhoMinus (k + 1) q := by
  set r := rhoMinus (k + 1) q
  have hP : rhoPlus (k + 1) q = 9 ^ (k + 1) * r := rhoPlus_eq _ _
  have hM : rhoPlus (k + 1) q ≤ rhoMinus k (q + 1) :=
    le_trans (by omega) (two_mul_rhoPlus_le_rhoMinus k q)
  have h9 : 6 * 9 ^ (ℓ - 1) ≤ 9 ^ (k + 1) := by
    calc 6 * 9 ^ (ℓ - 1) ≤ 9 * 9 ^ (ℓ - 1) := by omega
      _ = 9 ^ (ℓ - 1 + 1) := by ring
      _ ≤ 9 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hr := one_le_rhoMinus (k + 1) q
  have : 4 * ρ + 2 * r ≤ 9 ^ (k + 1) * r := by
    have h6 : 6 * 9 ^ (ℓ - 1) * r ≤ 9 ^ (k + 1) * r := Nat.mul_le_mul_right _ h9
    have : 1 ≤ 9 ^ (ℓ - 1) := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  refine ⟨by omega, by omega, by omega⟩

variable {G}

theorem distTest_node {k q ℓ s : ℕ} (u : Fin ℓ → Fin n) (hs : s ≤ rhoMinus k q) (i j : Fin ℓ) :
    distTest (node G k q u) s i j = true ↔ WithinDist G.resolved s (u i) (u j) := by
  rw [distTest, decide_eq_true_iff, mem_atoms_node]
  exact ⟨fun h => h.2.2, fun h => ⟨trivial, .distLe _ _ _ hs, h⟩⟩

/-- On a tree, admissibility read off the root label is admissibility. -/
theorem admissibleB_node {k q ℓ ρ : ℕ} (u : Fin ℓ → Fin n) (r : ℕ)
    (hs : 4 * ρ + 2 * r ≤ rhoMinus k q) (β : Fin ℓ → Fin ℓ) :
    admissibleB (node G k q u) r ρ β = true ↔ Admissible G.resolved r u ρ β := by
  have h1 := fun i j => distTest_node (G := G) (k := k) (q := q) u (s := 4 * ρ - 2 * r)
    (by omega) i j
  have h2 := fun i j => distTest_node (G := G) (k := k) (q := q) u (s := 4 * ρ + 2 * r) hs i j
  simp only [admissibleB, decide_eq_true_iff, Admissible]
  refine forall_congr' fun i => forall_congr' fun j =>
    and_congr (imp_congr Iff.rfl (h1 i j)) (imp_congr Iff.rfl ?_)
  rw [← h2 i j, Bool.not_eq_true]

/-- The canonical partition of an admissible radius is admissible. -/
theorem admissible_canonBlock {k q ℓ ρ : ℕ} (u : Fin ℓ → Fin n) (r : ℕ)
    (hs : 4 * ρ + 2 * r ≤ rhoMinus k q) {β : Fin ℓ → Fin ℓ}
    (hβ : Admissible G.resolved r u ρ β) :
    Admissible G.resolved r u ρ (canonBlock (node G k q u) (4 * ρ - 2 * r)) := by
  set t := node G k q u
  have htest : ∀ i j, distTest t (4 * ρ - 2 * r) i j = true ↔ β i = β j := by
    intro i j
    rw [distTest_node u (by omega)]
    constructor
    · intro h
      by_contra hne
      exact (hβ i j).2 hne (withinDist_mono (by omega) h)
    · exact (hβ i j).1
  have hfind : ∀ i, ∃ m, (List.finRange ℓ).find? (fun j => distTest t (4 * ρ - 2 * r) i j) =
      some m ∧ β i = β m := by
    intro i
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1
      (List.find?_isSome.2 ⟨i, List.mem_finRange i, (htest i i).2 rfl⟩ :
        ((List.finRange ℓ).find? (fun j => distTest t (4 * ρ - 2 * r) i j)).isSome)
    exact ⟨m, hm, (htest i m).1 (List.find?_some hm)⟩
  have hcanon : ∀ i j, canonBlock t (4 * ρ - 2 * r) i = canonBlock t (4 * ρ - 2 * r) j ↔
      β i = β j := by
    intro i j
    obtain ⟨mi, hmi, hβi⟩ := hfind i
    obtain ⟨mj, hmj, hβj⟩ := hfind j
    simp only [canonBlock, hmi, hmj, Option.getD_some]
    constructor
    · rintro rfl; rw [hβi, hβj]
    · intro hij
      have : (fun j' => distTest t (4 * ρ - 2 * r) i j') =
          (fun j' => distTest t (4 * ρ - 2 * r) j j') := by
        funext j'
        rw [Bool.eq_iff_iff, htest, htest, hij]
      rw [this, hmj] at hmi
      exact (Option.some_injective _ hmi).symm
  intro i j
  simp only [Ne, hcanon]
  exact hβ i j

/-- The search for the radius succeeds, with an admissible pair. -/
theorem findRadius_spec {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    rhoMinus (k + 1) q ≤ findRadius (node G k (q + 1) u) (rhoMinus (k + 1) q) ∧
      findRadius (node G k (q + 1) u) (rhoMinus (k + 1) q) ≤ 9 ^ (ℓ - 1) * rhoMinus (k + 1) q ∧
      Admissible G.resolved (rhoMinus (k + 1) q) u
        (findRadius (node G k (q + 1) u) (rhoMinus (k + 1) q))
        (canonBlock (node G k (q + 1) u)
          (4 * findRadius (node G k (q + 1) u) (rhoMinus (k + 1) q) - 2 * rhoMinus (k + 1) q)) := by
  set r := rhoMinus (k + 1) q with hr_def
  set t := node G k (q + 1) u
  have hr : r ≤ 9 ^ (ℓ - 1) * r := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))
  obtain ⟨⟨ρ₀, β₀, hρ₀, hρ₀', hadm⟩, -⟩ := clustering G.resolved r ℓ h1 u
  have hmem : ρ₀ ∈ List.range' r (9 ^ (ℓ - 1) * r - r + 1) := by
    rw [List.mem_range']; exact ⟨ρ₀ - r, by omega, by omega⟩
  have hsome : ((List.range' r (9 ^ (ℓ - 1) * r - r + 1)).find?
      (fun ρ => admissibleB t r ρ (canonBlock t (4 * ρ - 2 * r)))).isSome := by
    refine List.find?_isSome.2 ⟨ρ₀, hmem, ?_⟩
    have hs := (radius_bounds (q := q) h1 hk hρ₀').1
    exact (admissibleB_node u r hs _).2 (admissible_canonBlock u r hs hadm)
  obtain ⟨ρ₁, hρ₁⟩ := Option.isSome_iff_exists.1 hsome
  have hρeq : findRadius t r = ρ₁ := by simp only [findRadius, hρ₁, Option.getD_some]
  have hm := List.mem_range'.1 (List.mem_of_find?_eq_some hρ₁)
  have hp := List.find?_some hρ₁
  rw [hρeq]
  obtain ⟨i, hi, hρ₁i⟩ := hm
  have hb : ρ₁ ≤ 9 ^ (ℓ - 1) * r := by omega
  refine ⟨by omega, hb, ?_⟩
  exact (admissibleB_node u r (radius_bounds (q := q) h1 hk hb).1 _).1 hp

theorem lastTree_node {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (b : Fin n) :
    lastTree k q ℓ (node G (k + 1) q (Fin.snoc u b)) = tree G (k + 1) q ![b] := by
  simp only [lastTree, tree, restrictNode_node G q (k + 1) (isPInv_lastPInv ℓ)]
  congr 2
  funext j
  rw [Fin.fin_one_eq_zero j]
  simp

theorem distLe_last_node {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (b : Fin n) (j : Fin ℓ) :
    DistFO.distLe (rhoMinus (k + 1) q) j.castSucc (Fin.last ℓ) ∈
        Node.atoms (node G (k + 1) q (Fin.snoc u b)) ↔
      WithinDist G.resolved (rhoMinus (k + 1) q) (u j) b := by
  rw [mem_atoms_node]
  simp only [Sat, Fin.snoc_castSucc, Fin.snoc_last]
  exact ⟨fun h => h.2.2, fun h => ⟨trivial, .distLe _ _ _ le_rfl, h⟩⟩

theorem mem_nearFarSet {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (ν : TypeTree) :
    ν ∈ nearFarSet k q ℓ (rhoMinus (k + 1) q) (node G k (q + 1) u) ↔
      ∃ b, (∃ i, WithinDist G.resolved (rhoPlus (k + 1) q) (u i) b) ∧
        (∀ j, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u j) b) ∧
        ν = tree G (k + 1) q ![b] := by
  simp only [nearFarSet, Finset.mem_image, Finset.mem_filter, isFarExt, decide_eq_true_iff]
  constructor
  · rintro ⟨e, ⟨he, hfar⟩, rfl⟩
    obtain ⟨i, b, hb, rfl⟩ := (mem_exts_node G k q u e).1 he
    refine ⟨b, ⟨i, hb⟩, fun j hj => hfar j ((distLe_last_node u b j).2 hj), ?_⟩
    exact lastTree_node u b
  · rintro ⟨b, ⟨i, hb⟩, hfar, rfl⟩
    exact ⟨_, ⟨(mem_exts_node G k q u _).2 ⟨i, b, hb, rfl⟩,
      fun j hj => hfar j ((distLe_last_node u b j).1 hj)⟩, lastTree_node u b⟩

theorem mem_metPositions {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (ν : TypeTree) (i : Fin ℓ) :
    i ∈ metPositions k q ℓ (rhoMinus (k + 1) q) (node G k (q + 1) u) ν ↔
      ∃ b, tree G (k + 1) q ![b] = ν ∧ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b := by
  simp only [metPositions, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, ⟨he, hν⟩, hi⟩
    obtain ⟨j, b, hb, rfl⟩ := (mem_exts_node G k q u e).1 he
    exact ⟨b, (lastTree_node u b).symm.trans hν, (distLe_last_node u b i).1 hi⟩
  · rintro ⟨b, hν, hb⟩
    have hH : rhoMinus (k + 1) q ≤ rhoPlus (k + 1) q := rhoMinus_le_rhoPlus _ _
    exact ⟨_, ⟨(mem_exts_node G k q u _).2 ⟨i, b, withinDist_mono hH hb, rfl⟩,
      (lastTree_node u b).trans hν⟩, (distLe_last_node u b i).2 hb⟩

theorem domain_finite (k q : ℕ) : (domain G k q).Finite := by
  refine (((Set.finite_le_nat (9 ^ (k + q) * rhoMinus (k + q) q)).prod
    (Set.finite_range (fun p : Fin (q + 1) × Fin n =>
      tree G (k + p.1) (q - p.1) ![p.2])))).subset ?_
  rintro ⟨s, ν⟩ ⟨i, b, hi1, hiq, hs1, hs, rfl⟩
  refine ⟨?_, ⟨(⟨i, by omega⟩, b), rfl⟩⟩
  simp only [Set.mem_ofPred_eq]
  refine hs.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) ?_)
  exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (by omega) (by omega))

theorem mem_stp (k q : ℕ) (p : (ℕ × TypeTree) × ℕ) :
    p ∈ stp G k q ↔ p.1 ∈ domain G k q ∧ p.2 = value G k q p.1 := by
  unfold stp graphOn
  refine mem_finsetOf ?_
  refine ((domain_finite (G := G) k q).image fun d => (d, value G k q d)).subset ?_
  rintro ⟨d, m⟩ ⟨hd, hm⟩
  simp only at hd hm
  exact ⟨d, hd, by rw [hm]⟩

theorem mem_ftree (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (ν : TypeTree) :
    ν ∈ ftree G k (q + 1) u ↔ ∃ b, (∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b) ∧
      ν = tree G (k + 1) q ![b] := by
  unfold ftree
  rw [mem_finsetOf]
  · simp
  · refine (Set.finite_range fun b : Fin n => tree G (k + 1) (q + 1 - 1) ![b]).subset ?_
    rintro _ ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩

/-- **lem:to-ftree, semantic form.** -/
theorem farTreeNode_node (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    farTreeNode k q ℓ (node G k (q + 1) u) (stp G k (q + 1)) = ftree G k (q + 1) u := by
  obtain ⟨hρ1, hρ2, hadm⟩ := findRadius_spec (G := G) (q := q) u h1 hk
  set r := rhoMinus (k + 1) q with hr_def
  set t := node G k (q + 1) u
  set ρ := findRadius t r
  set β := canonBlock t (4 * ρ - 2 * r)
  obtain ⟨-, hH, hdom⟩ := radius_bounds (q := q) h1 hk hρ2
  have hr1 := one_le_rhoMinus (k + 1) q
  -- clustering for the realizations of a tree
  have hclust := (clustering G.resolved r ℓ h1 u).2 ρ β hρ1 hadm
  have key : ∀ b : Fin n, let ν := tree G (k + 1) q ![b]
      (ν ∈ nearFarSet k q ℓ r t ∨
        ((metPositions k q ℓ r t ν).image β).card < value G k (q + 1) (4 * ρ, ν)) ↔
      ∃ x, tree G (k + 1) q ![x] = ν ∧ ∀ i, ¬ WithinDist G.resolved r (u i) x := by
    intro b ν
    set X : Set (Fin n) := realizations G ν
    obtain ⟨hSX, hSsep, hScov, hScard⟩ := greedyScattered_set G (4 * ρ) X
    have hc := hclust X _ (rhoPlus (k + 1) q) hSX hSsep hScov hH
    have hXmem : ∀ x, x ∈ X ↔ tree G (k + 1) q ![x] = ν := fun x => Iff.rfl
    have hcount : ((metPositions k q ℓ r t ν).image β).card =
        (β '' {i | ∃ x ∈ X, WithinDist G.resolved r (u i) x}).ncard := by
      rw [← Set.ncard_coe_finset, Finset.coe_image]
      congr 2
      ext i
      simp only [Finset.mem_coe, Set.mem_ofPred_eq, hXmem]
      exact mem_metPositions (G := G) u ν i
    have hle : ((metPositions k q ℓ r t ν).image β).card < k + (q + 1) := by
      have := Finset.card_le_univ ((metPositions k q ℓ r t ν).image β)
      simp only [Fintype.card_fin] at this
      omega
    have hval : value G k (q + 1) (4 * ρ, ν) = min (greedyScattered G (4 * ρ) X).length
        (k + (q + 1)) := rfl
    rw [hval, lt_min_iff, and_iff_left hle, ← hScard, hcount,
      show ν ∈ nearFarSet k q ℓ r t ↔ _ from mem_nearFarSet u ν]
    simp only [hXmem] at hc
    rw [hc]
    constructor
    · rintro (⟨x, ⟨i, hi⟩, hfar, hx⟩ | h)
      · exact Or.inl ⟨x, hx.symm, hfar, i, hi⟩
      · exact Or.inr h
    · rintro (⟨x, hx, hfar, i, hi⟩ | h)
      · exact Or.inl ⟨x, ⟨i, hi⟩, hfar, hx.symm⟩
      · exact Or.inr h
  ext ν
  rw [mem_ftree]
  simp only [farTreeNode, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨⟨s, ν'⟩, m⟩, ⟨hp, hs, hk', hq', hcond⟩, rfl⟩
    rw [mem_stp] at hp
    obtain ⟨⟨i, b, hi1, hiq, -, -, hν'⟩, hm⟩ := hp
    simp only at hs hk' hq' hcond hm hν' ⊢
    subst hs hm
    have hi : i = 1 := by rw [hν'] at hk'; simp only [tree] at hk'; omega
    subst hi
    rw [show q + 1 - 1 = q by omega] at hν'
    subst hν'
    obtain ⟨x, hx, hfar⟩ := (key b).1 hcond
    exact ⟨x, hfar, hx.symm⟩
  · rintro ⟨x, hfar, rfl⟩
    refine ⟨((4 * ρ, tree G (k + 1) q ![x]), value G k (q + 1) (4 * ρ, tree G (k + 1) q ![x])),
      ⟨?_, rfl, rfl, rfl, (key x).2 ⟨x, rfl, hfar⟩⟩, rfl⟩
    rw [mem_stp]
    refine ⟨⟨1, x, le_rfl, by omega, show 1 ≤ 4 * ρ by omega, ?_, ?_⟩, rfl⟩
    · simpa using hdom
    · simp

/-- **lem:to-ftree, on type trees.** -/
theorem farTree_tree (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    farTree (tree G k (q + 1) u) (stp G k (q + 1)) = ftree G k (q + 1) u :=
  farTreeNode_node k q u h1 hk

end Correctness

end Lax185574Proofs.TreeAlgo
