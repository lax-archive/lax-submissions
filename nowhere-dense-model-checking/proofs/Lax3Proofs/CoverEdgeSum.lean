import Lax3Proofs.CoverDegree

/-!
The edge half of the cluster-mass bound (★).

`CoverDegree.sum_ncard_le_mul` charges the *vertices* of all clusters of
a degree-`d` family against `N · d`.  The driver's cost accounting runs
against the weight `‖A‖ = N + M` of an adjacency structure, so the same
charge is owed for the *edges* internal to the clusters, and it is not a
consequence of the vertex count: `CoverDegree` never mentions an edge.

This file supplies it.  The argument is one double count, dual to the
vertex one.  An edge `e` of `G` is internal to the cluster `X u` only if
*both* of its endpoints lie in `X u`; in particular one fixed endpoint
does, so the fibre `{u | e internal to X u}` embeds in `{u | x ∈ X u}`
for an endpoint `x` of `e`, and the degree hypothesis caps that fibre at
`d`.  Summing the incidences the other way gives
`∑ u ‖A[X u]‖ₑ ≤ d · M` (`sum_ncard_internalEdgeSet_le`), which adds to
the vertex half as `∑ u ‖A[X u]‖ ≤ d · ‖A‖` (`sum_clusterWeight_le`).

# The ceiling

`CoverDegree.exists_cover_degree` delivers the degree as `⌈c · N ^ δ⌉₊`,
not as `c · N ^ δ`, and the ceiling must be carried: at `c = 1`, `δ = ½`,
`N = 2` the true product `⌈c·N^δ⌉₊ · N` is `4`, while `c · N ^ (1+δ)` is
only `2.83`.  `sum_clusterWeight_le_rpow` absorbs it into the stated
constant `c + 1`, using `⌈x⌉₊ ≤ x + 1` and `1 ≤ ‖A‖ ^ δ` — which is
where the hypothesis `1 ≤ ‖A‖` is spent.  The other real step is that
the degree is stated at the vertex count `N` while the conclusion is at
the weight `‖A‖ = N + M ≥ N`; monotonicity of `x ↦ x ^ δ` for `δ ≥ 0`
covers it.

# Spelling

"Internal edge" is `internalEdgeSet G S = {e ∈ G.edgeSet | ∀ x ∈ e, x ∈ S}`,
a `Set (Sym2 (Fin N))` counted with `Set.ncard` — the cardinality idiom
of `CoverDegree` and of the `Lax12` concepts, and the spelling that needs
no `DecidableRel G.Adj` in any statement.  `internalEdgeSet_univ` pins it
against `G.edgeSet` at `S = Set.univ`, so `clusterWeight G Set.univ` is
literally `graphWeight G`.
-/

namespace Lax3Proofs.CoverEdgeSum

open scoped SimpleGraph
open Lax3.NeighborhoodCovers

variable {N : ℕ}

/-! ## Internal edges and weight -/

/-- The edges of `G` **internal** to a vertex set `S`: both endpoints lie
in `S`.  This is the edge set of `A[S]`, spelled inside `Sym2 (Fin N)`
so that no coercion of the vertex type is involved. -/
def internalEdgeSet (G : SimpleGraph (Fin N)) (S : Set (Fin N)) : Set (Sym2 (Fin N)) :=
  {e ∈ G.edgeSet | ∀ x ∈ e, x ∈ S}

@[simp] lemma mem_internalEdgeSet {G : SimpleGraph (Fin N)} {S : Set (Fin N)}
    {e : Sym2 (Fin N)} :
    e ∈ internalEdgeSet G S ↔ e ∈ G.edgeSet ∧ ∀ x ∈ e, x ∈ S := Iff.rfl

/-- Internal edges of the whole vertex set are all the edges. -/
@[simp] lemma internalEdgeSet_univ (G : SimpleGraph (Fin N)) :
    internalEdgeSet G Set.univ = G.edgeSet := by
  ext e; simp [internalEdgeSet]

lemma internalEdgeSet_subset (G : SimpleGraph (Fin N)) (S : Set (Fin N)) :
    internalEdgeSet G S ⊆ G.edgeSet := fun _ he => he.1

/-- `‖A[S]‖`: the weight of the substructure of `G` on `S` — its
vertices plus its internal edges. -/
noncomputable def clusterWeight (G : SimpleGraph (Fin N)) (S : Set (Fin N)) : ℕ :=
  S.ncard + (internalEdgeSet G S).ncard

/-- `‖A‖ = N + M`, the weight of the whole adjacency structure
(`algorithm-v2.md:431`). -/
noncomputable def graphWeight (G : SimpleGraph (Fin N)) : ℕ := N + G.edgeSet.ncard

@[simp] lemma clusterWeight_univ (G : SimpleGraph (Fin N)) :
    clusterWeight G Set.univ = graphWeight G := by
  simp [clusterWeight, graphWeight, Set.ncard_univ]

/-! ## The edge fibre bound -/

/-- **Edge fibre.**  An edge lies in at most `d` clusters, because one of
its endpoints must lie in every cluster it is internal to, and no vertex
lies in more than `d` clusters. -/
lemma ncard_internal_fibre_le (X : Fin N → Set (Fin N)) (d : ℕ)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ d) (e : Sym2 (Fin N)) :
    {u : Fin N | ∀ x ∈ e, x ∈ X u}.ncard ≤ d := by
  induction e with
  | _ x y =>
    refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (h x)
    exact fun u hu => hu x (Sym2.mem_mk_left x y)

/-- **Cluster edge mass.**  The edge half of (★): a family of vertex sets
no vertex of which lies in more than `d` members has total *internal edge*
count at most `d · M`.  Both sides count the incidences between edges and
the clusters they are internal to. -/
theorem sum_ncard_internalEdgeSet_le (G : SimpleGraph (Fin N))
    (X : Fin N → Set (Fin N)) (d : ℕ)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ d) :
    ∑ u : Fin N, (internalEdgeSet G (X u)).ncard ≤ d * G.edgeSet.ncard := by
  classical
  have hE : G.edgeSet.Finite := Set.toFinite _
  set E : Finset (Sym2 (Fin N)) := hE.toFinset with hEdef
  -- every cluster's internal edge set is a filter of `E`
  have hcard : ∀ u : Fin N, (internalEdgeSet G (X u)).ncard
      = (E.filter (fun e => ∀ x ∈ e, x ∈ X u)).card := by
    intro u
    rw [← Set.ncard_coe_finset]
    congr 1
    ext e
    simp [hEdef, internalEdgeSet]
  have hEcard : G.edgeSet.ncard = E.card := Set.ncard_eq_toFinset_card _ hE
  -- swap the two summations
  calc ∑ u : Fin N, (internalEdgeSet G (X u)).ncard
      = ∑ u : Fin N, ∑ e ∈ E, if (∀ x ∈ e, x ∈ X u) then 1 else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hcard u, Finset.card_filter]
    _ = ∑ e ∈ E, ∑ u : Fin N, if (∀ x ∈ e, x ∈ X u) then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ _e ∈ E, d := by
        refine Finset.sum_le_sum fun e _ => ?_
        have hfin : (∑ u : Fin N, if (∀ x ∈ e, x ∈ X u) then 1 else 0)
            = {u : Fin N | ∀ x ∈ e, x ∈ X u}.ncard := by
          rw [← Finset.card_filter, ← Set.ncard_coe_finset]
          congr 1
          ext u
          simp
        rw [hfin]
        exact ncard_internal_fibre_le X d h e
    _ = d * G.edgeSet.ncard := by
        rw [Finset.sum_const, smul_eq_mul, hEcard, Nat.mul_comm]

/-! ## The weight form -/

/-- **Cluster mass, vertices and edges.**  Adding the edge half to
`CoverDegree.sum_ncard_le_mul`: the clusters of a degree-`d` family have
total weight at most `d · ‖A‖`. -/
theorem sum_clusterWeight_le (G : SimpleGraph (Fin N)) (X : Fin N → Set (Fin N)) (d : ℕ)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ d) :
    ∑ u : Fin N, clusterWeight G (X u) ≤ d * graphWeight G := by
  have hV : ∑ u : Fin N, (X u).ncard ≤ N * d := CoverDegree.sum_ncard_le_mul X d h
  have hEd : ∑ u : Fin N, (internalEdgeSet G (X u)).ncard ≤ d * G.edgeSet.ncard :=
    sum_ncard_internalEdgeSet_le G X d h
  calc ∑ u : Fin N, clusterWeight G (X u)
      = (∑ u : Fin N, (X u).ncard) + ∑ u : Fin N, (internalEdgeSet G (X u)).ncard := by
        rw [← Finset.sum_add_distrib]; rfl
    _ ≤ N * d + d * G.edgeSet.ncard := Nat.add_le_add hV hEd
    _ = d * graphWeight G := by rw [graphWeight, Nat.mul_add, Nat.mul_comm N d]

/-- The same, for the clusters of an `r`-neighborhood cover. -/
theorem sum_clusterWeight_le_of_isNeighborhoodCover {r d : ℕ} {G : SimpleGraph (Fin N)}
    {X : Fin N → Set (Fin N)} (hcov : IsNeighborhoodCover G r X d) :
    ∑ u : Fin N, clusterWeight G (X u) ≤ d * graphWeight G :=
  sum_clusterWeight_le G X d hcov.degree_le

/-! ## (★), with the ceiling absorbed -/

/-- **(★).**  With the degree in the shape `CoverDegree.exists_cover_degree`
delivers it — `⌈c · N ^ δ⌉₊`, ceiling included — the total weight of all
clusters is at most `(c + 1) · ‖A‖ ^ (1 + δ)`.

The `+1` in the constant is exactly the ceiling; it cannot be dropped.
The three hypotheses are the ones the caller has to supply: the structure
is nonempty (`1 ≤ ‖A‖`), and the two constants of the cover bound are
nonnegative. -/
theorem sum_clusterWeight_le_rpow (G : SimpleGraph (Fin N)) (X : Fin N → Set (Fin N))
    (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hW : 1 ≤ graphWeight G)
    (h : ∀ v : Fin N, {u : Fin N | v ∈ X u}.ncard ≤ ⌈c * (N : ℝ) ^ δ⌉₊) :
    ((∑ u : Fin N, clusterWeight G (X u) : ℕ) : ℝ)
      ≤ (c + 1) * ((graphWeight G : ℕ) : ℝ) ^ (1 + δ) := by
  set W : ℝ := ((graphWeight G : ℕ) : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast hW
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW1
  have hNW : ((N : ℕ) : ℝ) ≤ W := by
    have h : (N : ℕ) ≤ graphWeight G := Nat.le_add_right _ _
    rw [hWdef]; exact_mod_cast h
  have hNnn : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
  -- the ceiling, honestly
  have hxnn : (0 : ℝ) ≤ c * ((N : ℕ) : ℝ) ^ δ := mul_nonneg hc (Real.rpow_nonneg hNnn δ)
  have hceil : ((⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ : ℕ) : ℝ) ≤ c * ((N : ℕ) : ℝ) ^ δ + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hxnn)
  -- `N ^ δ ≤ W ^ δ` and `1 ≤ W ^ δ`
  have hmono : ((N : ℕ) : ℝ) ^ δ ≤ W ^ δ := Real.rpow_le_rpow hNnn hNW hδ
  have hone : (1 : ℝ) ≤ W ^ δ := by
    have := Real.rpow_le_rpow (le_of_lt zero_lt_one) hW1 hδ
    rwa [Real.one_rpow] at this
  have hWδnn : (0 : ℝ) ≤ W ^ δ := le_trans zero_le_one hone
  -- the integer bound, cast up
  have hnat : (∑ u : Fin N, clusterWeight G (X u) : ℕ)
      ≤ ⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ * graphWeight G :=
    sum_clusterWeight_le G X _ h
  have hcast : ((∑ u : Fin N, clusterWeight G (X u) : ℕ) : ℝ)
      ≤ ((⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ : ℕ) : ℝ) * W := by
    rw [hWdef, ← Nat.cast_mul]
    exact_mod_cast hnat
  refine le_trans hcast ?_
  have hstep : ((⌈c * ((N : ℕ) : ℝ) ^ δ⌉₊ : ℕ) : ℝ) * W ≤ (c * W ^ δ + W ^ δ) * W := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hWpos)
    refine le_trans hceil ?_
    exact add_le_add (mul_le_mul_of_nonneg_left hmono hc) hone
  refine le_trans hstep (le_of_eq ?_)
  have hsplit : W ^ (1 + δ) = W * W ^ δ := by
    rw [Real.rpow_add hWpos, Real.rpow_one]
  rw [hsplit]
  ring

/-- (★) for the clusters of an `r`-neighborhood cover of degree
`⌈c · N ^ δ⌉₊` — the exact conclusion of
`CoverDegree.exists_cover_degree`. -/
theorem sum_clusterWeight_le_rpow_of_isNeighborhoodCover {r : ℕ} {G : SimpleGraph (Fin N)}
    {X : Fin N → Set (Fin N)} {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hW : 1 ≤ graphWeight G)
    (hcov : IsNeighborhoodCover G r X ⌈c * (N : ℝ) ^ δ⌉₊) :
    ((∑ u : Fin N, clusterWeight G (X u) : ℕ) : ℝ)
      ≤ (c + 1) * ((graphWeight G : ℕ) : ℝ) ^ (1 + δ) :=
  sum_clusterWeight_le_rpow G X c δ hc hδ hW hcov.degree_le

end Lax3Proofs.CoverEdgeSum
