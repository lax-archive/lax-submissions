import Lax3Proofs.CoverRoutine

/-!
# F5 — the cover pipeline's ordering phase, priced (the greedy chain's charge)

`CoverRoutine` (F1) built the greedy ordering routine and discharged the
`data` half of `CoverSpec.IsCoverOrdering` hypothesis-free, leaving
`steps := 0` as an explicit placeholder.  This file replaces the
placeholder with the honest account and proves the `time` half — so that
**`CoverSpec.CoverOrderingTime C` holds for every nowhere dense class
`C`** (`coverOrderingTime_of_nowhereDense`), the design's one remaining
mathematical import.

A caution the statement itself forces into the open: because
`OrderingOutput.steps` is *data*, the bare Prop `CoverOrderingTime C`
could be discharged vacuously by the `steps := 0` placeholder routine.
That discharge would be worthless — the content of this file is that the
witness routine below carries the **honest** charge of the pipeline
(`chainCharge`, each summand priced against the source algorithm), and
that *this* charge meets the bound.  `E12` is expected to re-derive the
same `steps` from a machine; the charge here is the number it must
reproduce.

## The charge, summand by summand

The routine's shape is F1's: the base orientation along a greedy
elimination of `G`; then `R` greedy rounds, round `i + 1` orienting the
new arcs along a greedy elimination of `fratGraph (D i)`; then a final
greedy elimination of the symmetrized augmented graph `(D R).toGraph`,
whose ranking (a permutation after inversion) is the output ordering.
The costs are the source's — Nešetřil–Ossona de Mendez, *Grad and
classes with bounded expansion II* (`references/nodm05/BEII.tex`), §4:
transitivity arcs in `O(md²·n)` (tex:615-620), fraternity edges in
`O(md²·n)` (tex:672-674), simplification + low-indegree orientation +
merge in `O(md²·n)` (tex:676-678), the orientation itself `O(n + m)`
(tex:446-499).  Per level at in-degree `≤ d` the concrete counts are:

* **candidate enumeration** — a transitive candidate is a directed path
  `u → w → v`, one per pair (in-arc of `v`, in-arc of its tail `w`):
  `transPairCount D = Σ_v Σ_{w ∈ inN v} |inN w| ≤ d²·n`.  A fraternal
  candidate is a pair of in-arcs of a common head:
  `fratPairCount D = Σ_w |inN w|² ≤ d²·n`.  This prices the *witness
  enumeration* of the links — **not** the `pick`-over-`univ` spelling of
  the mathematical definition `greedyStep`, whose literal `n²` scan is
  an artifact of stating the step as a filter;
* **the peel** of `fratGraph (D i)` — the low-indegree orientation of
  BEII tex:446-499, `O(#vertices + #edges)`; the fraternity graph's
  edges are among the fraternal candidate pairs, so `n + fratPairCount`
  covers it (bucketed min-degree deletion; the minimal bound
  `elimBound`, an `sInf` in the mathematics, is read off the peel as
  the largest degree at deletion time);
* **the step application** — one `O(1)` orientation decision per
  enumerated candidate: `transPairCount + fratPairCount` again;
* **carrying the old arcs** — `arcCount D = Σ_v |inN v| ≤ d·n`.

`levelCharge D = n + arcCount D + 3·fratPairCount D + 2·transPairCount D`
allocates one `fratPairCount` to the peel, one to the enumeration, one
to the application, and the two `transPairCount`s to enumeration and
application.  The base charge `m + 3·arcCount (D 0)` prices the peel of
`G` itself plus building `baseOr` (the arcs of `D 0` *are* the edges of
`G`: `baseOr_orients`).  The final charge `3·n + 5·arcCount (D R)`
prices symmetrizing `(D R).toGraph` (adjacency from the arcs, `≤ 2·arcs`
entries), its peel (`n + 2·arcs`), and emitting the ordering.

**The sort that is not there.**  `AugChainData` speaks of a permutation,
and F1 obtains it from the ranking by `rankPerm` — a *sort* of the
ranking's image.  No sort is priced, because none is run: the landed
peel construction ranks into `[0, S.card)`
(`degeneracyLE_of_lowDegreeVertices`, invariant `∀ v ∈ S, σ v < S.card`,
`Augmentation.lean:337`), i.e. the implementation emits the elimination
*positions* `0..n-1` directly, and realizing the permutation from an
injective rank array with values in `[0, n)` is an array inversion —
`n` writes, inside the final charge's `3·n`.  `rankPerm` is the
mathematical description of that inversion, not an algorithmic step.

## Where the in-degree bound comes from

The greedy chain's per-round in-degree bound on a nowhere dense class is
**landed**: `AugmentedDensity.greedy_chain_joint_inDegLE` runs the joint
in-degree/density recursion from a depth-`chainDepth R 1` density bound
(`exists_densityAtMost_of_nowhereDense`), and `CoverDegree.joint_fst_le`
closes the budget to `(d₀ + D₁ + 2) ^ 16 ^ i`.  (This is the same pair
of facts `CoverDegree.exists_cover_degree` already consumes; the
`AugmentedDepthOneDensity` hypothesis of the older
`Augmentation.greedy_chain_inDegLE` is discharged by that file, and
`exists_augChain_inDeg_subpolynomial` — a bound for the *canonical wcol
chain*, a different chain — is not involved.)  What is new here is only
the uniformization `exists_greedyChain_inDegLE`: one bound
`⌈c·m^δ⌉₊` for **all** rounds `i ≤ R` at once, `c` fixed before the
graph.

## The exponent

With the inner exponent `δ/(2·16^R)` the uniform in-degree bound is
`dmax ≤ (3c₀+5)^{16^R}·m^{δ/2}`, so the priced chain lands at
`chainCharge ≤ f·m^{1+δ}` (`exists_chainCharge_le`) — the shape of GKS's
own ordering account (`g(r,ε)·n^{1+ε}`, gks tex:1460-1463).  The
interface's `time` field asks for `1 + 2δ` (the sweep's exponent, which
dominates); `exists_chainCharge_le_double` weakens to it.  Quantifier
order throughout: the constant *before* `n`, `Gn`, `m`, `G`.
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax12.GraphClasses Lax12.NowhereDenseClasses Lax12.ShallowMinorDensity
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.AugmentedDensity
open Lax3Proofs.CoverDegree
open Lax3Proofs.CoverRoutine

variable {n : ℕ}

/-! ### The per-level counts

Three quantities of an orientation, each the exact number of objects one
stage of a greedy round touches.  All are `Σ`-formulas in the
in-neighbourhood sizes, so a uniform in-degree bound prices them. -/

/-- The arcs of an orientation: `Σ_v |inN v|`.  What carrying the old
arcs through a round costs, and — at `D 0`, which orients `G` — the
edge count of `G` itself. -/
def arcCount (D : Orientation n) : ℕ := ∑ v, (D.inN v).card

/-- The fraternal candidate pairs: `Σ_w |inN w|²` — for each vertex,
the ordered pairs of its in-arcs.  Every fraternal link `u → w ← v` is
witnessed here at `w`; this is BEII's `O(md²·n)` fraternity enumeration
(tex:672-674), and the edges of `fratGraph D` are among these pairs. -/
def fratPairCount (D : Orientation n) : ℕ := ∑ w, (D.inN w).card * (D.inN w).card

/-- The transitive candidate paths: `Σ_v Σ_{w ∈ inN v} |inN w|` — the
directed paths `u → w → v`.  Every transitive link is witnessed by one;
this is BEII's `O(md²·n)` transitivity enumeration (tex:615-620). -/
def transPairCount (D : Orientation n) : ℕ := ∑ v, ∑ w ∈ D.inN v, (D.inN w).card

/-- **The charge of one greedy round** from `D`: the vertex scan of the
fraternity peel, the old arcs, and the candidate enumeration — one
`fratPairCount` each for the peel's edge work, the fraternal
enumeration and the step application, one `transPairCount` each for the
transitive enumeration and the step application (module docstring). -/
def levelCharge (D : Orientation n) : ℕ :=
  n + arcCount D + 3 * fratPairCount D + 2 * transPairCount D

/-! ### The counts, priced by an in-degree bound

Every summand is per-vertex at most a product of in-degrees, so a
uniform bound `d` prices the sums at `n·d` resp. `n·d²`.  This is the
`d`-parameterization that keeps `n²` out of the theorem: no count is
ever bounded by the carrier alone. -/

theorem arcCount_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    arcCount D ≤ n * d := by
  show ∑ v : Fin n, (D.inN v).card ≤ n * d
  calc ∑ v : Fin n, (D.inN v).card ≤ ∑ _v : Fin n, d :=
        Finset.sum_le_sum fun v _ => hd v
    _ = n * d := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]

theorem fratPairCount_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    fratPairCount D ≤ n * (d * d) := by
  show ∑ w : Fin n, (D.inN w).card * (D.inN w).card ≤ n * (d * d)
  calc ∑ w : Fin n, (D.inN w).card * (D.inN w).card ≤ ∑ _w : Fin n, d * d :=
        Finset.sum_le_sum fun w _ => Nat.mul_le_mul (hd w) (hd w)
    _ = n * (d * d) := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]

theorem transPairCount_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    transPairCount D ≤ n * (d * d) := by
  show ∑ v : Fin n, ∑ w ∈ D.inN v, (D.inN w).card ≤ n * (d * d)
  calc ∑ v : Fin n, ∑ w ∈ D.inN v, (D.inN w).card
      ≤ ∑ v : Fin n, ∑ _w ∈ D.inN v, d :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hd w
    _ = ∑ v : Fin n, (D.inN v).card * d := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ _v : Fin n, d * d :=
        Finset.sum_le_sum fun v _ => Nat.mul_le_mul_right d (hd v)
    _ = n * (d * d) := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]

/-- **The per-level charge, priced**: at in-degree `≤ d` one greedy
round costs at most `n·(1 + d + 5d²)` — the `O(md²·n)` of BEII §4 with
`m_d = d`, and never a flat `n²`. -/
theorem levelCharge_le {D : Orientation n} {d : ℕ} (hd : D.InDegLE d) :
    levelCharge D ≤ n * (1 + d + 5 * (d * d)) := by
  have h1 := arcCount_le hd
  have h2 := fratPairCount_le hd
  have h3 := transPairCount_le hd
  calc levelCharge D
      = n + arcCount D + 3 * fratPairCount D + 2 * transPairCount D := rfl
    _ ≤ n + n * d + 3 * (n * (d * d)) + 2 * (n * (d * d)) := by omega
    _ = n * (1 + d + 5 * (d * d)) := by ring

/-! ### The chain's charge -/

/-- The charge of the base level: peel `G` and orient it along the peel
(`baseOr G (elimPerm G)`).  The peel is `O(n + |E(G)|)` and the arcs of
`D 0` are exactly the edges of `G` (`baseOr_orients`), so `m + 3·arcs`
covers the peel's vertex scan, its edge work and the orientation
build. -/
noncomputable def baseCharge {m : ℕ} (G : SimpleGraph (Fin m)) : ℕ :=
  m + 3 * arcCount (greedyChain G 0)

/-- The charge of the final elimination: symmetrize `(D R).toGraph`
from the arcs (`≤ 2·arcs` adjacency entries), peel it (`n + 2·arcs`),
emit the elimination positions and invert the rank array (`2·n`; the
peel ranks into `[0, n)`, so the permutation is an array inversion and
**no sort is run** — module docstring). -/
noncomputable def finalCharge (D : Orientation n) : ℕ :=
  3 * n + 5 * arcCount D

/-- **The charge of the whole ordering phase** on `G`: the base peel,
the `R` greedy rounds, and the final elimination of the symmetrized
augmented graph.  This is the `steps` value of the timed routine. -/
noncomputable def chainCharge {m : ℕ} (G : SimpleGraph (Fin m)) (R : ℕ) : ℕ :=
  baseCharge G + (∑ i ∈ Finset.range R, levelCharge (greedyChain G i))
    + finalCharge (greedyChain G R)

/-- On the empty carrier every count is an empty sum: the charge is
`0`.  (The `m = 0` case of every bound below.) -/
theorem chainCharge_zero (G : SimpleGraph (Fin 0)) (R : ℕ) : chainCharge G R = 0 := by
  simp [chainCharge, baseCharge, finalCharge, levelCharge, arcCount, fratPairCount,
    transPairCount]

/-- **The chain total at a uniform in-degree bound**: `R` levels, the
base and the final elimination, all priced by one `d`, total
`(5R + 8)·m·(d+1)²`.  Pure counting — the class enters only through
`d`. -/
theorem chainCharge_le_of_uniform {m : ℕ} {G : SimpleGraph (Fin m)} {R d : ℕ}
    (hd : ∀ i ≤ R, (greedyChain G i).InDegLE d) :
    chainCharge G R ≤ (5 * R + 8) * (m * ((d + 1) * (d + 1))) := by
  have hbase : baseCharge G ≤ 3 * (m * ((d + 1) * (d + 1))) := by
    have h := arcCount_le (hd 0 (Nat.zero_le R))
    have : baseCharge G = m + 3 * arcCount (greedyChain G 0) := rfl
    nlinarith [h]
  have hfin : finalCharge (greedyChain G R) ≤ 5 * (m * ((d + 1) * (d + 1))) := by
    have h := arcCount_le (hd R le_rfl)
    have : finalCharge (greedyChain G R) = 3 * m + 5 * arcCount (greedyChain G R) := rfl
    nlinarith [h]
  have hsum : (∑ i ∈ Finset.range R, levelCharge (greedyChain G i))
      ≤ R * (5 * (m * ((d + 1) * (d + 1)))) := by
    calc (∑ i ∈ Finset.range R, levelCharge (greedyChain G i))
        ≤ ∑ _i ∈ Finset.range R, 5 * (m * ((d + 1) * (d + 1))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h := levelCharge_le (hd i (le_of_lt (Finset.mem_range.mp hi)))
          nlinarith [h]
      _ = R * (5 * (m * ((d + 1) * (d + 1)))) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
  calc chainCharge G R
      = baseCharge G + (∑ i ∈ Finset.range R, levelCharge (greedyChain G i))
        + finalCharge (greedyChain G R) := rfl
    _ ≤ 3 * (m * ((d + 1) * (d + 1))) + R * (5 * (m * ((d + 1) * (d + 1))))
        + 5 * (m * ((d + 1) * (d + 1))) := by omega
    _ = (5 * R + 8) * (m * ((d + 1) * (d + 1))) := by ring

/-! ### The greedy chain's in-degree on a class

Assembled from landed parts: the depth-`chainDepth R 1` density of a
subgraph of a member (`exists_densityAtMost_of_nowhereDense`), the
minimality of `elimBound` against it (`inDeg_zero_le` — the greedy
guarantee of F1's first elimination), the joint recursion
(`greedy_chain_joint_inDegLE`) and its closed form (`joint_fst_le`). -/

/-- **The greedy chain's rounds, uniformly bounded on a class** (raw
form): for every round count and inner exponent there is a `c₀` such
that on every subgraph copy of a member all rounds `i ≤ R` of *the*
greedy chain have in-degree at most `(3·⌈c₀·m^δ'⌉₊ + 2) ^ 16 ^ R`. -/
theorem exists_greedyChain_inDegLE_pow (C : GraphClass) (hC : NowhereDense C)
    (R : ℕ) (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ i ≤ R, (greedyChain G i).InDegLE
          ((3 * ⌈c₀ * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ R) := by
  obtain ⟨c₀, hc₀⟩ := exists_densityAtMost_of_nowhereDense C hC (chainDepth R 1) δ' hδ'
  refine ⟨max c₀ 0, le_max_right _ _, fun n Gn hGn m G hsub => ?_⟩
  have hXnn : (0 : ℝ) ≤ (m : ℝ) ^ δ' := Real.rpow_nonneg (Nat.cast_nonneg m) δ'
  have hdensR : HasDensityAtMost G (chainDepth R 1) ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    hasDensityAtMost_mono
      (Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) hXnn))
      (hc₀ n Gn hGn m G hsub)
  have hdens1 : HasDensityAtMost G 1 ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    hasDensityAtMost_mono_depth
      (show (1 : ℕ) ≤ chainDepth R 1 from chainDepth_mono_round 1 (Nat.zero_le R)) hdensR
  have hd0 : (greedyChain G 0).InDegLE (elimBound G) := inDegLE_baseOr_elimPerm G
  have hd0le : elimBound G ≤ 2 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ :=
    inDeg_zero_le hdens1 fun _k' hk' => elimBound_le hk'
  have hjoint := greedy_chain_joint_inDegLE (isAugChain_greedyChain G R)
    (fun i _ => greedyFratRound_greedyChain G i) hd0 hdensR
  intro i hi v
  refine (hjoint i hi v).trans ?_
  calc (joint (elimBound G) ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ i).1
      ≤ (elimBound G + ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ i := joint_fst_le _ _ _
    _ ≤ (3 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ i :=
        Nat.pow_le_pow_left (by omega) _
    _ ≤ (3 * ⌈max c₀ 0 * (m : ℝ) ^ δ'⌉₊ + 2) ^ 16 ^ R :=
        Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hi)

/-- The cast of the raw bound: `(3·⌈c₀·X⌉₊ + 2)^P ≤ ((3c₀+5)·X)^P` for
`X ≥ 1` — the ceiling absorbed into the constant, the numeric step every
consumer of the raw form repeats. -/
private theorem dmax_cast_le {c₀ X : ℝ} (hc₀ : 0 ≤ c₀) (hX : 1 ≤ X) (P : ℕ) :
    (((3 * ⌈c₀ * X⌉₊ + 2) ^ P : ℕ) : ℝ) ≤ ((3 * c₀ + 5) * X) ^ P := by
  have hXnn : (0 : ℝ) ≤ X := zero_le_one.trans hX
  have hceil : ((⌈c₀ * X⌉₊ : ℕ) : ℝ) ≤ c₀ * X + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hc₀ hXnn)).le
  have hbase : ((3 * ⌈c₀ * X⌉₊ + 2 : ℕ) : ℝ) ≤ (3 * c₀ + 5) * X := by
    push_cast
    nlinarith [hceil, hX, hc₀]
  calc (((3 * ⌈c₀ * X⌉₊ + 2) ^ P : ℕ) : ℝ)
      = (((3 * ⌈c₀ * X⌉₊ + 2 : ℕ) : ℝ)) ^ P := by push_cast; ring
    _ ≤ ((3 * c₀ + 5) * X) ^ P := by gcongr

/-- `(m^(δ/P))^P = m^δ`: the inner exponent, undone. -/
private theorem rpow_div_pow (m P : ℕ) (hP : 0 < P) (δ : ℝ) :
    ((m : ℝ) ^ (δ / (P : ℝ))) ^ (P : ℕ) = (m : ℝ) ^ δ := by
  have hP0 : ((P : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [← Real.rpow_natCast ((m : ℝ) ^ (δ / (P : ℝ))) P,
    ← Real.rpow_mul (Nat.cast_nonneg m), div_mul_cancel₀ _ hP0]

/-- `1 ≤ m^ε` for `m ≥ 1`, `ε ≥ 0`. -/
private theorem one_le_rpow {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε) :
    (1 : ℝ) ≤ (m : ℝ) ^ ε := by
  calc (1 : ℝ) = (1 : ℝ) ^ ε := (Real.one_rpow _).symm
    _ ≤ (m : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hm) hε

/-- **The greedy chain's in-degree bound, on a class** — the
`⌈c·m^δ⌉₊` form: one constant, fixed before the graph, bounding the
in-degree of *every* round `i ≤ R` of the greedy chain on every
subgraph copy of every member.  This is the uniformization of the
landed `greedy_chain_joint_inDegLE` that the pricing consumes. -/
theorem exists_greedyChain_inDegLE (C : GraphClass) (hC : NowhereDense C)
    (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        ∀ i ≤ R, (greedyChain G i).InDegLE ⌈c * (m : ℝ) ^ δ⌉₊ := by
  have hPpos : 0 < (16 ^ R : ℕ) := by positivity
  have hδ' : 0 < δ / ((16 ^ R : ℕ) : ℝ) := div_pos hδ (by exact_mod_cast hPpos)
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_greedyChain_inDegLE_pow C hC R _ hδ'
  refine ⟨(3 * c₀ + 5) ^ (16 ^ R : ℕ), fun n Gn hGn m G hsub i hi v => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact v.elim0
  have h := hc₀ n Gn hGn m G hsub i hi v
  refine h.trans ?_
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ)) := one_le_rpow hm hδ'.le
  have hcast := dmax_cast_le hc₀0 hX1 (16 ^ R)
  have hXP := rpow_div_pow m (16 ^ R) hPpos δ
  have hfin : (((3 * ⌈c₀ * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))⌉₊ + 2) ^ 16 ^ R : ℕ) : ℝ)
      ≤ (3 * c₀ + 5) ^ (16 ^ R : ℕ) * (m : ℝ) ^ δ := by
    calc (((3 * ⌈c₀ * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))⌉₊ + 2) ^ 16 ^ R : ℕ) : ℝ)
        ≤ ((3 * c₀ + 5) * (m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))) ^ (16 ^ R : ℕ) := hcast
      _ = (3 * c₀ + 5) ^ (16 ^ R : ℕ)
            * ((m : ℝ) ^ (δ / ((16 ^ R : ℕ) : ℝ))) ^ (16 ^ R : ℕ) := mul_pow _ _ _
      _ = (3 * c₀ + 5) ^ (16 ^ R : ℕ) * (m : ℝ) ^ δ := by rw [hXP]
  exact_mod_cast hfin.trans (Nat.le_ceil _)

/-! ### The priced chain, on a class -/

/-- **The ordering phase's charge, bounded** — at the exponent it truly
has: on a nowhere dense class, `chainCharge ≤ f·m^{1+δ}`, with `f`
fixed before the graph.  This is the shape of GKS's own account of the
ordering (`g(r,ε)·n^{1+ε}`, gks tex:1460-1463); the interface's
`1 + 2δ` (the sweep's exponent) is a weakening
(`exists_chainCharge_le_double`). -/
theorem exists_chainCharge_le (C : GraphClass) (hC : NowhereDense C) (R : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (chainCharge G R : ℝ) ≤ f * (m : ℝ) ^ (1 + δ) := by
  have hPpos : 0 < (2 * 16 ^ R : ℕ) := by positivity
  have hδ' : 0 < δ / ((2 * 16 ^ R : ℕ) : ℝ) := div_pos hδ (by exact_mod_cast hPpos)
  obtain ⟨c₀, hc₀0, hc₀⟩ := exists_greedyChain_inDegLE_pow C hC R _ hδ'
  refine ⟨(4 * (5 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ), by positivity, ?_⟩
  intro n Gn hGn m G hsub
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [chainCharge_zero, Nat.cast_zero,
      Real.zero_rpow (by positivity : (1 : ℝ) + δ ≠ 0), mul_zero]
  -- the uniform in-degree bound of every round
  have huni := hc₀ n Gn hGn m G hsub
  set D₁ : ℕ := ⌈c₀ * (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))⌉₊ with hD₁def
  -- the ℕ-side total at that bound
  have hN := chainCharge_le_of_uniform huni
  set dmax : ℕ := (3 * D₁ + 2) ^ 16 ^ R with hdmaxdef
  have hd1 : 1 ≤ dmax := Nat.one_le_pow _ _ (by omega)
  have hsq : (dmax + 1) * (dmax + 1) ≤ 4 * ((3 * D₁ + 2) ^ (2 * 16 ^ R)) := by
    have h4 : (dmax + 1) * (dmax + 1) ≤ 4 * (dmax * dmax) := by nlinarith [hd1]
    have hdd : dmax * dmax = (3 * D₁ + 2) ^ (2 * 16 ^ R) := by
      rw [hdmaxdef, ← pow_add, two_mul]
    rwa [hdd] at h4
  have hN2 : chainCharge G R ≤ 4 * (5 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) := by
    calc chainCharge G R ≤ (5 * R + 8) * (m * ((dmax + 1) * (dmax + 1))) := hN
      _ ≤ (5 * R + 8) * (m * (4 * ((3 * D₁ + 2) ^ (2 * 16 ^ R)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsq)
      _ = 4 * (5 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) := by ring
  -- the ℝ-side massage
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hX1 : (1 : ℝ) ≤ (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ)) := one_le_rpow hm hδ'.le
  have hcast := dmax_cast_le hc₀0 hX1 (2 * 16 ^ R)
  have hXP := rpow_div_pow m (2 * 16 ^ R) hPpos δ
  calc (chainCharge G R : ℝ)
      ≤ ((4 * (5 * R + 8) * (m * (3 * D₁ + 2) ^ (2 * 16 ^ R)) : ℕ) : ℝ) := by
        exact_mod_cast hN2
    _ = (4 * (5 * R + 8) : ℝ) * ((m : ℝ) * (((3 * D₁ + 2) ^ (2 * 16 ^ R) : ℕ) : ℝ)) := by
        push_cast; ring
    _ ≤ (4 * (5 * R + 8) : ℝ) * ((m : ℝ)
          * ((3 * c₀ + 5) * (m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))) ^ (2 * 16 ^ R : ℕ)) := by
        rw [hD₁def]
        gcongr
    _ = (4 * (5 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ)
          * ((m : ℝ) * ((m : ℝ) ^ (δ / ((2 * 16 ^ R : ℕ) : ℝ))) ^ (2 * 16 ^ R : ℕ)) := by
        rw [mul_pow]; ring
    _ = (4 * (5 * R + 8) : ℝ) * (3 * c₀ + 5) ^ (2 * 16 ^ R : ℕ) * (m : ℝ) ^ (1 + δ) := by
        rw [hXP, Real.rpow_add hm0, Real.rpow_one]

/-- The charge bound in the interface's exponent: `chainCharge ≤
f·m^{1+2δ}` — `exists_chainCharge_le` weakened along
`m^{1+δ} ≤ m^{1+2δ}`.  This is the exact shape of
`CoverSpec.IsCoverOrdering.time`. -/
theorem exists_chainCharge_le_double (C : GraphClass) (hC : NowhereDense C) (R : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, 0 ≤ f ∧ ∀ (n : ℕ) (Gn : SimpleGraph (Fin n)), C n Gn →
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)), G ⊑ Gn →
        (chainCharge G R : ℝ) ≤ f * (m : ℝ) ^ (1 + 2 * δ) := by
  obtain ⟨f, hf0, hf⟩ := exists_chainCharge_le C hC R δ hδ
  refine ⟨f, hf0, fun n Gn hGn m G hsub => (hf n Gn hGn m G hsub).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ hf0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero, Real.zero_rpow (by positivity : (1 : ℝ) + δ ≠ 0),
      Real.zero_rpow (by positivity : (1 : ℝ) + 2 * δ ≠ 0)]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)

/-! ### The timed routine

`OrderingOutput.steps` is data, so the honest discharge is a *second*
routine, equal to F1's `greedyOrderingRoutine` in every field except
`steps` — which now carries `chainCharge` instead of the placeholder
`0`.  The four congruence identities are definitional, so the `data`
theorem is inherited rather than re-proved. -/

/-- **The greedy ordering routine, priced**: F1's routine with the
placeholder `steps := 0` replaced by the honest charge of the phase.
Chain, order and the two elimination bounds are *unchanged*. -/
noncomputable def timedGreedyRoutine (R : ℕ) : CoverSpec.OrderingRoutine :=
  fun m G => { greedyOrderingRoutine R m G with steps := (chainCharge G R : ℝ) }

/-- **The congruence with F1's routine**: every field except `steps`
is the placeholder routine's, definitionally.  This is what lets
`data` transfer without re-proof. -/
theorem timedGreedyRoutine_congr (R m : ℕ) (G : SimpleGraph (Fin m)) :
    ((timedGreedyRoutine R) m G).chain = ((greedyOrderingRoutine R) m G).chain ∧
    ((timedGreedyRoutine R) m G).order = ((greedyOrderingRoutine R) m G).order ∧
    ((timedGreedyRoutine R) m G).inDeg = ((greedyOrderingRoutine R) m G).inDeg ∧
    ((timedGreedyRoutine R) m G).backDeg = ((greedyOrderingRoutine R) m G).backDeg :=
  ⟨rfl, rfl, rfl, rfl⟩

@[simp] theorem timedGreedyRoutine_steps (R m : ℕ) (G : SimpleGraph (Fin m)) :
    ((timedGreedyRoutine R) m G).steps = (chainCharge G R : ℝ) := rfl

@[simp] theorem timedGreedyRoutine_order (R m : ℕ) (G : SimpleGraph (Fin m)) :
    ((timedGreedyRoutine R) m G).order = elimPerm (greedyChain G R).toGraph := rfl

/-- The `data` half, inherited across the congruence: the timed
routine's output satisfies the six-clause `AugChainData` postcondition
for every graph on every carrier — the same proof term as F1's, since
every field it speaks about is unchanged. -/
theorem timedGreedyRoutine_data (R : ℕ) :
    ∀ (m : ℕ) (G : SimpleGraph (Fin m)),
      AugChainData G ((timedGreedyRoutine R) m G).chain
        ((timedGreedyRoutine R) m G).order R
        ((timedGreedyRoutine R) m G).inDeg
        ((timedGreedyRoutine R) m G).backDeg :=
  fun m G => greedyOrderingRoutine_data R m G

/-! ### The discharge -/

/-- **Both halves of `IsCoverOrdering`, proved, for the priced
routine**: on a nowhere dense class, for every round count and every
`δ > 0` there is an `f` — fixed before the graph — such that the timed
greedy routine is a correct ordering phase (`data`, hypothesis-free
from F1) whose honest charge is at most `f·m^{1+2δ}` (`time`, the
charge bound above). -/
theorem isCoverOrdering_timedGreedyRoutine (C : GraphClass) (hC : NowhereDense C)
    (R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : ℝ, CoverSpec.IsCoverOrdering C R δ f (timedGreedyRoutine R) := by
  obtain ⟨f, _hf0, hf⟩ := exists_chainCharge_le_double C hC R δ hδ
  exact ⟨f, ⟨fun _n _Gn _hGn m G _hsub => timedGreedyRoutine_data R m G,
    fun n Gn hGn m G hsub => hf n Gn hGn m G hsub⟩⟩

/-- **The campaign's headline hypothesis, discharged**: every nowhere
dense class satisfies `CoverSpec.CoverOrderingTime` — for every round
count `R` and every `δ > 0` there are a constant and a routine, both
fixed before any graph is read, computing a correct `R`-round ordering
phase in at most `f·m^{1+2δ}` steps on every subgraph copy of every
member.  The witness is the *priced* greedy routine: its `steps` field
is the honest pipeline charge `chainCharge`, not a placeholder (module
docstring). -/
theorem coverOrderingTime_of_nowhereDense (C : GraphClass) (hC : NowhereDense C) :
    CoverSpec.CoverOrderingTime C := by
  intro R δ hδ
  obtain ⟨f, hf⟩ := isCoverOrdering_timedGreedyRoutine C hC R δ hδ
  exact ⟨f, timedGreedyRoutine R, hf⟩

end Lax3Proofs.Prog
