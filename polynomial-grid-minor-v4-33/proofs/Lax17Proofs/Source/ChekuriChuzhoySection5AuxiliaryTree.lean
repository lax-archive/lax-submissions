import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lax17Proofs.Source.ChekuriChuzhoySection5TerminalSkeleton
import Lax17Proofs.Source.SinghLauRounding

namespace Lax17Proofs

universe u v w

/-!
# Chekuri--Chuzhoy Section 5 auxiliary tree

This file formalizes Chekuri--Chuzhoy preprint Observation 5.16 and
Claim 5.17.  They appear as Observation 5.18 and Claim 5.19 in the journal
version (JACM 63(5), Article 40, Section 5.4.2).

The source multigraph `H` has vertex set `Fin m`, degree exactly `h` at every
vertex, and every nontrivial cut has at least `h` named edge copies.  The
simple graph `heavySupport H h` retains the pair `u, v` precisely when its
parallel bundle has rational cardinality at least `h / m^3`.  Its edge
capacity is that bundle cardinality.

The LP point below is the one displayed in Claim 5.17:

`x_e = ((m - 1) / m) * c(e) * (1 / C(u) + 1 / C(v))`.

The Singh--Lau rounding step is supplied by the axiom-free implementation in
`SinghLauRounding.lean`.
-/

namespace SimpleGraph

open Finset


namespace ChekuriChuzhoySection5TerminalSkeleton
namespace FiniteEdgeIndexedGraph

variable {W : Type u} [DecidableEq W]

/-- The unordered endpoint pair of a named multigraph edge. -/
def edgeKey (H : FiniteEdgeIndexedGraph W) (e : H.Edge) : Sym2 W :=
  s(H.left e, H.right e)

/-- All named copies having the same unordered endpoint pair. -/
noncomputable def edgeBundle
    (H : FiniteEdgeIndexedGraph W) (p : Sym2 W) : Finset H.Edge := by
  classical
  exact Finset.univ.filter fun e => H.edgeKey e = p

@[simp] theorem mem_edgeBundle
    (H : FiniteEdgeIndexedGraph W) {p : Sym2 W} {e : H.Edge} :
    e ∈ H.edgeBundle p ↔ H.edgeKey e = p := by
  simp [edgeBundle]

/-- Capacities in the auxiliary simple graph are parallel-bundle
cardinalities, coerced to `Rat` for the spanning-tree LP. -/
noncomputable def bundleCapacity
    (H : FiniteEdgeIndexedGraph W) (p : Sym2 W) : Rat :=
  (H.edgeBundle p).card

theorem bundleCapacity_nonnegative
    (H : FiniteEdgeIndexedGraph W) (p : Sym2 W) :
    0 ≤ H.bundleCapacity p := by
  unfold bundleCapacity
  positivity

/-- Named copies whose endpoint keys belong to `P`. -/
noncomputable def copiesOver
    (H : FiniteEdgeIndexedGraph W) (P : Finset (Sym2 W)) : Finset H.Edge := by
  classical
  exact Finset.univ.filter fun e => H.edgeKey e ∈ P

@[simp] theorem mem_copiesOver
    (H : FiniteEdgeIndexedGraph W) {P : Finset (Sym2 W)} {e : H.Edge} :
    e ∈ H.copiesOver P ↔ H.edgeKey e ∈ P := by
  simp [copiesOver]

/-- Bundle fibers partition all copies lying over a set of endpoint pairs. -/
theorem copiesOver_card_eq_sum_bundle_card
    (H : FiniteEdgeIndexedGraph W) (P : Finset (Sym2 W)) :
    (H.copiesOver P).card = ∑ p ∈ P, (H.edgeBundle p).card := by
  classical
  have hmap :
      ((H.copiesOver P : Finset H.Edge) : Set H.Edge).MapsTo
        H.edgeKey (P : Set (Sym2 W)) := by
    intro e he
    exact H.mem_copiesOver.mp he
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  ext e
  constructor
  · intro he
    exact H.mem_edgeBundle.mpr (Finset.mem_filter.mp he).2
  · intro he
    have hkey := H.mem_edgeBundle.mp he
    exact Finset.mem_filter.mpr
      ⟨H.mem_copiesOver.mpr (hkey ▸ hp), hkey⟩

theorem copiesOver_card_eq_sum_bundleCapacity
    (H : FiniteEdgeIndexedGraph W) (P : Finset (Sym2 W)) :
    ((H.copiesOver P).card : Rat) =
      ∑ p ∈ P, H.bundleCapacity p := by
  unfold bundleCapacity
  norm_cast
  exact H.copiesOver_card_eq_sum_bundle_card P

end FiniteEdgeIndexedGraph
end ChekuriChuzhoySection5TerminalSkeleton

namespace ChekuriChuzhoySection5AuxiliaryTree

open ChekuriChuzhoySection5TerminalSkeleton
open FiniteEdgeIndexedGraph

variable {m h : Nat}

/-- The source threshold `h / m^3`, interpreted in `Rat`. -/
def heavyThreshold (m h : Nat) : Rat :=
  (h : Rat) / (m : Rat) ^ 3

theorem heavyThreshold_pos (hm : 0 < m) (hh : 0 < h) :
    0 < heavyThreshold m h := by
  unfold heavyThreshold
  positivity

/-- Convert the rational heavy-edge threshold into the exact natural bundle
size consumed by the source-sharp Hall selection.  The heavy-support step
loses `m^3`, and selecting one representative per group loses one further
factor `m`. -/
theorem mul_width_le_bundleCard_of_heavy
    (H : FiniteEdgeIndexedGraph (Fin m)) (p : Sym2 (Fin m))
    {w : Nat} (hm : 0 < m)
    (hwidth : m ^ 4 * w ≤ h)
    (hheavy : heavyThreshold m h ≤ H.bundleCapacity p) :
    m * w ≤ (H.edgeBundle p).card := by
  have hden : (0 : Rat) < (m : Rat) ^ 3 := by
    positivity
  have hcapacityRat :
      (h : Rat) ≤ ((H.edgeBundle p).card : Rat) * (m : Rat) ^ 3 := by
    exact (div_le_iff₀ hden).mp (by
      simpa [heavyThreshold, FiniteEdgeIndexedGraph.bundleCapacity] using hheavy)
  have hcapacity :
      h ≤ (H.edgeBundle p).card * m ^ 3 := by
    exact_mod_cast hcapacityRat
  have hscaled :
      m ^ 3 * (m * w) ≤ m ^ 3 * (H.edgeBundle p).card := by
    calc
      m ^ 3 * (m * w) = m ^ 4 * w := by ring
      _ ≤ h := hwidth
      _ ≤ (H.edgeBundle p).card * m ^ 3 := hcapacity
      _ = m ^ 3 * (H.edgeBundle p).card := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos hm)

/-- The simple support of endpoint pairs carrying at least `h / m^3`
parallel copies. -/
noncomputable def heavySupport
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat) :
    _root_.SimpleGraph (Fin m) where
  Adj u v :=
    u ≠ v ∧ heavyThreshold m h ≤ H.bundleCapacity s(u, v)
  symm := by
    intro u v huv
    refine ⟨huv.1.symm, ?_⟩
    simpa [FiniteEdgeIndexedGraph.bundleCapacity, Sym2.eq_swap] using huv.2
  loopless := ⟨by
    intro v hv
    exact hv.1 rfl⟩

@[simp] theorem heavySupport_adj
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat) (u v : Fin m) :
    (heavySupport H h).Adj u v ↔
      u ≠ v ∧ heavyThreshold m h ≤ H.bundleCapacity s(u, v) :=
  Iff.rfl

/-- All unordered pairs containing `v`; the diagonal pair is harmless
because the source multigraph is loopless. -/
noncomputable def allPairsAt (v : Fin m) : Finset (Sym2 (Fin m)) := by
  classical
  exact Finset.univ.image fun u => s(v, u)

theorem allPairsAt_card_le (v : Fin m) :
    (allPairsAt v).card ≤ m := by
  classical
  exact (Finset.card_image_le.trans_eq (by simp))

theorem edgeKey_mem_allPairsAt_iff
    (H : FiniteEdgeIndexedGraph (Fin m)) (v : Fin m) (e : H.Edge) :
    H.edgeKey e ∈ allPairsAt v ↔ e ∈ H.incidentEdges v := by
  classical
  rw [H.mem_incidentEdges]
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨u, _hu, hkey⟩
    rcases Sym2.eq_iff.mp hkey with h | h
    · exact Or.inl h.1.symm
    · exact Or.inr h.1.symm
  · intro he
    rcases he with hleft | hright
    · apply Finset.mem_image.mpr
      refine ⟨H.right e, Finset.mem_univ _, ?_⟩
      simp [FiniteEdgeIndexedGraph.edgeKey, hleft]
    · apply Finset.mem_image.mpr
      refine ⟨H.left e, Finset.mem_univ _, ?_⟩
      simp [FiniteEdgeIndexedGraph.edgeKey, hright, Sym2.eq_swap]

theorem copiesOver_allPairsAt
    (H : FiniteEdgeIndexedGraph (Fin m)) (v : Fin m) :
    H.copiesOver (allPairsAt v) = H.incidentEdges v := by
  classical
  ext e
  simp [edgeKey_mem_allPairsAt_iff H v e]

/-- Heavy support edges incident with `v`. -/
noncomputable def heavyPairsAt
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat) (v : Fin m) :
    Finset (Sym2 (Fin m)) :=
  SimpleGraph.SinghLau.incidentEdges (heavySupport H h) v

theorem heavyPairsAt_subset_allPairsAt
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat) (v : Fin m) :
    heavyPairsAt H h v ⊆ allPairsAt v := by
  classical
  intro p hp
  have hvp : v ∈ p := (Finset.mem_filter.mp hp).2
  rcases Sym2.mem_iff_exists.mp hvp with ⟨u, rfl⟩
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

/-- Total retained capacity incident with a support vertex. -/
noncomputable def vertexCapacity
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat) (v : Fin m) : Rat :=
  ∑ p ∈ heavyPairsAt H h v, H.bundleCapacity p

/-- Whether an unordered pair crosses `S`. -/
def PairCrosses (S : Finset (Fin m)) : Sym2 (Fin m) → Prop :=
  Sym2.lift
    ⟨fun u v =>
      (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S), by
      intro u v
      exact propext (by tauto)⟩

@[simp] theorem pairCrosses_mk
    (S : Finset (Fin m)) (u v : Fin m) :
    PairCrosses S s(u, v) ↔
      (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
  simp [PairCrosses]

/-- Heavy support edges crossing `S`. -/
noncomputable def crossingPairs
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) : Finset (Sym2 (Fin m)) := by
  classical
  exact (heavySupport H h).edgeFinset.filter (PairCrosses S)

/-- Total retained capacity across `S`. -/
noncomputable def cutCapacity
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) : Rat :=
  ∑ p ∈ crossingPairs H h S, H.bundleCapacity p

/-- Every unordered pair crossing `S`, indexed once with its endpoint in
`S` first. -/
noncomputable def allCutPairs
    (S : Finset (Fin m)) : Finset (Sym2 (Fin m)) := by
  classical
  exact (S ×ˢ Sᶜ).image fun uv => s(uv.1, uv.2)

theorem allCutPairs_card_le_sq (S : Finset (Fin m)) :
    (allCutPairs S).card ≤ m ^ 2 := by
  classical
  calc
    (allCutPairs S).card ≤ (S ×ˢ Sᶜ).card :=
      Finset.card_image_le
    _ = S.card * Sᶜ.card := by rw [Finset.card_product]
    _ ≤ m * m := Nat.mul_le_mul
      (by simpa using Finset.card_le_univ S)
      (by simpa using Finset.card_le_univ Sᶜ)
    _ = m ^ 2 := by ring

theorem edgeKey_mem_allCutPairs_iff
    (H : FiniteEdgeIndexedGraph (Fin m))
    (S : Finset (Fin m)) (e : H.Edge) :
    H.edgeKey e ∈ allCutPairs S ↔ H.Crosses S e := by
  classical
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨uv, huv, hkey⟩
    have hu : uv.1 ∈ S := (Finset.mem_product.mp huv).1
    have hv : uv.2 ∈ Sᶜ := (Finset.mem_product.mp huv).2
    have hv' : uv.2 ∉ S := by simpa using hv
    rcases Sym2.eq_iff.mp hkey with h | h
    · exact Or.inl ⟨h.1.symm ▸ hu, h.2.symm ▸ hv'⟩
    · exact Or.inr ⟨h.1.symm ▸ hu, h.2.symm ▸ hv'⟩
  · intro he
    rcases he with h | h
    · apply Finset.mem_image.mpr
      refine ⟨(H.left e, H.right e), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨h.1, by simpa using h.2⟩
    · apply Finset.mem_image.mpr
      refine ⟨(H.right e, H.left e), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨h.1, by simpa using h.2⟩
      · exact Sym2.eq_swap

theorem copiesOver_allCutPairs
    (H : FiniteEdgeIndexedGraph (Fin m)) (S : Finset (Fin m)) :
    H.copiesOver (allCutPairs S) = H.boundary S := by
  classical
  ext e
  simp [edgeKey_mem_allCutPairs_iff H S e]

theorem crossingPairs_subset_allCutPairs
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) :
    crossingPairs H h S ⊆ allCutPairs S := by
  classical
  intro p hp
  have hcross : PairCrosses S p := (Finset.mem_filter.mp hp).2
  induction p using Sym2.inductionOn with
  | _ u v =>
      rcases (pairCrosses_mk S u v).mp hcross with huv | hvu
      · exact Finset.mem_image.mpr
          ⟨(u, v), Finset.mem_product.mpr
            ⟨huv.1, by simpa using huv.2⟩, rfl⟩
      · exact Finset.mem_image.mpr
          ⟨(v, u), Finset.mem_product.mpr
            ⟨hvu.1, by simpa using hvu.2⟩, Sym2.eq_swap⟩

private theorem edgeBundle_diag
    (H : FiniteEdgeIndexedGraph (Fin m)) (v : Fin m) :
    H.edgeBundle s(v, v) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he := H.mem_edgeBundle.mp he
  rcases Sym2.eq_iff.mp he with h | h
  · exact H.end_ne e (h.1.trans h.2.symm)
  · exact H.end_ne e (h.2.trans h.1.symm).symm

private theorem bundleCapacity_lt_of_mem_lightPairsAt
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 0 < m) (hh : 0 < h) (v : Fin m)
    {p : Sym2 (Fin m)}
    (hp : p ∈ allPairsAt v \ heavyPairsAt H h v) :
    H.bundleCapacity p < heavyThreshold m h := by
  classical
  rcases Finset.mem_image.mp (Finset.mem_sdiff.mp hp).1 with
    ⟨u, _hu, hpu⟩
  subst p
  by_cases huv : v = u
  · subst u
    rw [FiniteEdgeIndexedGraph.bundleCapacity, edgeBundle_diag]
    simpa using heavyThreshold_pos hm hh
  · apply lt_of_not_ge
    intro hlarge
    apply (Finset.mem_sdiff.mp hp).2
    apply Finset.mem_filter.mpr
    constructor
    · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
        ((heavySupport_adj H h v u).2 ⟨huv, hlarge⟩)
    · simp

private theorem bundleCapacity_lt_of_mem_lightCutPairs
    (H : FiniteEdgeIndexedGraph (Fin m))
    (S : Finset (Fin m))
    {p : Sym2 (Fin m)}
    (hp : p ∈ allCutPairs S \ crossingPairs H h S) :
    H.bundleCapacity p < heavyThreshold m h := by
  classical
  rcases Finset.mem_image.mp (Finset.mem_sdiff.mp hp).1 with
    ⟨uv, huv, hpuv⟩
  have hu : uv.1 ∈ S := (Finset.mem_product.mp huv).1
  have hv : uv.2 ∉ S := by
    simpa using (Finset.mem_product.mp huv).2
  have huv_ne : uv.1 ≠ uv.2 := by
    intro huv_eq
    exact hv (huv_eq ▸ hu)
  subst p
  apply lt_of_not_ge
  intro hlarge
  apply (Finset.mem_sdiff.mp hp).2
  apply Finset.mem_filter.mpr
  constructor
  · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
      ((heavySupport_adj H h uv.1 uv.2).2 ⟨huv_ne, hlarge⟩)
  · exact (pairCrosses_mk S uv.1 uv.2).2 (Or.inl ⟨hu, hv⟩)

private theorem sum_bundleCapacity_lt_of_card_le
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 0 < m) (hh : 0 < h)
    (P : Finset (Sym2 (Fin m))) (b : Nat)
    (hb : 0 < b)
    (hcard : P.card ≤ b)
    (hsmall : ∀ p ∈ P, H.bundleCapacity p < heavyThreshold m h) :
    (∑ p ∈ P, H.bundleCapacity p) <
      (b : Rat) * heavyThreshold m h := by
  classical
  have hthreshold_pos := heavyThreshold_pos hm hh
  by_cases hP : P.Nonempty
  · calc
      (∑ p ∈ P, H.bundleCapacity p) <
          ∑ _p ∈ P, heavyThreshold m h :=
        Finset.sum_lt_sum_of_nonempty hP hsmall
      _ = (P.card : Rat) * heavyThreshold m h := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (b : Rat) * heavyThreshold m h := by
        gcongr
  · have hPempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    simp [hPempty, hthreshold_pos, Nat.cast_pos.mpr hb]

private theorem cast_m_mul_threshold
    (hm : 0 < m) :
    (m : Rat) * heavyThreshold m h = (h : Rat) / (m : Rat) ^ 2 := by
  unfold heavyThreshold
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

private theorem cast_m_sq_mul_threshold
    (hm : 0 < m) :
    ((m ^ 2 : Nat) : Rat) * heavyThreshold m h =
      (h : Rat) / (m : Rat) := by
  unfold heavyThreshold
  norm_num [Nat.cast_pow]
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

/-- Observation 5.16, first bullet (journal Observation 5.18):
retained incident capacity lies between `(1 - 1/m^2)h` and `h`. -/
theorem observation516_vertexCapacity
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h) (v : Fin m) :
    (1 - 1 / (m : Rat) ^ 2) * (h : Rat) ≤
        vertexCapacity H h v ∧
      vertexCapacity H h v ≤ (h : Rat) := by
  classical
  let A := allPairsAt v
  let P := heavyPairsAt H h v
  let L := A \ P
  have hmpos : 0 < m := lt_of_lt_of_le (by omega) hm
  have hPA : P ⊆ A := heavyPairsAt_subset_allPairsAt H h v
  have htotal : (∑ p ∈ A, H.bundleCapacity p) = (h : Rat) := by
    rw [← H.copiesOver_card_eq_sum_bundleCapacity A]
    rw [show H.copiesOver A = H.incidentEdges v by
      simpa [A] using copiesOver_allPairsAt H v]
    exact_mod_cast (by
      simpa [FiniteEdgeIndexedGraph.degree] using hdegree v)
  have hlight :
      (∑ p ∈ L, H.bundleCapacity p) <
        (m : Rat) * heavyThreshold m h := by
    apply sum_bundleCapacity_lt_of_card_le H hmpos hh L m hmpos
    · exact (Finset.card_le_card Finset.sdiff_subset).trans (by
        simpa [A] using allPairsAt_card_le v)
    · intro p hp
      exact bundleCapacity_lt_of_mem_lightPairsAt H hmpos hh v
        (by simpa [L, A, P] using hp)
  have hsplit :
      (∑ p ∈ L, H.bundleCapacity p) +
          vertexCapacity H h v =
        ∑ p ∈ A, H.bundleCapacity p := by
    simpa [L, P, vertexCapacity] using
      (Finset.sum_sdiff hPA
        (f := fun p => H.bundleCapacity p))
  have hlight_nonnegative :
      0 ≤ ∑ p ∈ L, H.bundleCapacity p := by
    exact Finset.sum_nonneg fun p _hp => H.bundleCapacity_nonnegative p
  constructor
  · have hlower :
        (1 - 1 / (m : Rat) ^ 2) * (h : Rat) =
          (h : Rat) - (h : Rat) / (m : Rat) ^ 2 := by
      field_simp [Nat.cast_ne_zero.mpr hmpos.ne']
    rw [cast_m_mul_threshold (h := h) hmpos] at hlight
    rw [hlower]
    rw [htotal] at hsplit
    linarith
  · rw [htotal] at hsplit
    linarith

/-- Observation 5.16, second bullet in capacitated cut form.  By finite
max-flow/min-cut this is exactly the source's pairwise flow assertion. -/
theorem observation516_cutCapacity
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hconnected : H.IsEdgeConnected h)
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (hSproper : S ≠ Finset.univ) :
    (1 - 1 / (m : Rat)) * (h : Rat) ≤ cutCapacity H h S := by
  classical
  let A := allCutPairs S
  let P := crossingPairs H h S
  let L := A \ P
  have hmpos : 0 < m := lt_of_lt_of_le (by omega) hm
  have hPA : P ⊆ A := crossingPairs_subset_allCutPairs H h S
  have htotal :
      (h : Rat) ≤ ∑ p ∈ A, H.bundleCapacity p := by
    rw [← H.copiesOver_card_eq_sum_bundleCapacity A]
    rw [show H.copiesOver A = H.boundary S by
      simpa [A] using copiesOver_allCutPairs H S]
    exact_mod_cast hconnected S hS hSproper
  have hlight :
      (∑ p ∈ L, H.bundleCapacity p) <
        ((m ^ 2 : Nat) : Rat) * heavyThreshold m h := by
    apply sum_bundleCapacity_lt_of_card_le H hmpos hh L (m ^ 2) (by positivity)
    · exact (Finset.card_le_card Finset.sdiff_subset).trans (by
        simpa [A] using allCutPairs_card_le_sq S)
    · intro p hp
      exact bundleCapacity_lt_of_mem_lightCutPairs H S
        (by simpa [L, A, P] using hp)
  have hsplit :
      (∑ p ∈ L, H.bundleCapacity p) +
          cutCapacity H h S =
        ∑ p ∈ A, H.bundleCapacity p := by
    simpa [L, P, cutCapacity] using
      (Finset.sum_sdiff hPA
        (f := fun p => H.bundleCapacity p))
  have hlower :
      (1 - 1 / (m : Rat)) * (h : Rat) =
        (h : Rat) - (h : Rat) / (m : Rat) := by
    field_simp [Nat.cast_ne_zero.mpr hmpos.ne']
  rw [cast_m_sq_mul_threshold (h := h) hmpos] at hlight
  rw [hlower]
  linarith

/-! ## The explicit Claim 5.17 LP point -/

/-- The common factor `(m - 1) / m` in the paper's LP point. -/
def treeScale (m : Nat) : Rat :=
  ((m : Rat) - 1) / (m : Rat)

theorem treeScale_pos (hm : 2 ≤ m) :
    0 < treeScale m := by
  unfold treeScale
  apply div_pos
  · have hmRat : (2 : Rat) ≤ m := by exact_mod_cast hm
    linarith
  · exact_mod_cast (by omega : 0 < m)

theorem treeScale_nonnegative (hm : 2 ≤ m) :
    0 ≤ treeScale m :=
  (treeScale_pos hm).le

theorem treeScale_le_one (hm : 0 < m) :
    treeScale m ≤ 1 := by
  unfold treeScale
  apply (div_le_iff₀ (by exact_mod_cast hm)).2
  linarith

theorem treeScale_mul_card (hm : 0 < m) :
    treeScale m * (m : Rat) = (m : Rat) - 1 := by
  unfold treeScale
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

private theorem treeScale_le_observationCoefficient (hm : 2 ≤ m) :
    treeScale m ≤ 1 - 1 / (m : Rat) ^ 2 := by
  have hmpos : 0 < m := by omega
  unfold treeScale
  field_simp [Nat.cast_ne_zero.mpr hmpos.ne']
  have hmrat : (2 : Rat) ≤ m := by exact_mod_cast hm
  nlinarith

theorem treeScale_mul_h_le_vertexCapacity
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h) (v : Fin m) :
    treeScale m * (h : Rat) ≤ vertexCapacity H h v := by
  have hcoefficient := treeScale_le_observationCoefficient (m := m) hm
  have hcast : (0 : Rat) ≤ h := by positivity
  exact
    (mul_le_mul_of_nonneg_right hcoefficient hcast).trans
      (observation516_vertexCapacity H hm hh hdegree v).1

theorem vertexCapacity_pos
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h) (v : Fin m) :
    0 < vertexCapacity H h v := by
  have hscale := treeScale_pos (m := m) hm
  have hhRat : (0 : Rat) < h := by exact_mod_cast hh
  exact lt_of_lt_of_le (mul_pos hscale hhRat)
    (treeScale_mul_h_le_vertexCapacity H hm hh hdegree v)

/-- The normalized contribution of endpoint `v` to the LP value of `p`. -/
noncomputable def normalizedEndpoint
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (p : Sym2 (Fin m)) (v : Fin m) : Rat :=
  H.bundleCapacity p / vertexCapacity H h v

/-- The rational point displayed in Claim 5.17. -/
noncomputable def claim517Weight
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (p : Sym2 (Fin m)) : Rat :=
  treeScale m *
    ∑ v ∈ p.toFinset, normalizedEndpoint H h p v

/-- Swap an edge/end-point sum after restricting endpoints to `S`. -/
private theorem sum_endpoint_restrict_swap
    {V : Type u} [Fintype V] [DecidableEq V]
    (P : Finset (Sym2 V)) (S : Finset V) (f : Sym2 V → V → Rat) :
    (∑ p ∈ P, ∑ v ∈ p.toFinset.filter (fun v => v ∈ S), f p v) =
      ∑ v ∈ S, ∑ p ∈ P.filter (fun p => v ∈ p), f p v := by
  classical
  calc
    (∑ p ∈ P, ∑ v ∈ p.toFinset.filter (fun v => v ∈ S), f p v) =
        ∑ p ∈ P, ∑ v ∈ S, if v ∈ p then f p v else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [show p.toFinset.filter (fun v => v ∈ S) =
          S.filter (fun v => v ∈ p) by
        ext v
        simp [Sym2.mem_toFinset, and_comm]]
      simpa using
        (Finset.sum_filter
          (s := S) (p := fun v => v ∈ p) (f := fun v => f p v))
    _ = ∑ v ∈ S, ∑ p ∈ P, if v ∈ p then f p v else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ v ∈ S, ∑ p ∈ P.filter (fun p => v ∈ p), f p v := by
      apply Finset.sum_congr rfl
      intro v _hv
      simpa using
        (Finset.sum_filter
          (s := P) (p := fun p => v ∈ p) (f := fun p => f p v)).symm

private theorem sum_normalizedEndpoint_heavyPairsAt
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h) (v : Fin m) :
    (∑ p ∈ heavyPairsAt H h v, normalizedEndpoint H h p v) = 1 := by
  unfold normalizedEndpoint vertexCapacity
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (vertexCapacity_pos H hm hh hdegree v))

theorem claim517Weight_nonnegative
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (p : Sym2 (Fin m)) :
    0 ≤ claim517Weight H h p := by
  unfold claim517Weight
  apply mul_nonneg (treeScale_nonnegative hm)
  apply Finset.sum_nonneg
  intro v _hv
  unfold normalizedEndpoint
  exact div_nonneg (H.bundleCapacity_nonnegative p)
    (vertexCapacity_pos H hm hh hdegree v).le

theorem claim517Weight_total
    (H : FiniteEdgeIndexedGraph (Fin m))
    [Fintype (heavySupport H h).edgeSet]
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h) :
    (∑ p ∈ (heavySupport H h).edgeFinset, claim517Weight H h p) =
      (m : Rat) - 1 := by
  classical
  let Z := heavySupport H h
  have hswap :=
    sum_endpoint_restrict_swap
      (P := Z.edgeFinset) (S := (Finset.univ : Finset (Fin m)))
      (f := normalizedEndpoint H h)
  have hendpoint :
      (∑ p ∈ Z.edgeFinset,
          ∑ v ∈ p.toFinset, normalizedEndpoint H h p v) =
        (m : Rat) := by
    have hincident :
        ∀ v : Fin m,
          Z.edgeFinset.filter (fun p => v ∈ p) =
            heavyPairsAt H h v := by
      intro v
      ext p
      simp [Z, heavyPairsAt, SimpleGraph.SinghLau.incidentEdges,
        SimpleGraph.mem_edgeFinset]
    have hswap' :
        (∑ p ∈ Z.edgeFinset,
            ∑ v ∈ p.toFinset, normalizedEndpoint H h p v) =
          ∑ v : Fin m,
            ∑ p ∈ heavyPairsAt H h v,
              normalizedEndpoint H h p v := by
      calc
        (∑ p ∈ Z.edgeFinset,
            ∑ v ∈ p.toFinset, normalizedEndpoint H h p v) =
            ∑ v : Fin m,
              ∑ p ∈ Z.edgeFinset.filter (fun p => v ∈ p),
                normalizedEndpoint H h p v := by
          simpa using hswap
        _ = ∑ v : Fin m,
              ∑ p ∈ heavyPairsAt H h v,
                normalizedEndpoint H h p v := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [hincident v]
    rw [hswap']
    calc
      (∑ v : Fin m,
          ∑ p ∈ heavyPairsAt H h v,
            normalizedEndpoint H h p v) =
          ∑ _v : Fin m, (1 : Rat) := by
        apply Finset.sum_congr rfl
        intro v _hv
        exact sum_normalizedEndpoint_heavyPairsAt H hm hh hdegree v
      _ = (m : Rat) := by simp
  unfold claim517Weight
  rw [← Finset.mul_sum]
  have hendpoint' :
      (∑ p ∈ (heavySupport H h).edgeFinset,
          ∑ v ∈ p.toFinset, normalizedEndpoint H h p v) =
        (m : Rat) := by
    simpa [Z] using hendpoint
  exact
    (congrArg (fun x : Rat => treeScale m * x) hendpoint').trans
      (treeScale_mul_card (m := m) (by omega))

private theorem treeScale_mul_normalizedEndpoint_le_bundle_div_h
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (p : Sym2 (Fin m)) (v : Fin m) :
    treeScale m * normalizedEndpoint H h p v ≤
      H.bundleCapacity p / (h : Rat) := by
  have hcapacity_pos := vertexCapacity_pos H hm hh hdegree v
  have hhRat : (0 : Rat) < h := by exact_mod_cast hh
  have hratio :
      treeScale m / vertexCapacity H h v ≤ 1 / (h : Rat) := by
    apply (div_le_div_iff₀ hcapacity_pos hhRat).2
    simpa using treeScale_mul_h_le_vertexCapacity H hm hh hdegree v
  unfold normalizedEndpoint
  calc
    treeScale m * (H.bundleCapacity p / vertexCapacity H h v) =
        H.bundleCapacity p *
          (treeScale m / vertexCapacity H h v) := by ring
    _ ≤ H.bundleCapacity p * (1 / (h : Rat)) :=
      mul_le_mul_of_nonneg_left hratio (H.bundleCapacity_nonnegative p)
    _ = H.bundleCapacity p / (h : Rat) := by ring

private theorem claim517Weight_le_at_incident
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    {p : Sym2 (Fin m)} {v : Fin m}
    (hp : p ∈ heavyPairsAt H h v) :
    claim517Weight H h p ≤
      treeScale m * normalizedEndpoint H h p v +
        H.bundleCapacity p / (h : Rat) := by
  classical
  have hpEdge :
      p ∈ (heavySupport H h).edgeSet :=
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp hp).1
  have hvp : v ∈ p := (Finset.mem_filter.mp hp).2
  have hvFinset : v ∈ p.toFinset := Sym2.mem_toFinset.mpr hvp
  have hpCard : p.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag p
      ((heavySupport H h).not_isDiag_of_mem_edgeSet hpEdge)
  have heraseCard : (p.toFinset.erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hvFinset, hpCard]
  have hother :
      treeScale m *
          (∑ u ∈ p.toFinset.erase v, normalizedEndpoint H h p u) ≤
        H.bundleCapacity p / (h : Rat) := by
    calc
      treeScale m *
          (∑ u ∈ p.toFinset.erase v, normalizedEndpoint H h p u) =
          ∑ u ∈ p.toFinset.erase v,
            treeScale m * normalizedEndpoint H h p u := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _u ∈ p.toFinset.erase v,
          H.bundleCapacity p / (h : Rat) := by
        apply Finset.sum_le_sum
        intro u _hu
        exact
          treeScale_mul_normalizedEndpoint_le_bundle_div_h
            H hm hh hdegree p u
      _ = H.bundleCapacity p / (h : Rat) := by
        simp [heraseCard, Finset.sum_const]
  have hsum :
      (∑ u ∈ p.toFinset, normalizedEndpoint H h p u) =
        normalizedEndpoint H h p v +
          ∑ u ∈ p.toFinset.erase v, normalizedEndpoint H h p u := by
    rw [← Finset.sum_erase_add _ _ hvFinset]
    ring
  unfold claim517Weight
  rw [hsum, mul_add]
  linarith

/-- The fractional degree of the explicit point is at most two. -/
theorem claim517Weight_degree
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h) (v : Fin m) :
    (∑ p ∈ heavyPairsAt H h v, claim517Weight H h p) ≤ 2 := by
  have hbound :
      (∑ p ∈ heavyPairsAt H h v, claim517Weight H h p) ≤
        ∑ p ∈ heavyPairsAt H h v,
          (treeScale m * normalizedEndpoint H h p v +
            H.bundleCapacity p / (h : Rat)) := by
    apply Finset.sum_le_sum
    intro p hp
    exact claim517Weight_le_at_incident H hm hh hdegree hp
  have hnormalized :=
    sum_normalizedEndpoint_heavyPairsAt H hm hh hdegree v
  have hcapacityUpper :=
    (observation516_vertexCapacity H hm hh hdegree v).2
  have hhRat : (0 : Rat) < h := by exact_mod_cast hh
  have hright :
      (∑ p ∈ heavyPairsAt H h v,
          (treeScale m * normalizedEndpoint H h p v +
            H.bundleCapacity p / (h : Rat))) ≤ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hnormalized,
      mul_one, ← Finset.sum_div]
    change
      treeScale m + vertexCapacity H h v / (h : Rat) ≤ 2
    have hscale := treeScale_le_one (m := m) (by omega)
    have hquotient : vertexCapacity H h v / (h : Rat) ≤ 1 := by
      exact (div_le_one hhRat).2 hcapacityUpper
    linarith
  exact hbound.trans hright

/-! ### Forest inequalities -/

/-- Normalized endpoint mass on support edges internal to `S`. -/
noncomputable def internalNormalizedMass
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) : Rat :=
  ∑ p ∈ SimpleGraph.SinghLau.internalEdges (heavySupport H h) S,
    ∑ v ∈ p.toFinset, normalizedEndpoint H h p v

/-- Normalized endpoint mass contributed on the `S` side of the support
boundary. -/
noncomputable def cutInsideNormalizedMass
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) : Rat :=
  ∑ p ∈ crossingPairs H h S,
    ∑ v ∈ p.toFinset.filter (fun v => v ∈ S),
      normalizedEndpoint H h p v

private theorem pairInside_filter_eq
    (S : Finset (Fin m)) (p : Sym2 (Fin m))
    (hp : SimpleGraph.SinghLau.PairInside S p) :
    p.toFinset.filter (fun v => v ∈ S) = p.toFinset := by
  classical
  induction p using Sym2.inductionOn with
  | _ u v =>
      have hp' := (SimpleGraph.SinghLau.pairInside_mk S u v).mp hp
      ext x
      constructor
      · exact fun hx => (Finset.mem_filter.mp hx).1
      · intro hx
        apply Finset.mem_filter.mpr
        refine ⟨hx, ?_⟩
        have hx' : x = u ∨ x = v := by
          simpa [Sym2.toFinset_mk_eq] using hx
        rcases hx' with rfl | rfl
        · exact hp'.1
        · exact hp'.2

private theorem pairCrosses_iff_not_pairInside_of_mem
    (S : Finset (Fin m)) {v : Fin m} {p : Sym2 (Fin m)}
    (hv : v ∈ S) (hvp : v ∈ p) :
    PairCrosses S p ↔ ¬SimpleGraph.SinghLau.PairInside S p := by
  induction p using Sym2.inductionOn with
  | _ a b =>
      have hvp' : v = a ∨ v = b := by simpa using hvp
      rcases hvp' with rfl | rfl
      · simp [PairCrosses, SimpleGraph.SinghLau.PairInside, hv]
      · simp [PairCrosses, SimpleGraph.SinghLau.PairInside, hv]

private noncomputable def insideHeavyPairsAt
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) (v : Fin m) : Finset (Sym2 (Fin m)) := by
  classical
  exact (heavyPairsAt H h v).filter
    (SimpleGraph.SinghLau.PairInside S)

private noncomputable def outsideHeavyPairsAt
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) (v : Fin m) : Finset (Sym2 (Fin m)) := by
  classical
  exact (heavyPairsAt H h v).filter
    (fun p => ¬SimpleGraph.SinghLau.PairInside S p)

private theorem internalIncident_eq
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) (v : Fin m) :
    (SimpleGraph.SinghLau.internalEdges (heavySupport H h) S).filter
        (fun p => v ∈ p) =
      insideHeavyPairsAt H h S v := by
  classical
  unfold insideHeavyPairsAt
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hpInternal := Finset.mem_filter.mp hp'.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact SimpleGraph.mem_edgeFinset.mpr
          (SimpleGraph.mem_edgeFinset.mp hpInternal.1)
      · exact hp'.2
    · exact hpInternal.2
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hpIncident := Finset.mem_filter.mp hp'.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact SimpleGraph.mem_edgeFinset.mpr
          (SimpleGraph.mem_edgeFinset.mp hpIncident.1)
      · exact hp'.2
    · exact hpIncident.2

private theorem crossingIncident_eq
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) {v : Fin m} (hv : v ∈ S) :
    (crossingPairs H h S).filter (fun p => v ∈ p) =
      outsideHeavyPairsAt H h S v := by
  classical
  unfold outsideHeavyPairsAt
  ext p
  constructor
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hpCross := Finset.mem_filter.mp hp'.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact SimpleGraph.mem_edgeFinset.mpr
          (SimpleGraph.mem_edgeFinset.mp hpCross.1)
      · exact hp'.2
    · exact
        (pairCrosses_iff_not_pairInside_of_mem S hv hp'.2).mp hpCross.2
  · intro hp
    have hp' := Finset.mem_filter.mp hp
    have hpIncident := Finset.mem_filter.mp hp'.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact SimpleGraph.mem_edgeFinset.mpr
          (SimpleGraph.mem_edgeFinset.mp hpIncident.1)
      · exact
          (pairCrosses_iff_not_pairInside_of_mem S hv hpIncident.2).mpr hp'.2
    · exact hpIncident.2

private theorem internalNormalizedMass_swap
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) :
    internalNormalizedMass H h S =
      ∑ v ∈ S,
        ∑ p ∈
          (SimpleGraph.SinghLau.internalEdges
            (heavySupport H h) S).filter (fun p => v ∈ p),
          normalizedEndpoint H h p v := by
  classical
  unfold internalNormalizedMass
  calc
    (∑ p ∈ SimpleGraph.SinghLau.internalEdges (heavySupport H h) S,
        ∑ v ∈ p.toFinset, normalizedEndpoint H h p v) =
        ∑ p ∈ SimpleGraph.SinghLau.internalEdges (heavySupport H h) S,
          ∑ v ∈ p.toFinset.filter (fun v => v ∈ S),
            normalizedEndpoint H h p v := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pairInside_filter_eq S p (Finset.mem_filter.mp hp).2]
    _ = _ :=
      sum_endpoint_restrict_swap
        (P := SimpleGraph.SinghLau.internalEdges (heavySupport H h) S)
        (S := S) (f := normalizedEndpoint H h)

private theorem cutInsideNormalizedMass_swap
    (H : FiniteEdgeIndexedGraph (Fin m)) (h : Nat)
    (S : Finset (Fin m)) :
    cutInsideNormalizedMass H h S =
      ∑ v ∈ S,
        ∑ p ∈ (crossingPairs H h S).filter (fun p => v ∈ p),
          normalizedEndpoint H h p v := by
  exact
    sum_endpoint_restrict_swap
      (P := crossingPairs H h S) (S := S)
      (f := normalizedEndpoint H h)

/-- Full normalized incident mass at vertices of `S` partitions into
internal mass and the contribution from the `S` side of the cut. -/
theorem internalNormalizedMass_add_cutInside
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (S : Finset (Fin m)) :
    internalNormalizedMass H h S + cutInsideNormalizedMass H h S =
      (S.card : Rat) := by
  classical
  rw [internalNormalizedMass_swap, cutInsideNormalizedMass_swap,
    ← Finset.sum_add_distrib]
  calc
    (∑ v ∈ S,
        ((∑ p ∈
            (SimpleGraph.SinghLau.internalEdges
              (heavySupport H h) S).filter (fun p => v ∈ p),
              normalizedEndpoint H h p v) +
          ∑ p ∈ (crossingPairs H h S).filter (fun p => v ∈ p),
              normalizedEndpoint H h p v)) =
        ∑ _v ∈ S, (1 : Rat) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [internalIncident_eq H h S v, crossingIncident_eq H h S hv]
      unfold insideHeavyPairsAt outsideHeavyPairsAt
      rw [Finset.sum_filter_add_sum_filter_not]
      exact sum_normalizedEndpoint_heavyPairsAt H hm hh hdegree v
    _ = (S.card : Rat) := by simp

private theorem bundle_div_h_le_normalizedEndpoint
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (p : Sym2 (Fin m)) (v : Fin m) :
    H.bundleCapacity p / (h : Rat) ≤ normalizedEndpoint H h p v := by
  have hhRat : (0 : Rat) < h := by exact_mod_cast hh
  have hcapacityPos := vertexCapacity_pos H hm hh hdegree v
  have hcapacityUpper :=
    (observation516_vertexCapacity H hm hh hdegree v).2
  unfold normalizedEndpoint
  apply (div_le_div_iff₀ hhRat hcapacityPos).2
  exact mul_le_mul_of_nonneg_left hcapacityUpper
    (H.bundleCapacity_nonnegative p)

private theorem bundle_div_h_le_cutInside_term
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (S : Finset (Fin m)) {p : Sym2 (Fin m)}
    (hp : p ∈ crossingPairs H h S) :
    H.bundleCapacity p / (h : Rat) ≤
      ∑ v ∈ p.toFinset.filter (fun v => v ∈ S),
        normalizedEndpoint H h p v := by
  classical
  induction p using Sym2.inductionOn with
  | _ a b =>
      have hp' := Finset.mem_filter.mp hp
      have hadj : (heavySupport H h).Adj a b := by
        exact (SimpleGraph.mem_edgeSet (G := heavySupport H h)).mp
          (SimpleGraph.mem_edgeFinset.mp hp'.1)
      have hab : a ≠ b := hadj.ne
      rcases (pairCrosses_mk S a b).mp hp'.2 with hcross | hcross
      · have hratio :=
          bundle_div_h_le_normalizedEndpoint H hm hh hdegree s(a, b) a
        have hfilter :
            ({a, b} : Finset (Fin m)).filter (fun v => v ∈ S) = {a} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨hxab, hxS⟩
            rcases hxab with hxa | hxb
            · exact hxa
            · subst x
              exact (hcross.2 hxS).elim
          · intro hxa
            subst x
            exact ⟨Or.inl rfl, hcross.1⟩
        rw [Sym2.toFinset_mk_eq, hfilter]
        simpa using hratio
      · have hratio :=
          bundle_div_h_le_normalizedEndpoint H hm hh hdegree s(a, b) b
        have hfilter :
            ({a, b} : Finset (Fin m)).filter (fun v => v ∈ S) = {b} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨hxab, hxS⟩
            rcases hxab with hxa | hxb
            · subst x
              exact (hcross.2 hxS).elim
            · exact hxb
          · intro hxb
            subst x
            exact ⟨Or.inr rfl, hcross.1⟩
        rw [Sym2.toFinset_mk_eq, hfilter]
        simpa using hratio

theorem cutCapacity_div_h_le_cutInsideNormalizedMass
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (S : Finset (Fin m)) :
    cutCapacity H h S / (h : Rat) ≤
      cutInsideNormalizedMass H h S := by
  unfold cutCapacity cutInsideNormalizedMass
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  exact bundle_div_h_le_cutInside_term H hm hh hdegree S hp

private theorem treeScale_eq_one_sub_inv (hm : 0 < m) :
    treeScale m = 1 - 1 / (m : Rat) := by
  unfold treeScale
  field_simp [Nat.cast_ne_zero.mpr hm.ne']

theorem treeScale_le_cutInsideNormalizedMass
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (hconnected : H.IsEdgeConnected h)
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (hSproper : S ≠ Finset.univ) :
    treeScale m ≤ cutInsideNormalizedMass H h S := by
  have hmpos : 0 < m := by omega
  have hcut := observation516_cutCapacity H hm hh hconnected S hS hSproper
  rw [← treeScale_eq_one_sub_inv (m := m) hmpos] at hcut
  have hhRat : (0 : Rat) < h := by exact_mod_cast hh
  have hscaled : treeScale m ≤ cutCapacity H h S / (h : Rat) :=
    (le_div_iff₀ hhRat).2 hcut
  exact hscaled.trans
    (cutCapacity_div_h_le_cutInsideNormalizedMass H hm hh hdegree S)

private theorem internalEdges_eq_empty_of_card_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (Z : _root_.SimpleGraph V) (S : Finset V)
    (hcard : S.card ≤ 1) :
    SimpleGraph.SinghLau.internalEdges Z S = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  induction p using Sym2.inductionOn with
  | _ a b =>
      have hadj : Z.Adj a b :=
        (SimpleGraph.mem_edgeSet (G := Z)).mp
          (SimpleGraph.mem_edgeFinset.mp hp'.1)
      have habInside :=
        (SimpleGraph.SinghLau.pairInside_mk S a b).mp hp'.2
      have hab : a = b :=
        (Finset.card_le_one_iff.mp hcard) habInside.1 habInside.2
      exact hadj.ne hab

private theorem treeScale_forest_arithmetic
    (hm : 2 ≤ m) {s : Nat} (hs : 2 ≤ s) :
    treeScale m * ((s : Rat) - treeScale m) ≤ (s : Rat) - 1 := by
  have hmpos : 0 < m := by omega
  have hmRat : (2 : Rat) ≤ m := by exact_mod_cast hm
  have hsRat : (2 : Rat) ≤ s := by exact_mod_cast hs
  unfold treeScale
  field_simp [Nat.cast_ne_zero.mpr hmpos.ne']
  nlinarith

/-- Constraint (3) of the spanning-tree LP for the explicit Claim 5.17
point. -/
theorem claim517Weight_forest
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (hconnected : H.IsEdgeConnected h)
    (S : Finset (Fin m)) (hSproper : S ≠ Finset.univ) :
    (∑ p ∈
        SimpleGraph.SinghLau.internalEdges (heavySupport H h) S,
        claim517Weight H h p) ≤ (S.card - 1 : Nat) := by
  classical
  by_cases hsmall : S.card ≤ 1
  · rw [internalEdges_eq_empty_of_card_le_one (heavySupport H h) S hsmall]
    simp
  · have htwo : 2 ≤ S.card := by omega
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hmass :=
      internalNormalizedMass_add_cutInside H hm hh hdegree S
    have hcut :=
      treeScale_le_cutInsideNormalizedMass
        H hm hh hdegree hconnected S hS hSproper
    have hinternal :
        internalNormalizedMass H h S ≤
          (S.card : Rat) - treeScale m := by
      linarith
    have hweight :
        (∑ p ∈
            SimpleGraph.SinghLau.internalEdges (heavySupport H h) S,
            claim517Weight H h p) =
          treeScale m * internalNormalizedMass H h S := by
      unfold claim517Weight internalNormalizedMass
      rw [Finset.mul_sum]
    have hcast :
        ((S.card - 1 : Nat) : Rat) = (S.card : Rat) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hweight]
    exact_mod_cast (calc
      treeScale m * internalNormalizedMass H h S ≤
          treeScale m * ((S.card : Rat) - treeScale m) :=
        mul_le_mul_of_nonneg_left hinternal (treeScale_nonnegative hm)
      _ ≤ (S.card : Rat) - 1 :=
        treeScale_forest_arithmetic hm htwo
      _ = ((S.card - 1 : Nat) : Rat) := hcast.symm)

/-- The explicit rational point from Claim 5.17, with all four LP constraint
families proved from Observation 5.16. -/
noncomputable def claim517FeasiblePoint
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (hconnected : H.IsEdgeConnected h) :
    SimpleGraph.SinghLau.FeasibleBoundedDegreePoint
      (heavySupport H h) 2 where
  weight := claim517Weight H h
  nonnegative := by
    intro p _hp
    exact claim517Weight_nonnegative H hm hh hdegree p
  total := by
    have htotal := claim517Weight_total H hm hh hdegree
    simpa [Nat.cast_sub (by omega : 1 ≤ m)] using htotal
  forest := by
    intro S hSproper
    exact claim517Weight_forest H hm hh hdegree hconnected S hSproper
  degree := by
    intro v
    have hincident :
        SimpleGraph.SinghLau.incidentEdges (heavySupport H h) v =
          heavyPairsAt H h v := by
      ext p
      simp [SimpleGraph.SinghLau.incidentEdges, heavyPairsAt,
        SimpleGraph.mem_edgeFinset]
    rw [hincident]
    exact claim517Weight_degree H hm hh hdegree v

/-- Chekuri--Chuzhoy preprint Claim 5.17 (journal Claim 5.19), specialized
to the degree-`h`, `h`-edge-connected terminal multigraph produced in
Section 5.4.2.

Every selected tree edge is a heavy pair and therefore represents at least
`h / m^3` named parallel copies in the source multigraph. -/
theorem claim517_exists_boundedDegreeAuxiliarySpanningTree
    (H : FiniteEdgeIndexedGraph (Fin m))
    (hm : 2 ≤ m) (hh : 0 < h)
    (hdegree : ∀ v, H.degree v = h)
    (hconnected : H.IsEdgeConnected h) :
    ∃ T : _root_.SimpleGraph (Fin m),
      T ≤ heavySupport H h ∧
      T.IsTree ∧
      MaxDegreeAtMost T 3 ∧
      ∀ u v, T.Adj u v →
        heavyThreshold m h ≤ H.bundleCapacity s(u, v) := by
  let point :=
    claim517FeasiblePoint H hm hh hdegree hconnected
  rcases
      SimpleGraph.SinghLau.boundedDegreeSpanningTree_proved
        (heavySupport H h) 2 (by simpa using hm) point with
    ⟨T, hTsupport, hTtree, hTdegree⟩
  refine ⟨T, hTsupport, hTtree, by simpa using hTdegree, ?_⟩
  intro u v huv
  exact (heavySupport_adj H h u v).mp (hTsupport huv) |>.2

end ChekuriChuzhoySection5AuxiliaryTree
end SimpleGraph

end Lax17Proofs
