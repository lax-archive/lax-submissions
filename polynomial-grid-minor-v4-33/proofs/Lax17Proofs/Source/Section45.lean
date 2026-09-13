import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Lax17Proofs.Source.PathOfSets
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Section 4.5: selecting a weak path-of-sets system

This file formalizes the proof-facing content of Section 4.5.  The section has
two parts.

First, it proves the finite directed-layer argument behind Theorem 4.15 in a
weighted form: if every independent subfamily has weighted size `< A`, then a
directed graph on total weighted size at least `A * n` contains a directed chain
of `n` vertices.  This is the formal version of Claim 4.18 together with the
use of Observation 4.17.

Second, it packages the graph-theoretic assembly step from the selected slice
indices.  The package records exactly the cluster, nail, connector, and
well-linkedness data built in the paper from the retained row segments; from
that data the weak path-of-sets system is constructed with no further axioms.
-/

namespace SimpleGraph


namespace Section45

open Finset

/-! ## The finite directed-layer argument -/

variable {α : Type u}

/-- A finite set is independent for a directed relation if no two distinct
vertices are connected by an edge in either direction. -/
def RelIndependent (rel : α → α → Prop) (I : Finset α) : Prop :=
  ∀ ⦃a b : α⦄, a ∈ I → b ∈ I → a ≠ b → ¬ rel a b ∧ ¬ rel b a

namespace RelIndependent

variable {rel : α → α → Prop} {I J : Finset α}

/-- Independence is inherited by subsets. -/
theorem mono (h : RelIndependent rel I) (hJI : J ⊆ I) :
    RelIndependent rel J := by
  intro a b ha hb hne
  exact h (hJI ha) (hJI hb) hne

end RelIndependent

/-- The first layer of a finite directed graph restricted to `s`: vertices
with no incoming edge from `s`. -/
noncomputable def sourceLayer (rel : α → α → Prop) [∀ a b, Decidable (rel a b)]
    (s : Finset α) : Finset α :=
  s.filter fun v => ∀ u ∈ s, ¬ rel u v

namespace sourceLayer

variable {rel : α → α → Prop} [∀ a b, Decidable (rel a b)]
variable {s : Finset α}

theorem subset : sourceLayer rel s ⊆ s := by
  intro v hv
  exact (mem_filter.mp hv).1

theorem no_incoming {v : α} (hv : v ∈ sourceLayer rel s) :
    ∀ u ∈ s, ¬ rel u v :=
  (mem_filter.mp hv).2

theorem independent : RelIndependent rel (sourceLayer rel s) := by
  intro a b ha hb hne
  constructor
  · exact (no_incoming hb) a (subset ha)
  · exact (no_incoming ha) b (subset hb)

theorem exists_predecessor_of_mem_sdiff {v : α}
    [DecidableEq α]
    (hv : v ∈ s \ sourceLayer rel s) :
    ∃ u ∈ s, rel u v := by
  have hvs : v ∈ s := (mem_sdiff.mp hv).1
  have hvnot : v ∉ sourceLayer rel s := (mem_sdiff.mp hv).2
  by_contra hnone
  apply hvnot
  exact mem_filter.mpr
    ⟨hvs, by
      intro u hu hrel
      exact hnone ⟨u, hu, hrel⟩⟩

end sourceLayer

/-- A chain in a directed relation, all of whose vertices lie in `s`. -/
def RelChainIn (rel : α → α → Prop) (s : Finset α) (l : List α) : Prop :=
  l.IsChain rel ∧ ∀ v ∈ l, v ∈ s

/-- Weighted source-layer form of Claim 4.18.  If every independent subset
`I ⊆ s` satisfies `D * |I| < A`, and `D * |s|` is at least `A * n`, then `s`
contains a directed chain on `n` vertices.

The constants are arranged this way so that Section 4.5 can use
`A = 2 * N` and the Observation 4.17 bound `D * |I| < 2N` without divisions. -/
theorem exists_relChainIn_of_weighted_independent_bound
    [DecidableEq α]
    (rel : α → α → Prop) [∀ a b, Decidable (rel a b)]
    (s : Finset α) {A D n : ℕ}
    (hA : 0 < A)
    (hind :
      ∀ I : Finset α, I ⊆ s → RelIndependent rel I → D * I.card < A)
    (hlarge : A * n ≤ D * s.card) :
    ∃ l : List α, l.length = n ∧ RelChainIn rel s l := by
  classical
  induction n generalizing s with
  | zero =>
      refine ⟨[], by simp, ?_⟩
      exact ⟨List.isChain_nil, by simp⟩
  | succ n ih =>
      cases n with
      | zero =>
          have hspos : 0 < s.card := by
            by_contra hzero
            have hscard : s.card = 0 := Nat.eq_zero_of_not_pos hzero
            have hle0 : A ≤ 0 := by
              simpa [hscard] using hlarge
            omega
          rcases Finset.card_pos.mp hspos with ⟨v, hv⟩
          refine ⟨[v], by simp, ?_⟩
          exact ⟨List.isChain_singleton v, by simp [hv]⟩
      | succ n =>
          let L := sourceLayer rel s
          let R := s \ L
          have hLsub : L ⊆ s := sourceLayer.subset
          have hLind : RelIndependent rel L := sourceLayer.independent
          have hLsmall : D * L.card < A := hind L hLsub hLind
          have hRsub : R ⊆ s := by
            intro v hv
            exact (Finset.mem_sdiff.mp hv).1
          have hsplit : R.card + L.card = s.card := by
            simpa [R, L] using Finset.card_sdiff_add_card_eq_card hLsub
          have hmul_split : D * R.card + D * L.card = D * s.card := by
            rw [← Nat.mul_add, hsplit]
          have hRlarge : A * (n + 1) ≤ D * R.card := by
            have hlarge' : A * (n + 1 + 1) ≤ D * s.card := by
              simpa [Nat.succ_eq_add_one, add_assoc] using hlarge
            have hA_split : A * (n + 1 + 1) = A * (n + 1) + A := by
              ring
            omega
          have hindR :
              ∀ I : Finset α, I ⊆ R → RelIndependent rel I → D * I.card < A := by
            intro I hIR hI
            exact hind I (subset_trans hIR hRsub) hI
          rcases ih R hindR hRlarge with
            ⟨l, hlen, hchain, hmem⟩
          cases l with
          | nil =>
              simp at hlen
          | cons v t =>
              have hvR : v ∈ R := hmem v (by simp)
              rcases sourceLayer.exists_predecessor_of_mem_sdiff
                  (rel := rel) (s := s) (v := v) (by simpa [R, L] using hvR) with
                ⟨u, hu, huv⟩
              refine ⟨u :: v :: t, ?_, ?_⟩
              · simp [hlen]
              · constructor
                · simpa [List.isChain_cons_cons] using
                    (List.IsChain.cons_cons huv hchain)
                · intro x hx
                  simp only [List.mem_cons] at hx
                  rcases hx with rfl | rfl | hx
                  · exact hu
                  · exact hRsub hvR
                  · exact hRsub (hmem x (by simp [hx]))

/-- The large-overlap relation on slice indices used in Theorem 4.15. -/
def LargeOverlapRel {N M : ℕ} (S : Fin M → Finset (Fin N)) (w : ℕ)
    (i j : Fin M) : Prop :=
  i < j ∧ w ≤ (S i ∩ S j).card

/-- The degree sum identity for the row-set incidence relation. -/
theorem sum_rowDegrees_eq_sum_card
    {N M : ℕ} (S : Fin M → Finset (Fin N)) (I : Finset (Fin M)) :
    (∑ x : Fin N, (I.filter fun i => x ∈ S i).card) =
      ∑ i ∈ I, (S i).card := by
  classical
  let rel : Fin M → Fin N → Prop := fun i x => x ∈ S i
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := I) (t := (Finset.univ : Finset (Fin N)))
  have hAbove :
      ∀ i : Fin M,
        ((Finset.univ : Finset (Fin N)).bipartiteAbove rel i) = S i := by
    intro i
    ext x
    simp [rel]
  calc
    (∑ x : Fin N, (I.filter fun i => x ∈ S i).card)
        = ∑ x ∈ (Finset.univ : Finset (Fin N)),
            (I.bipartiteBelow rel x).card := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [Finset.bipartiteBelow, rel]
    _ = ∑ i ∈ I, ((Finset.univ : Finset (Fin N)).bipartiteAbove rel i).card := by
          simpa using hdc.symm
    _ = ∑ i ∈ I, (S i).card := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hAbove i]

/-- The square-degree sum identity for the row-set incidence relation.  The
left side counts triples `(i,j,x)` by `x`; the right side counts them by
ordered pairs `(i,j)`. -/
theorem sum_rowDegrees_sq_eq_sum_intersections
    {N M : ℕ} (S : Fin M → Finset (Fin N)) (I : Finset (Fin M)) :
    (∑ x : Fin N, (I.filter fun i => x ∈ S i).card ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card := by
  classical
  let pairSet : Finset (Fin M × Fin M) := I.product I
  let rel : (Fin M × Fin M) → Fin N → Prop :=
    fun p x => x ∈ S p.1 ∧ x ∈ S p.2
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := pairSet) (t := (Finset.univ : Finset (Fin N)))
  have hBelow :
      ∀ x : Fin N,
        (pairSet.bipartiteBelow rel x) =
          (I.filter fun i => x ∈ S i).product
            (I.filter fun i => x ∈ S i) := by
    intro x
    ext p
    simp [pairSet, rel, and_left_comm, and_assoc]
  have hAbove :
      ∀ p : Fin M × Fin M,
        ((Finset.univ : Finset (Fin N)).bipartiteAbove rel p) =
          S p.1 ∩ S p.2 := by
    intro p
    ext x
    simp [rel]
  calc
    (∑ x : Fin N, (I.filter fun i => x ∈ S i).card ^ 2)
        = ∑ x ∈ (Finset.univ : Finset (Fin N)),
            (pairSet.bipartiteBelow rel x).card := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [hBelow x]
          simp [pow_two]
    _ = ∑ p ∈ pairSet,
          ((Finset.univ : Finset (Fin N)).bipartiteAbove rel p).card := by
          simpa using hdc.symm
    _ = ∑ p ∈ pairSet, (S p.1 ∩ S p.2).card := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [hAbove p]
    _ = ∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card := by
          change (∑ p ∈ I.product I, (S p.1 ∩ S p.2).card) =
            ∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card
          simpa using
            (Finset.sum_product' I I
              (fun i j : Fin M => (S i ∩ S j).card))

/-- In an independent set for the large-overlap digraph, every two distinct
row sets meet in fewer than `w` rows. -/
theorem inter_card_lt_of_relIndependent
    {N M w : ℕ} {S : Fin M → Finset (Fin N)}
    {I : Finset (Fin M)}
    (hI : RelIndependent (LargeOverlapRel S w) I)
    {i j : Fin M} (hi : i ∈ I) (hj : j ∈ I) (hne : i ≠ j) :
    (S i ∩ S j).card < w := by
  classical
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hno : ¬ LargeOverlapRel S w i j := (hI hi hj hne).1
    exact Nat.lt_of_not_ge (by
      intro hge
      exact hno ⟨hij, hge⟩)
  · have hno : ¬ LargeOverlapRel S w j i := (hI hi hj hne).2
    have hlt : (S j ∩ S i).card < w := by
      exact Nat.lt_of_not_ge (by
        intro hge
        exact hno ⟨hji, hge⟩)
    simpa [Finset.inter_comm] using hlt

/-- Ordered-pair upper bound used in Claim 4.16. -/
theorem sum_intersections_lt_sum_card_add_square_mul
    {N M w : ℕ} (hw : 0 < w) {S : Fin M → Finset (Fin N)}
    {I : Finset (Fin M)}
    (hInonempty : I.Nonempty)
    (hI : RelIndependent (LargeOverlapRel S w) I) :
    (∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card) <
      (∑ i ∈ I, (S i).card) + I.card ^ 2 * w := by
  classical
  have hdiag_off :
        (∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card) ≤
          (∑ i ∈ I, (S i).card) + I.card * (I.card - 1) * (w - 1) := by
    calc
      (∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card)
          ≤ ∑ i ∈ I, ((S i).card + (I.card - 1) * (w - 1)) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have herase_card : (I.erase i).card = I.card - 1 :=
              Finset.card_erase_of_mem hi
            calc
              (∑ j ∈ I, (S i ∩ S j).card)
                  = (S i).card + ∑ j ∈ I.erase i, (S i ∩ S j).card := by
                    rw [← Finset.add_sum_erase I (fun j => (S i ∩ S j).card) hi]
                    simp [Finset.inter_self]
              _ ≤ (S i).card + (I.erase i).card * (w - 1) := by
                    gcongr
                    exact Finset.sum_le_card_nsmul _ _ _ (by
                      intro j hj
                      have hjI : j ∈ I := Finset.mem_of_mem_erase hj
                      have hne : j ≠ i := by
                        exact (Finset.mem_erase.mp hj).1
                      have hlt : (S i ∩ S j).card < w :=
                        inter_card_lt_of_relIndependent hI hi hjI (by exact hne.symm)
                      omega)
              _ = (S i).card + (I.card - 1) * (w - 1) := by
                    rw [herase_card]
      _ = (∑ i ∈ I, (S i).card) + I.card * ((I.card - 1) * (w - 1)) := by
            simp [Finset.sum_add_distrib]
      _ = (∑ i ∈ I, (S i).card) + I.card * (I.card - 1) * (w - 1) := by
            ring
  have hstrict :
      I.card * (I.card - 1) * (w - 1) < I.card ^ 2 * w := by
    have hIpos : 0 < I.card := Finset.card_pos.mpr hInonempty
    have hwsub : w - 1 < w := by omega
    have hprod :
        (I.card - 1) * (w - 1) < I.card * w := by
      nlinarith [Nat.sub_le I.card 1, hwsub,
        Nat.zero_le (I.card - 1), Nat.zero_le (w - 1)]
    have hmul :=
      Nat.mul_lt_mul_of_pos_left hprod hIpos
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact lt_of_le_of_lt hdiag_off (by nlinarith)

/-- Observation 4.17 from the numerical hypotheses of Theorem 4.15.

This is the double-counting argument of Claim 4.16 in division-free form.  If
each set `S_i` has size at least `D`, `N ≥ 3w`, and `D^2 ≥ 4Nw`, then every
independent set in the large-overlap digraph has `D * |I| < 2N`. -/
theorem independent_bound_of_theorem415_hypotheses
    {N M D w : ℕ} (S : Fin M → Finset (Fin N))
    (hw : 0 < w)
    (hN : 3 * w ≤ N)
    (hDsq : 4 * N * w ≤ D ^ 2)
    (hcard : ∀ i : Fin M, D ≤ (S i).card) :
    ∀ I : Finset (Fin M), RelIndependent (LargeOverlapRel S w) I →
      D * I.card < 2 * N := by
  classical
  intro I hI
  have hNpos : 0 < N := by
    nlinarith
  by_cases hInonempty : I.Nonempty
  · by_contra hnot
    have hlargeI : 2 * N ≤ D * I.card := Nat.le_of_not_gt hnot
    let ssum : ℕ := ∑ i ∈ I, (S i).card
    let pairCount : ℕ := ∑ i ∈ I, ∑ j ∈ I, (S i ∩ S j).card
    have hsum_lower : D * I.card ≤ ssum := by
      calc
        D * I.card = ∑ i ∈ I, D := by
          simp [Finset.sum_const]
          ring
        _ ≤ ∑ i ∈ I, (S i).card := by
          exact Finset.sum_le_sum (by intro i hi; exact hcard i)
    have hssum_large : 2 * N ≤ ssum := hlargeI.trans hsum_lower
    have hdeg := sum_rowDegrees_eq_sum_card S I
    have hsq := sum_rowDegrees_sq_eq_sum_intersections S I
    have hcauchy :
        (∑ x : Fin N, (I.filter fun i => x ∈ S i).card) ^ 2 ≤
          (Finset.univ : Finset (Fin N)).card *
            ∑ x : Fin N, (I.filter fun i => x ∈ S i).card ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin N)))
          (f := fun x : Fin N => (I.filter fun i => x ∈ S i).card))
    have hlower : ssum ^ 2 ≤ N * pairCount := by
      simpa [ssum, pairCount, hdeg, hsq] using hcauchy
    have hupper :
        pairCount < ssum + I.card ^ 2 * w := by
      simpa [ssum, pairCount] using
        sum_intersections_lt_sum_card_add_square_mul
          (S := S) hw hInonempty hI
    have hstrict :
        N * pairCount < N * (ssum + I.card ^ 2 * w) :=
      Nat.mul_lt_mul_of_pos_left hupper hNpos
    have hmainUpper :
        N * (ssum + I.card ^ 2 * w) ≤ ssum ^ 2 := by
      have h1 : 2 * (N * ssum) ≤ ssum ^ 2 := by
        nlinarith [hssum_large]
      have h2 : 4 * (N * (I.card ^ 2 * w)) ≤ ssum ^ 2 := by
        have h2a : 4 * (N * (I.card ^ 2 * w)) ≤ (D * I.card) ^ 2 := by
          nlinarith [hDsq]
        have h2b : (D * I.card) ^ 2 ≤ ssum ^ 2 :=
          Nat.pow_le_pow_left hsum_lower 2
        exact h2a.trans h2b
      nlinarith [h1, h2]
    have : ssum ^ 2 < ssum ^ 2 :=
      lt_of_le_of_lt hlower (hstrict.trans_le hmainUpper)
    exact (lt_irrefl _) this
  · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hInonempty
    subst I
    simp [hNpos]

/-- A theorem-shaped version of Theorem 4.15 after the independent-set bound
of Observation 4.17 has been established.

The paper proves the independent-set bound from the numerical hypotheses of
Theorem 4.15 in Claim 4.16.  This theorem is the remaining directed-graph
argument: a chain of `w` slice indices whose consecutive sets overlap in at
least `w` rows. -/
theorem theorem415_from_independent_bound
    {N M : ℕ} (S : Fin M → Finset (Fin N)) {D w : ℕ}
    (hind :
      ∀ I : Finset (Fin M), RelIndependent (LargeOverlapRel S w) I →
        D * I.card < 2 * N)
    (hlarge : 2 * N * w ≤ D * M) :
    ∃ l : List (Fin M),
      l.length = w ∧
        l.IsChain (LargeOverlapRel S w) := by
  classical
  by_cases hN : 0 < 2 * N
  · rcases exists_relChainIn_of_weighted_independent_bound
      (rel := LargeOverlapRel S w) (s := Finset.univ)
      (A := 2 * N) (D := D) (n := w)
      hN (by
        intro I _ hI
        exact hind I hI) (by simpa using hlarge) with
      ⟨l, hlen, hchain, hmem⟩
    exact ⟨l, hlen, hchain⟩
  · have hNzero : N = 0 := by omega
    subst N
    have hbad : D * (∅ : Finset (Fin M)).card < 0 := by
      exact hind ∅ (by intro a b ha hb hne; cases ha)
    omega

/-- Theorem 4.15 in the paper's numerical form.  The output is a list of
`w` slice indices; `List.IsChain (LargeOverlapRel S w)` says exactly that
consecutive indices are strictly increasing and the corresponding row sets
intersect in at least `w` rows. -/
theorem theorem415
    {N M D w : ℕ} (S : Fin M → Finset (Fin N))
    (hN : 3 * w ≤ N)
    (hDsq : 4 * N * w ≤ D ^ 2)
    (hlarge : 2 * N * w ≤ D * M)
    (hcard : ∀ i : Fin M, D ≤ (S i).card) :
    ∃ l : List (Fin M),
      l.length = w ∧
        l.IsChain (LargeOverlapRel S w) := by
  by_cases hw : 0 < w
  · exact theorem415_from_independent_bound S
      (independent_bound_of_theorem415_hypotheses S hw hN hDsq hcard)
      hlarge
  · have hwzero : w = 0 := by omega
    subst w
    exact ⟨[], by simp, List.isChain_nil⟩

/-! ## The graph assembly step -/

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- All graph-theoretic data needed after Theorem 4.15 has selected the slice
indices.  This structure is intentionally close to the last paragraph of
Section 4.5: it records the chosen cluster sequence, its left and right nail
sets, the connector path packings between consecutive clusters, and the
edge-well-linkedness of the nail union in every cluster.

The fields are exactly the fields of a weak path-of-sets system, but named in
the language of the Section 4.5 construction. -/
structure WeakPathOfSetsAssemblyData
    (G : _root_.SimpleGraph V) (ell w : ℕ) where
  /-- The selected sequence is nonempty. -/
  length_pos : 0 < ell
  /-- The selected row subfamilies have positive size. -/
  width_pos : 0 < w
  /-- The clusters `C'_j = C_{i_j}`. -/
  cluster : Fin ell → Finset V
  /-- Each selected cluster is connected. -/
  cluster_connected : ∀ i : Fin ell, IsCluster G (cluster i)
  /-- Distinct selected clusters are disjoint. -/
  cluster_disjoint :
    ∀ ⦃i j : Fin ell⦄, i ≠ j → Disjoint (cluster i) (cluster j)
  /-- The left nail set `A_j`. -/
  left : Fin ell → Finset V
  /-- The right nail set `B_j`. -/
  right : Fin ell → Finset V
  /-- Left nails are contained in their selected cluster. -/
  left_subset_cluster : ∀ i : Fin ell, left i ⊆ cluster i
  /-- Right nails are contained in their selected cluster. -/
  right_subset_cluster : ∀ i : Fin ell, right i ⊆ cluster i
  /-- The two nail sides in one cluster are disjoint. -/
  left_right_disjoint : ∀ i : Fin ell, Disjoint (left i) (right i)
  /-- Each left nail set has size `w`. -/
  left_card : ∀ i : Fin ell, (left i).card = w
  /-- Each right nail set has size `w`. -/
  right_card : ∀ i : Fin ell, (right i).card = w
  /-- The connector paths `P_j` between `B_j` and `A_{j+1}`. -/
  connector :
    (i : Fin ell) → (hi : i.1 + 1 < ell) →
      PerfectPathPacking G (right i) (left ⟨i.1 + 1, hi⟩)
  /-- The connector family across each gap has size `w`. -/
  connector_card :
    ∀ (i : Fin ell) (hi : i.1 + 1 < ell),
      (connector i hi).card = w
  /-- Connector paths are internally disjoint from every selected cluster. -/
  connector_internally_disjoint_clusters :
    ∀ (i : Fin ell) (hi : i.1 + 1 < ell) (j : Fin ell),
      (connector i hi).toPathPacking.InternallyDisjointFromSet (cluster j)
  /-- Connector families for different gaps are mutually node-disjoint. -/
  connector_mutually_nodeDisjoint :
    ∀ ⦃i j : Fin ell⦄ (hi : i.1 + 1 < ell) (hj : j.1 + 1 < ell),
      i ≠ j →
        (connector i hi).toPathPacking.MutuallyNodeDisjoint
          (connector j hj).toPathPacking
  /-- The nail union `A_j ∪ B_j` is weakly edge-well-linked in `C'_j`, as
  supplied by the happy-cluster output of Theorem 4.11. -/
  nails_weakWellLinked :
    ∀ i : Fin ell, Section44.WeakEdgeWellLinkedIn G (cluster i) (left i ∪ right i) w

namespace WeakPathOfSetsAssemblyData

/-- Assemble the weak path-of-sets system promised at the end of Section 4.5
from the selected clusters, nails, and connector paths. -/
noncomputable def toWeakPathOfSetsSystem
    {ell w : ℕ} (D : WeakPathOfSetsAssemblyData G ell w) :
    WeakPathOfSetsSystem G ell w where
  toPathOfSetsSystem :=
  { length_pos := D.length_pos
    width_pos := D.width_pos
    cluster := D.cluster
    cluster_connected := D.cluster_connected
    cluster_disjoint := D.cluster_disjoint
    left := D.left
    right := D.right
    left_subset_cluster := D.left_subset_cluster
    right_subset_cluster := D.right_subset_cluster
    left_right_disjoint := D.left_right_disjoint
    left_card := D.left_card
    right_card := D.right_card
    connector := D.connector
    connector_card := D.connector_card
    connector_internally_disjoint_clusters :=
      D.connector_internally_disjoint_clusters
    connector_mutually_nodeDisjoint :=
      D.connector_mutually_nodeDisjoint }
  nails_edgeWellLinked := by
    intro i
    apply Section44.observation49 (w := w)
    · calc
        (D.left i ∪ D.right i).card = (D.left i).card + (D.right i).card := by
          exact Finset.card_union_of_disjoint (D.left_right_disjoint i)
        _ = 2 * w := by
          rw [D.left_card i, D.right_card i]
          ring
        _ ≤ 2 * w := le_rfl
    · exact D.nails_weakWellLinked i

end WeakPathOfSetsAssemblyData

/-- Section 4.5 graph assembly theorem.  Once Theorem 4.15 has selected the
`ell = w` slices and the row-subpath construction has supplied the cluster,
nail, and connector data recorded in `WeakPathOfSetsAssemblyData`, the result
is a weak path-of-sets system of the same length and width. -/
theorem weak_pathOfSetsSystem_of_section45_assembly
    {ell w : ℕ} (D : WeakPathOfSetsAssemblyData G ell w) :
    Nonempty (WeakPathOfSetsSystem G ell w) :=
  ⟨D.toWeakPathOfSetsSystem⟩

/-- The `j`th selected slice index represented by a list of length `w`. -/
def selectedIndex {M w : ℕ}
    (l : List (Fin M)) (hlen : l.length = w) (j : Fin w) : Fin M :=
  l.get ⟨j.1, by simp [hlen, j.2]⟩

/-- Consecutive selected indices in a selected chain satisfy the large-overlap
relation. -/
theorem selectedIndex_chain_succ {N M w : ℕ}
    {sliceRows : Fin M → Finset (Fin N)}
    {l : List (Fin M)} (hlen : l.length = w)
    (hchain : l.IsChain (LargeOverlapRel sliceRows w))
    (i : Fin w) (hi : i.1 + 1 < w) :
    LargeOverlapRel sliceRows w
      (selectedIndex l hlen i)
      (selectedIndex l hlen ⟨i.1 + 1, hi⟩) := by
  have hrel := List.IsChain.getElem hchain i.1 (by simpa [hlen] using hi)
  simpa [selectedIndex] using hrel

/-- The nail set obtained from two row-index sets by taking their left and
right endpoint images in a fixed slice. -/
def endpointNailSet {N M : ℕ}
    (leftEndpoint rightEndpoint : Fin M → Fin N → V)
    (i : Fin M) (L R : Finset (Fin N)) : Finset V :=
  L.image (leftEndpoint i) ∪ R.image (rightEndpoint i)

/-- Weak well-linkedness of the endpoint nail set generated by two row-index
sets in a fixed slice. -/
def EndpointRowsWeakWellLinked {N M : ℕ}
    (G : _root_.SimpleGraph V) (cluster : Fin M → Finset V)
    (leftEndpoint rightEndpoint : Fin M → Fin N → V)
    (i : Fin M) (L R : Finset (Fin N)) (w : ℕ) : Prop :=
  Section44.WeakEdgeWellLinkedIn G (cluster i)
    (endpointNailSet leftEndpoint rightEndpoint i L R) w

/-- The paper's left row set for the selected cluster `i`.  For the first
selected cluster this is the arbitrary set `T₁ ⊆ S_{i₁}`.  For later clusters it
is the gap set chosen inside `S_{i-1} ∩ S_i`. -/
def paperLeftRows {N M w : ℕ} {sliceRows : Fin M → Finset (Fin N)}
    (firstRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) →
          Finset (Fin N))
    (gapRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) →
          (i : Fin w) → i.1 + 1 < w → Finset (Fin N))
    (l : List (Fin M)) (hlen : l.length = w)
    (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w) :
    Finset (Fin N) :=
  if h0 : i.1 = 0 then
    firstRows l hlen hchain
  else
    let k : Fin w := ⟨i.1 - 1, by omega⟩
    gapRows l hlen hchain k (by
      dsimp [k]
      omega)

/-- The paper's right row set for the selected cluster `i`.  Away from the last
cluster it is the next gap set `T_{i+1} ⊆ S_i ∩ S_{i+1}`.  For the last cluster
it is the same set as its left row set, matching the paper's convention
`T_{w+1}=T_w`. -/
def paperRightRows {N M w : ℕ} {sliceRows : Fin M → Finset (Fin N)}
    (firstRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) →
          Finset (Fin N))
    (gapRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) →
          (i : Fin w) → i.1 + 1 < w → Finset (Fin N))
    (l : List (Fin M)) (hlen : l.length = w)
    (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w) :
    Finset (Fin N) :=
  if hi : i.1 + 1 < w then
    gapRows l hlen hchain i hi
  else
    paperLeftRows firstRows gapRows l hlen hchain i

/-- The row sets `T_j` used in the paper exist once each selected slice contains
at least `w` rows.  The first set is chosen inside the first selected slice; the
gap sets are chosen inside the consecutive large overlaps. -/
theorem exists_paperRows
    {N M D w : ℕ} (sliceRows : Fin M → Finset (Fin N))
    (hwidth : 0 < w)
    (hDwidth : w ≤ D)
    (hcard : ∀ i : Fin M, D ≤ (sliceRows i).card) :
    ∃ (firstRows :
        (l : List (Fin M)) → (hlen : l.length = w) →
          l.IsChain (LargeOverlapRel sliceRows w) → Finset (Fin N)),
      ∃ (gapRows :
        (l : List (Fin M)) → (hlen : l.length = w) →
          l.IsChain (LargeOverlapRel sliceRows w) →
            (i : Fin w) → i.1 + 1 < w → Finset (Fin N)),
        (∀ (l : List (Fin M)) (hlen : l.length = w)
          (hchain : l.IsChain (LargeOverlapRel sliceRows w)),
            firstRows l hlen hchain ⊆
              sliceRows (selectedIndex l hlen ⟨0, hwidth⟩)) ∧
        (∀ (l : List (Fin M)) (hlen : l.length = w)
          (hchain : l.IsChain (LargeOverlapRel sliceRows w)),
            (firstRows l hlen hchain).card = w) ∧
        (∀ (l : List (Fin M)) (hlen : l.length = w)
          (hchain : l.IsChain (LargeOverlapRel sliceRows w))
          (i : Fin w) (hi : i.1 + 1 < w),
            gapRows l hlen hchain i hi ⊆
              sliceRows (selectedIndex l hlen i)) ∧
        (∀ (l : List (Fin M)) (hlen : l.length = w)
          (hchain : l.IsChain (LargeOverlapRel sliceRows w))
          (i : Fin w) (hi : i.1 + 1 < w),
            gapRows l hlen hchain i hi ⊆
              sliceRows (selectedIndex l hlen ⟨i.1 + 1, hi⟩)) ∧
        (∀ (l : List (Fin M)) (hlen : l.length = w)
          (hchain : l.IsChain (LargeOverlapRel sliceRows w))
          (i : Fin w) (hi : i.1 + 1 < w),
            (gapRows l hlen hchain i hi).card = w) := by
  classical
  let firstRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) → Finset (Fin N) :=
    fun l hlen _hchain =>
      Classical.choose <| Finset.exists_subset_card_eq
        ((hDwidth.trans (hcard (selectedIndex l hlen ⟨0, hwidth⟩))))
  let gapRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) →
          (i : Fin w) → i.1 + 1 < w → Finset (Fin N) :=
    fun l hlen hchain i hi =>
      Classical.choose <| Finset.exists_subset_card_eq
        ((selectedIndex_chain_succ (sliceRows := sliceRows) hlen hchain i hi).2)
  refine ⟨firstRows, gapRows, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hlen hchain
    exact (Classical.choose_spec <| Finset.exists_subset_card_eq
      ((hDwidth.trans (hcard (selectedIndex l hlen ⟨0, hwidth⟩))))).1
  · intro l hlen hchain
    exact (Classical.choose_spec <| Finset.exists_subset_card_eq
      ((hDwidth.trans (hcard (selectedIndex l hlen ⟨0, hwidth⟩))))).2
  · intro l hlen hchain i hi r hr
    have hsub :
        gapRows l hlen hchain i hi ⊆
          sliceRows (selectedIndex l hlen i) ∩
            sliceRows (selectedIndex l hlen ⟨i.1 + 1, hi⟩) :=
      (Classical.choose_spec <| Finset.exists_subset_card_eq
        ((selectedIndex_chain_succ (sliceRows := sliceRows) hlen hchain i hi).2)).1
    exact (Finset.mem_inter.mp (hsub hr)).1
  · intro l hlen hchain i hi r hr
    have hsub :
        gapRows l hlen hchain i hi ⊆
          sliceRows (selectedIndex l hlen i) ∩
            sliceRows (selectedIndex l hlen ⟨i.1 + 1, hi⟩) :=
      (Classical.choose_spec <| Finset.exists_subset_card_eq
        ((selectedIndex_chain_succ (sliceRows := sliceRows) hlen hchain i hi).2)).1
    exact (Finset.mem_inter.mp (hsub hr)).2
  · intro l hlen hchain i hi
    exact (Classical.choose_spec <| Finset.exists_subset_card_eq
      ((selectedIndex_chain_succ (sliceRows := sliceRows) hlen hchain i hi).2)).2

/-- A row-endpoint formulation of Section 4.5.  The selected-chain realization
is given by row subsets and endpoint maps: the theorem derives the actual nail
sets by imaging those row subsets under the endpoint maps, and then constructs
the weak path-of-sets system. -/
theorem section45_weak_pathOfSetsSystem_of_rowEndpointData
    {N M D w : ℕ}
    (sliceRows : Fin M → Finset (Fin N))
    (hwidth : 0 < w)
    (hN : 3 * w ≤ N)
    (hDsq : 4 * N * w ≤ D ^ 2)
    (hlarge : 2 * N * w ≤ D * M)
    (hcard : ∀ i : Fin M, D ≤ (sliceRows i).card)
    (cluster : Fin M → Finset V)
    (cluster_connected : ∀ i : Fin M, IsCluster G (cluster i))
    (selected_cluster_disjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (_ : l.IsChain (LargeOverlapRel sliceRows w))
        ⦃i j : Fin w⦄, i ≠ j →
          Disjoint (cluster (selectedIndex l hlen i))
            (cluster (selectedIndex l hlen j)))
    (leftEndpoint rightEndpoint : Fin M → Fin N → V)
    (leftEndpoint_injective :
      ∀ i : Fin M, Function.Injective (leftEndpoint i))
    (rightEndpoint_injective :
      ∀ i : Fin M, Function.Injective (rightEndpoint i))
    (leftEndpoint_mem :
      ∀ (i : Fin M) {r : Fin N}, r ∈ sliceRows i →
        leftEndpoint i r ∈ cluster i)
    (rightEndpoint_mem :
      ∀ (i : Fin M) {r : Fin N}, r ∈ sliceRows i →
        rightEndpoint i r ∈ cluster i)
    (leftRows rightRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) →
          Fin w → Finset (Fin N))
    (leftRows_subset :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          leftRows l hlen hchain i ⊆
            sliceRows (selectedIndex l hlen i))
    (rightRows_subset :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          rightRows l hlen hchain i ⊆
            sliceRows (selectedIndex l hlen i))
    (leftRows_card :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          (leftRows l hlen hchain i).card = w)
    (rightRows_card :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          (rightRows l hlen hchain i).card = w)
    (nails_disjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          Disjoint
            ((leftRows l hlen hchain i).image
              (leftEndpoint (selectedIndex l hlen i)))
            ((rightRows l hlen hchain i).image
              (rightEndpoint (selectedIndex l hlen i))))
    (connector :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          PerfectPathPacking G
            ((rightRows l hlen hchain i).image
              (rightEndpoint (selectedIndex l hlen i)))
            ((leftRows l hlen hchain ⟨i.1 + 1, hi⟩).image
              (leftEndpoint (selectedIndex l hlen ⟨i.1 + 1, hi⟩))))
    (connector_internally_disjoint_clusters :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w) (j : Fin w),
          (connector l hlen hchain i hi).toPathPacking.InternallyDisjointFromSet
            (cluster (selectedIndex l hlen j)))
    (connector_mutually_nodeDisjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        ⦃i j : Fin w⦄ (hi : i.1 + 1 < w) (hj : j.1 + 1 < w),
          i ≠ j →
            (connector l hlen hchain i hi).toPathPacking.MutuallyNodeDisjoint
              (connector l hlen hchain j hj).toPathPacking)
    (nails_weakWellLinked :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          (EndpointRowsWeakWellLinked G cluster leftEndpoint rightEndpoint
            (selectedIndex l hlen i)
            (leftRows l hlen hchain i) (rightRows l hlen hchain i) w)) :
    Nonempty (WeakPathOfSetsSystem G w w) := by
  classical
  rcases theorem415 sliceRows hN hDsq hlarge hcard with ⟨l, hlen, hchain⟩
  refine weak_pathOfSetsSystem_of_section45_assembly ?_
  exact
  { length_pos := hwidth
    width_pos := hwidth
    cluster := fun i =>
      cluster (selectedIndex l hlen i)
    cluster_connected := by
      intro i
      exact cluster_connected (selectedIndex l hlen i)
    cluster_disjoint := selected_cluster_disjoint l hlen hchain
    left := fun i =>
      (leftRows l hlen hchain i).image
        (leftEndpoint (selectedIndex l hlen i))
    right := fun i =>
      (rightRows l hlen hchain i).image
        (rightEndpoint (selectedIndex l hlen i))
    left_subset_cluster := by
      intro i v hv
      rcases Finset.mem_image.mp hv with ⟨r, hr, rfl⟩
      exact leftEndpoint_mem (selectedIndex l hlen i)
        (leftRows_subset l hlen hchain i hr)
    right_subset_cluster := by
      intro i v hv
      rcases Finset.mem_image.mp hv with ⟨r, hr, rfl⟩
      exact rightEndpoint_mem (selectedIndex l hlen i)
        (rightRows_subset l hlen hchain i hr)
    left_right_disjoint := by
      intro i
      exact nails_disjoint l hlen hchain i
    left_card := by
      intro i
      rw [Finset.card_image_of_injective]
      · exact leftRows_card l hlen hchain i
      · exact leftEndpoint_injective (selectedIndex l hlen i)
    right_card := by
      intro i
      rw [Finset.card_image_of_injective]
      · exact rightRows_card l hlen hchain i
      · exact rightEndpoint_injective (selectedIndex l hlen i)
    connector := fun i hi => connector l hlen hchain i hi
    connector_card := by
      intro i hi
      rw [(connector l hlen hchain i hi).card_eq_left_card]
      rw [Finset.card_image_of_injective]
      · exact rightRows_card l hlen hchain i
      · exact rightEndpoint_injective (selectedIndex l hlen i)
    connector_internally_disjoint_clusters :=
      connector_internally_disjoint_clusters l hlen hchain
    connector_mutually_nodeDisjoint :=
      connector_mutually_nodeDisjoint l hlen hchain
    nails_weakWellLinked := by
      intro i
      simpa [EndpointRowsWeakWellLinked, endpointNailSet] using
        nails_weakWellLinked l hlen hchain i }

/-- Section 4.5 with the paper's row-set convention.  The sets `T_j` are
represented by an arbitrary first set `firstRows` and by one `gapRows` set for
each consecutive overlap in the selected chain.  The left nails of cluster `j`
come from `T_j`, and the right nails come from `T_{j+1}`, with the convention
that the last right set equals the last left set. -/
theorem section45_weak_pathOfSetsSystem_of_paperRowEndpointData
    {N M D w : ℕ}
    (sliceRows : Fin M → Finset (Fin N))
    (hwidth : 0 < w)
    (hN : 3 * w ≤ N)
    (hDsq : 4 * N * w ≤ D ^ 2)
    (hlarge : 2 * N * w ≤ D * M)
    (hcard : ∀ i : Fin M, D ≤ (sliceRows i).card)
    (cluster : Fin M → Finset V)
    (cluster_connected : ∀ i : Fin M, IsCluster G (cluster i))
    (selected_cluster_disjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (_ : l.IsChain (LargeOverlapRel sliceRows w))
        ⦃i j : Fin w⦄, i ≠ j →
          Disjoint (cluster (selectedIndex l hlen i))
            (cluster (selectedIndex l hlen j)))
    (leftEndpoint rightEndpoint : Fin M → Fin N → V)
    (leftEndpoint_injective :
      ∀ i : Fin M, Function.Injective (leftEndpoint i))
    (rightEndpoint_injective :
      ∀ i : Fin M, Function.Injective (rightEndpoint i))
    (leftEndpoint_mem :
      ∀ (i : Fin M) {r : Fin N}, r ∈ sliceRows i →
        leftEndpoint i r ∈ cluster i)
    (rightEndpoint_mem :
      ∀ (i : Fin M) {r : Fin N}, r ∈ sliceRows i →
        rightEndpoint i r ∈ cluster i)
    (firstRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) → Finset (Fin N))
    (gapRows :
      (l : List (Fin M)) → (hlen : l.length = w) →
        l.IsChain (LargeOverlapRel sliceRows w) →
          (i : Fin w) → i.1 + 1 < w → Finset (Fin N))
    (firstRows_subset :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)),
          firstRows l hlen hchain ⊆
            sliceRows (selectedIndex l hlen ⟨0, hwidth⟩))
    (firstRows_card :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)),
          (firstRows l hlen hchain).card = w)
    (gapRows_subset_left :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          gapRows l hlen hchain i hi ⊆
            sliceRows (selectedIndex l hlen i))
    (gapRows_subset_right :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          gapRows l hlen hchain i hi ⊆
            sliceRows (selectedIndex l hlen ⟨i.1 + 1, hi⟩))
    (gapRows_card :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          (gapRows l hlen hchain i hi).card = w)
    (nails_disjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          Disjoint
            ((paperLeftRows firstRows gapRows l hlen hchain i).image
              (leftEndpoint (selectedIndex l hlen i)))
            ((paperRightRows firstRows gapRows l hlen hchain i).image
              (rightEndpoint (selectedIndex l hlen i))))
    (connector :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w),
          PerfectPathPacking G
            ((paperRightRows firstRows gapRows l hlen hchain i).image
              (rightEndpoint (selectedIndex l hlen i)))
            ((paperLeftRows firstRows gapRows l hlen hchain ⟨i.1 + 1, hi⟩).image
              (leftEndpoint (selectedIndex l hlen ⟨i.1 + 1, hi⟩))))
    (connector_internally_disjoint_clusters :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        (i : Fin w) (hi : i.1 + 1 < w) (j : Fin w),
          (connector l hlen hchain i hi).toPathPacking.InternallyDisjointFromSet
            (cluster (selectedIndex l hlen j)))
    (connector_mutually_nodeDisjoint :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w))
        ⦃i j : Fin w⦄ (hi : i.1 + 1 < w) (hj : j.1 + 1 < w),
          i ≠ j →
            (connector l hlen hchain i hi).toPathPacking.MutuallyNodeDisjoint
              (connector l hlen hchain j hj).toPathPacking)
    (nails_weakWellLinked :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          EndpointRowsWeakWellLinked G cluster leftEndpoint rightEndpoint
            (selectedIndex l hlen i)
            (paperLeftRows firstRows gapRows l hlen hchain i)
            (paperRightRows firstRows gapRows l hlen hchain i) w) :
    Nonempty (WeakPathOfSetsSystem G w w) := by
  classical
  let leftRows :=
    fun (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w) =>
        paperLeftRows firstRows gapRows l hlen hchain i
  let rightRows :=
    fun (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w) =>
        paperRightRows firstRows gapRows l hlen hchain i
  have hleft_subset :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          leftRows l hlen hchain i ⊆
            sliceRows (selectedIndex l hlen i) := by
    intro l hlen hchain i
    by_cases h0 : i.1 = 0
    · have h0lt : 0 < w := by simpa [h0] using i.2
      have hi : i = ⟨0, h0lt⟩ := by
        ext
        exact h0
      simpa [leftRows, paperLeftRows, h0, hi] using
        firstRows_subset l hlen hchain
    · let k : Fin w := ⟨i.1 - 1, by omega⟩
      have hk : k.1 + 1 < w := by
        dsimp [k]
        omega
      have hnext : (⟨k.1 + 1, hk⟩ : Fin w) = i := by
        ext
        dsimp [k]
        omega
      simpa [leftRows, paperLeftRows, h0, k, hk, hnext] using
        gapRows_subset_right l hlen hchain k hk
  have hright_subset :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          rightRows l hlen hchain i ⊆
            sliceRows (selectedIndex l hlen i) := by
    intro l hlen hchain i
    by_cases hi : i.1 + 1 < w
    · simpa [rightRows, paperRightRows, hi] using
        gapRows_subset_left l hlen hchain i hi
    · simpa [rightRows, paperRightRows, hi] using
        hleft_subset l hlen hchain i
  have hleft_card :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          (leftRows l hlen hchain i).card = w := by
    intro l hlen hchain i
    by_cases h0 : i.1 = 0
    · simpa [leftRows, paperLeftRows, h0] using
        firstRows_card l hlen hchain
    · let k : Fin w := ⟨i.1 - 1, by omega⟩
      have hk : k.1 + 1 < w := by
        dsimp [k]
        omega
      simpa [leftRows, paperLeftRows, h0, k, hk] using
        gapRows_card l hlen hchain k hk
  have hright_card :
      ∀ (l : List (Fin M)) (hlen : l.length = w)
        (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
          (rightRows l hlen hchain i).card = w := by
    intro l hlen hchain i
    by_cases hi : i.1 + 1 < w
    · simpa [rightRows, paperRightRows, hi] using
        gapRows_card l hlen hchain i hi
    · simpa [rightRows, paperRightRows, hi] using
        hleft_card l hlen hchain i
  exact section45_weak_pathOfSetsSystem_of_rowEndpointData
    sliceRows hwidth hN hDsq hlarge hcard
    cluster cluster_connected selected_cluster_disjoint
    leftEndpoint rightEndpoint leftEndpoint_injective rightEndpoint_injective
    leftEndpoint_mem rightEndpoint_mem
    leftRows rightRows hleft_subset hright_subset hleft_card hright_card
    (by
      intro l hlen hchain i
      simpa [leftRows, rightRows] using nails_disjoint l hlen hchain i)
    (by
      intro l hlen hchain i hi
      simpa [leftRows, rightRows] using connector l hlen hchain i hi)
    (by
      intro l hlen hchain i hi j
      exact connector_internally_disjoint_clusters l hlen hchain i hi j)
    (by
      intro l hlen hchain i j hi hj hij
      exact connector_mutually_nodeDisjoint l hlen hchain hi hj hij)
    (by
      intro l hlen hchain i
      simpa [leftRows, rightRows] using nails_weakWellLinked l hlen hchain i)

/-- The complete proof-facing input for the Section 4.5 step.

The paper obtains `sliceRows` from the retained row segments in the happy
clusters.  The numeric and cardinality fields are the hypotheses checked
immediately before applying Theorem 4.15.  The `assembly` field is the explicit
graph construction after the indices `i₁ < ... < i_w` are selected: it
supplies the clusters, nail sets, connector paths, and well-linkedness
certificates for that selected sequence. -/
structure Section45Input
    (G : _root_.SimpleGraph V) (N M D w : ℕ) where
  /-- The set `S_i` of row indices whose slice-`i` segment is retained in the
  happy cluster chosen for that slice. -/
  sliceRows : Fin M → Finset (Fin N)
  /-- Section 4.5 constructs a positive-width path-of-sets system. -/
  width_pos : 0 < w
  /-- The first numerical hypothesis of Theorem 4.15, `N ≥ 3w`. -/
  N_large : 3 * w ≤ N
  /-- The second numerical hypothesis of Theorem 4.15, `D^2 ≥ 4Nw`. -/
  D_square : 4 * N * w ≤ D ^ 2
  /-- The numerical lower bound that forces a chain of `w` selected slices. -/
  large : 2 * N * w ≤ D * M
  /-- Each slice row set has size at least `D`. -/
  row_card : ∀ i : Fin M, D ≤ (sliceRows i).card
  /-- The selected clusters, indexed by the selected chain. -/
  cluster :
    (l : List (Fin M)) → l.length = w →
      l.IsChain (LargeOverlapRel sliceRows w) →
        Fin w → Finset V
  /-- Each selected cluster is connected. -/
  cluster_connected :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
        IsCluster G (cluster l hlen hchain i)
  /-- Distinct selected clusters are disjoint. -/
  cluster_disjoint :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w))
      ⦃i j : Fin w⦄, i ≠ j →
        Disjoint (cluster l hlen hchain i) (cluster l hlen hchain j)
  /-- Left nails of the selected clusters. -/
  left :
    (l : List (Fin M)) → (hlen : l.length = w) →
      l.IsChain (LargeOverlapRel sliceRows w) →
        Fin w → Finset V
  /-- Right nails of the selected clusters. -/
  right :
    (l : List (Fin M)) → (hlen : l.length = w) →
      l.IsChain (LargeOverlapRel sliceRows w) →
        Fin w → Finset V
  /-- Left nails lie in their selected cluster. -/
  left_subset_cluster :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
        left l hlen hchain i ⊆ cluster l hlen hchain i
  /-- Right nails lie in their selected cluster. -/
  right_subset_cluster :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
        right l hlen hchain i ⊆ cluster l hlen hchain i
  /-- The two nail sides in each selected cluster are disjoint. -/
  left_right_disjoint :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
        Disjoint (left l hlen hchain i) (right l hlen hchain i)
  /-- Each selected left nail set has size `w`. -/
  left_card :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
        (left l hlen hchain i).card = w
  /-- Each selected right nail set has size `w`. -/
  right_card :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
        (right l hlen hchain i).card = w
  /-- Connector path packings between consecutive selected clusters. -/
  connector :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w))
      (i : Fin w) (hi : i.1 + 1 < w),
        PerfectPathPacking G
          (right l hlen hchain i)
          (left l hlen hchain ⟨i.1 + 1, hi⟩)
  /-- Each connector family has size `w`. -/
  connector_card :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w))
      (i : Fin w) (hi : i.1 + 1 < w),
        (connector l hlen hchain i hi).card = w
  /-- Connector paths are internally disjoint from all selected clusters. -/
  connector_internally_disjoint_clusters :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w))
      (i : Fin w) (hi : i.1 + 1 < w) (j : Fin w),
        (connector l hlen hchain i hi).toPathPacking.InternallyDisjointFromSet
          (cluster l hlen hchain j)
  /-- Connector families for different selected gaps are mutually
  node-disjoint. -/
  connector_mutually_nodeDisjoint :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w))
      ⦃i j : Fin w⦄ (hi : i.1 + 1 < w) (hj : j.1 + 1 < w),
        i ≠ j →
          (connector l hlen hchain i hi).toPathPacking.MutuallyNodeDisjoint
            (connector l hlen hchain j hj).toPathPacking
  /-- In each selected cluster, the union of left and right nails is weakly
  edge-well-linked. -/
  nails_weakWellLinked :
    ∀ (l : List (Fin M)) (hlen : l.length = w)
      (hchain : l.IsChain (LargeOverlapRel sliceRows w)) (i : Fin w),
        Section44.WeakEdgeWellLinkedIn G
          (cluster l hlen hchain i)
          (left l hlen hchain i ∪ right l hlen hchain i) w

/-- Section 4.5 as a single proposition: from the retained-row overlap data
and the corresponding cluster/nail/connector realization, construct a weak
path-of-sets system of length and width `w`. -/
def Section45Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
    {N M D w : ℕ},
      Section45Input G N M D w →
        Nonempty (WeakPathOfSetsSystem G w w)

/-- Chuzhoy--Tan Section 4.5, in proof-facing form.  The directed selection
part is `theorem415_from_independent_bound`; the final graph object is obtained
by applying the supplied Section 4.5 assembly data to the selected chain. -/
theorem section45_weak_pathOfSetsSystem : Section45Statement.{u} := by
  intro V _instDecidableEq G N M D w Input
  classical
  rcases theorem415
      Input.sliceRows Input.N_large Input.D_square Input.large Input.row_card with
    ⟨l, hlen, hchain⟩
  refine weak_pathOfSetsSystem_of_section45_assembly ?_
  exact
  { length_pos := by
      exact Input.width_pos
    width_pos := Input.width_pos
    cluster := Input.cluster l hlen hchain
    cluster_connected := Input.cluster_connected l hlen hchain
    cluster_disjoint := Input.cluster_disjoint l hlen hchain
    left := Input.left l hlen hchain
    right := Input.right l hlen hchain
    left_subset_cluster := Input.left_subset_cluster l hlen hchain
    right_subset_cluster := Input.right_subset_cluster l hlen hchain
    left_right_disjoint := Input.left_right_disjoint l hlen hchain
    left_card := Input.left_card l hlen hchain
    right_card := Input.right_card l hlen hchain
    connector := Input.connector l hlen hchain
    connector_card := Input.connector_card l hlen hchain
    connector_internally_disjoint_clusters :=
      Input.connector_internally_disjoint_clusters l hlen hchain
    connector_mutually_nodeDisjoint :=
      Input.connector_mutually_nodeDisjoint l hlen hchain
    nails_weakWellLinked := Input.nails_weakWellLinked l hlen hchain }

end Section45

end SimpleGraph

end Lax17Proofs
