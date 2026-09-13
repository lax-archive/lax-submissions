import Mathlib.Combinatorics.SimpleGraph.Metric
import Lax17Proofs.Source.ExpanderMinor

namespace Lax17Proofs

universe u v w

/-!
# The expansion-diameter lemma used in Theorem 8.1

This file starts the self-contained formalization of Lemma 8.2 from
`expander.pdf`, in the form needed by the proof of Theorem 8.1.

The paper writes `N_G(X,Y)` for the subset of vertices of `Y` having a neighbor
in `X`.  The API below therefore works with `relativeExternalNeighborhood G X Y`
and repeatedly applies it with `Y = C \ X`, where `C` is the current reservoir.

The main finite object is a reservoir ball: the vertices of `C` reachable from a
root by a walk of bounded length whose entire support stays inside `C`.  The
lemmas in this file prove the one-step expansion facts that feed the usual BFS
growth proof of the logarithmic diameter bound.
-/

namespace SimpleGraph


variable {V : Type u}

/-- Ceiling base-two logarithm is at most floor base-two logarithm plus one. -/
theorem nat_clog_two_le_log_two_add_one (n : ℕ) :
    Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
  Nat.clog_le_of_le_pow
    (Nat.le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two n))

/-- A reservoir has no larger ceiling logarithm than the ambient host, up to
the usual `+1` gap between `clog` and `log`. -/
theorem reservoir_clog_two_le_host_log_two_add_one
    [Fintype V] (C : Finset V) :
    Nat.clog 2 C.card ≤ Nat.log 2 (Fintype.card V) + 1 :=
  (Nat.clog_mono_right 2 (Finset.card_le_univ C)).trans
    (nat_clog_two_le_log_two_add_one (Fintype.card V))

/-- For hosts with positive binary logarithm, the reservoir `clog` is bounded
by twice the host `log`. -/
theorem reservoir_clog_two_le_two_host_log_two
    [Fintype V] (C : Finset V)
    (hlog : 0 < Nat.log 2 (Fintype.card V)) :
    Nat.clog 2 C.card ≤ 2 * Nat.log 2 (Fintype.card V) := by
  have h := reservoir_clog_two_le_host_log_two_add_one (V := V) C
  omega

/-- The ball of radius `r` around `x`, measured by walks whose support remains
inside the reservoir `C`. -/
noncomputable def reservoirBall [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (x : V) (r : ℕ) : Finset V :=
  by
    classical
    exact C.filter fun y =>
      ∃ p : G.Walk x y,
        p.length ≤ r ∧ ∀ z : V, z ∈ p.support → z ∈ C

@[simp] theorem mem_reservoirBall [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {C : Finset V} {x y : V} {r : ℕ} :
    y ∈ reservoirBall G C x r ↔
      y ∈ C ∧
        ∃ p : G.Walk x y,
          p.length ≤ r ∧ ∀ z : V, z ∈ p.support → z ∈ C := by
  simp [reservoirBall]

/-- Reservoir balls are subsets of their reservoir. -/
theorem reservoirBall_subset_reservoir [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (C : Finset V) (x : V) (r : ℕ) :
    reservoirBall G C x r ⊆ C := by
  intro y hy
  exact (mem_reservoirBall.1 hy).1

/-- The root belongs to every reservoir ball centered at it. -/
theorem mem_reservoirBall_self [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {C : Finset V} {x : V} {r : ℕ} (hxC : x ∈ C) :
    x ∈ reservoirBall G C x r := by
  refine mem_reservoirBall.2 ⟨hxC, _root_.SimpleGraph.Walk.nil, ?_, ?_⟩
  · simp
  · intro z hz
    have hzx : z = x := by simpa using hz
    simpa [hzx] using hxC

/-- Reservoir balls are monotone in the radius. -/
theorem reservoirBall_mono_radius [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {C : Finset V} {x : V} {r s : ℕ} (hrs : r ≤ s) :
    reservoirBall G C x r ⊆ reservoirBall G C x s := by
  intro y hy
  rcases mem_reservoirBall.1 hy with ⟨hyC, p, hplen, hpC⟩
  exact mem_reservoirBall.2 ⟨hyC, p, hplen.trans hrs, hpC⟩

/-- The paper frontier `N_G(B, C \ B)` of a reservoir ball is contained in the
next reservoir ball. -/
theorem relativeExternalNeighborhood_reservoirBall_subset_succ
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {C : Finset V} {x : V} {r : ℕ} :
    relativeExternalNeighborhood G (reservoirBall G C x r)
        (C \ reservoirBall G C x r) ⊆
      reservoirBall G C x (r + 1) := by
  intro y hy
  rcases mem_relativeExternalNeighborhood.1 hy with
    ⟨hyCB, _hyB, a, haB, hya⟩
  rcases Finset.mem_sdiff.mp hyCB with ⟨hyC, _hyNotB⟩
  rcases mem_reservoirBall.1 haB with ⟨_haC, p, hplen, hpC⟩
  refine mem_reservoirBall.2 ⟨hyC, p.concat hya.symm, ?_, ?_⟩
  · rw [_root_.SimpleGraph.Walk.length_concat]
    omega
  · intro z hz
    rw [_root_.SimpleGraph.Walk.support_concat] at hz
    rcases List.mem_append.1 hz with hzOld | hzLast
    · exact hpC z hzOld
    · have hzy : z = y := by simpa using hzLast
      simpa [hzy] using hyC

/-- A reservoir ball and its paper frontier are both contained in the next
reservoir ball. -/
theorem reservoirBall_union_frontier_subset_succ [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {C : Finset V} {x : V} {r : ℕ} :
    reservoirBall G C x r ∪
        relativeExternalNeighborhood G (reservoirBall G C x r)
          (C \ reservoirBall G C x r) ⊆
      reservoirBall G C x (r + 1) := by
  intro y hy
  rcases Finset.mem_union.mp hy with hyB | hyF
  · exact reservoirBall_mono_radius (G := G) (C := C) (x := x)
      (Nat.le_succ r) hyB
  · exact relativeExternalNeighborhood_reservoirBall_subset_succ hyF

/-- One BFS step grows by at least the size of the relative frontier. -/
theorem reservoirBall_card_add_frontier_le_succ [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {C : Finset V} {x : V} {r : ℕ} :
    (reservoirBall G C x r).card +
        (relativeExternalNeighborhood G (reservoirBall G C x r)
          (C \ reservoirBall G C x r)).card ≤
      (reservoirBall G C x (r + 1)).card := by
  classical
  let B := reservoirBall G C x r
  let F := relativeExternalNeighborhood G B (C \ B)
  have hdisj : Disjoint B F := by
    rw [Finset.disjoint_left]
    intro y hyB hyF
    exact (Finset.mem_sdiff.mp
      ((mem_relativeExternalNeighborhood.1 hyF).1)).2 hyB
  have hsubset : B ∪ F ⊆ reservoirBall G C x (r + 1) := by
    simpa [B, F] using
      (reservoirBall_union_frontier_subset_succ
        (G := G) (C := C) (x := x) (r := r))
  calc
    B.card + F.card = (B ∪ F).card := by
      rw [Finset.card_union_of_disjoint hdisj]
    _ ≤ (reservoirBall G C x (r + 1)).card :=
      Finset.card_le_card hsubset

/-- The “no small-expansion reservoir set” hypothesis corresponding to the
negation of the low-expansion branch of Lemma 8.2. -/
def NoSmallRelativeExpansion [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (C : Finset V) : Prop :=
  ∀ U : Finset V, U ⊆ C → U.Nonempty → 2 * U.card ≤ C.card →
    U.card <
      D * (relativeExternalNeighborhood G U (C \ U)).card

/-- Under `NoSmallRelativeExpansion`, every reservoir ball of size at most half
the reservoir has a frontier large enough for the BFS-growth recurrence. -/
theorem reservoirBall_card_lt_mul_frontier_of_noSmallRelativeExpansion
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} {C : Finset V} {x : V} {r : ℕ}
    (hno : NoSmallRelativeExpansion G D C)
    (hxC : x ∈ C)
    (hhalf : 2 * (reservoirBall G C x r).card ≤ C.card) :
    (reservoirBall G C x r).card <
      D * (relativeExternalNeighborhood G (reservoirBall G C x r)
        (C \ reservoirBall G C x r)).card := by
  exact hno (reservoirBall G C x r)
    (reservoirBall_subset_reservoir C x r)
    ⟨x, mem_reservoirBall_self (G := G) (C := C) (r := r) hxC⟩
    hhalf

/-- Under `NoSmallRelativeExpansion`, a reservoir ball of size at most half the
reservoir strictly grows after one BFS step. -/
theorem reservoirBall_card_lt_succ_of_noSmallRelativeExpansion
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} {C : Finset V} {x : V} {r : ℕ}
    (hno : NoSmallRelativeExpansion G D C)
    (hxC : x ∈ C)
    (hhalf : 2 * (reservoirBall G C x r).card ≤ C.card) :
    (reservoirBall G C x r).card <
      (reservoirBall G C x (r + 1)).card := by
  classical
  let B := reservoirBall G C x r
  let F := relativeExternalNeighborhood G B (C \ B)
  have hfrontier : B.card < D * F.card := by
    simpa [B, F] using
      reservoirBall_card_lt_mul_frontier_of_noSmallRelativeExpansion
        (G := G) (D := D) (C := C) (x := x) (r := r)
        hno hxC hhalf
  have hFpos : 0 < F.card := by
    by_contra hFzero
    have hFzero' : F.card = 0 := Nat.eq_zero_of_not_pos hFzero
    simp [hFzero'] at hfrontier
  have hstep :
      B.card + F.card ≤ (reservoirBall G C x (r + 1)).card := by
    simpa [B, F] using
      (reservoirBall_card_add_frontier_le_succ
        (G := G) (C := C) (x := x) (r := r))
  have hlt : B.card < (reservoirBall G C x (r + 1)).card :=
    (Nat.lt_add_of_pos_right hFpos).trans_le hstep
  simpa [B] using hlt

/-- If all reservoir balls up to radius `m` have size at most half the
reservoir, then the radius-`m` ball contains at least `m+1` vertices.  This is
the finite termination core of the BFS-growth proof. -/
theorem reservoirBall_card_ge_succ_of_all_half
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} {C : Finset V} {x : V}
    (hno : NoSmallRelativeExpansion G D C)
    (hxC : x ∈ C) :
    ∀ m : ℕ,
      (∀ k : ℕ, k ≤ m →
        2 * (reservoirBall G C x k).card ≤ C.card) →
      m + 1 ≤ (reservoirBall G C x m).card := by
  intro m
  induction m with
  | zero =>
      intro _hhalf
      exact Nat.succ_le_of_lt
        (Finset.card_pos.mpr
          ⟨x, mem_reservoirBall_self (G := G) (C := C) (r := 0) hxC⟩)
  | succ m ih =>
      intro hhalf
      have hhalf_m :
          2 * (reservoirBall G C x m).card ≤ C.card :=
        hhalf m (Nat.le_succ m)
      have hlt :
          (reservoirBall G C x m).card <
            (reservoirBall G C x (m + 1)).card :=
        reservoirBall_card_lt_succ_of_noSmallRelativeExpansion
          (G := G) (D := D) (C := C) (x := x) (r := m)
          hno hxC hhalf_m
      have hih :
          m + 1 ≤ (reservoirBall G C x m).card :=
        ih (by
          intro k hk
          exact hhalf k (hk.trans (Nat.le_succ m)))
      omega

/-- Linear-radius fallback from the BFS-growth proof: under no small relative
expansion, every root has a reservoir ball larger than half the reservoir by
radius `|C|`.  The logarithmic refinement needed for the final quantitative
Theorem 8.1 strengthens this lemma. -/
theorem reservoirBall_large_by_card_of_noSmallRelativeExpansion
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} {C : Finset V} {x : V}
    (hno : NoSmallRelativeExpansion G D C)
    (hxC : x ∈ C) :
    C.card < 2 * (reservoirBall G C x C.card).card := by
  by_contra hnot
  have hhalf_all :
      ∀ k : ℕ, k ≤ C.card →
        2 * (reservoirBall G C x k).card ≤ C.card := by
    intro k hk
    by_contra hhalf
    have hlarge : C.card < 2 * (reservoirBall G C x k).card :=
      Nat.lt_of_not_ge hhalf
    have hmono :
        reservoirBall G C x k ⊆ reservoirBall G C x C.card :=
      reservoirBall_mono_radius (G := G) (C := C) (x := x) hk
    have hcard :
        (reservoirBall G C x k).card ≤
          (reservoirBall G C x C.card).card :=
      Finset.card_le_card hmono
    exact hnot (hlarge.trans_le (Nat.mul_le_mul_left 2 hcard))
  have hge :
      C.card + 1 ≤ (reservoirBall G C x C.card).card :=
    reservoirBall_card_ge_succ_of_all_half
      (G := G) (D := D) (C := C) (x := x) hno hxC C.card
      hhalf_all
  have hle :
      (reservoirBall G C x C.card).card ≤ C.card :=
    Finset.card_le_card (reservoirBall_subset_reservoir C x C.card)
  omega

/-- Quantitative BFS growth: if the radius-`r + D` ball is still at most half
the reservoir, then the radius-`r + D` ball has more than twice as many
vertices as the radius-`r` ball.  This is the doubling step used in the
logarithmic refinement of Lemma 8.2. -/
theorem reservoirBall_card_double_after_radius_add
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} (hDpos : 0 < D) {C : Finset V} {x : V} {r : ℕ}
    (hno : NoSmallRelativeExpansion G D C)
    (hxC : x ∈ C)
    (hhalf_end :
      2 * (reservoirBall G C x (r + D)).card ≤ C.card) :
    2 * (reservoirBall G C x r).card <
      (reservoirBall G C x (r + D)).card := by
  classical
  let base := (reservoirBall G C x r).card
  have hclaim :
      ∀ t : ℕ, t ≤ D →
        D * base + t * (base + 1) ≤
          D * (reservoirBall G C x (r + t)).card := by
    intro t ht
    induction t with
    | zero =>
        simp [base]
    | succ t ih =>
        have htD : t < D := Nat.succ_le_iff.mp ht
        have ht_le_D : t ≤ D := Nat.le_of_lt htD
        have ih' := ih ht_le_D
        let Bt := reservoirBall G C x (r + t)
        let F := relativeExternalNeighborhood G Bt (C \ Bt)
        have hBt_subset_end :
            Bt ⊆ reservoirBall G C x (r + D) := by
          exact reservoirBall_mono_radius
            (G := G) (C := C) (x := x) (by omega)
        have hBt_card_le_end :
            Bt.card ≤ (reservoirBall G C x (r + D)).card :=
          Finset.card_le_card hBt_subset_end
        have hhalf_t : 2 * Bt.card ≤ C.card := by
          omega
        have hfrontBt : Bt.card < D * F.card := by
          simpa [Bt, F] using
            reservoirBall_card_lt_mul_frontier_of_noSmallRelativeExpansion
              (G := G) (D := D) (C := C) (x := x) (r := r + t)
              hno hxC hhalf_t
        have hbase_le_Bt : base ≤ Bt.card := by
          have hsubset :
              reservoirBall G C x r ⊆ Bt := by
            exact reservoirBall_mono_radius
              (G := G) (C := C) (x := x) (by omega)
          simpa [base, Bt] using Finset.card_le_card hsubset
        have hfront : base + 1 ≤ D * F.card :=
          Nat.succ_le_of_lt (hbase_le_Bt.trans_lt hfrontBt)
        have hstep :
            Bt.card + F.card ≤
              (reservoirBall G C x (r + t + 1)).card := by
          simpa [Bt, F] using
            (reservoirBall_card_add_frontier_le_succ
              (G := G) (C := C) (x := x) (r := r + t))
        have hstepD :
            D * Bt.card + D * F.card ≤
              D * (reservoirBall G C x (r + t + 1)).card := by
          have hmul := Nat.mul_le_mul_left D hstep
          rwa [Nat.mul_add] at hmul
        have hcombine :
            D * base + t * (base + 1) + (base + 1) ≤
              D * Bt.card + D * F.card :=
          Nat.add_le_add ih' hfront
        have hnext :
            D * base + (t + 1) * (base + 1) ≤
              D * (reservoirBall G C x (r + (t + 1))).card := by
          calc
            D * base + (t + 1) * (base + 1)
                = D * base + t * (base + 1) + (base + 1) := by
                  ring_nf
            _ ≤ D * Bt.card + D * F.card := hcombine
            _ ≤ D * (reservoirBall G C x (r + t + 1)).card := hstepD
            _ = D * (reservoirBall G C x (r + (t + 1))).card := by
                  ring_nf
        exact hnext
  have hend :
      D * base + D * (base + 1) ≤
        D * (reservoirBall G C x (r + D)).card :=
    hclaim D le_rfl
  have hmul :
      D * (2 * base + 1) ≤
        D * (reservoirBall G C x (r + D)).card := by
    calc
      D * (2 * base + 1) = D * base + D * (base + 1) := by
        ring_nf
      _ ≤ D * (reservoirBall G C x (r + D)).card := hend
  have hcancel :
      2 * base + 1 ≤ (reservoirBall G C x (r + D)).card :=
    le_of_mul_le_mul_left hmul hDpos
  omega

/-- Logarithmic reservoir-ball growth in `Nat.clog` form.  If every
at-most-half reservoir set has large relative neighborhood, then by radius
`D * clog₂ |C|` every reservoir ball has more than half of `C`.

This is the quantitative heart of Lemma 8.2; a later bridge converts
`Nat.clog` into the `Nat.log` convention used by the Theorem 8.1 constants. -/
theorem reservoirBall_large_by_mul_clog_of_noSmallRelativeExpansion
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} (hDpos : 0 < D) {C : Finset V} {x : V}
    (hno : NoSmallRelativeExpansion G D C)
    (hxC : x ∈ C) :
    C.card <
      2 * (reservoirBall G C x (D * Nat.clog 2 C.card)).card := by
  classical
  let L := Nat.clog 2 C.card
  by_contra hnot
  have hfinalHalf :
      2 * (reservoirBall G C x (D * L)).card ≤ C.card := by
    exact Nat.le_of_not_gt hnot
  have hpow_le :
      ∀ t : ℕ, t ≤ L →
        2 ^ t ≤ (reservoirBall G C x (D * t)).card := by
    intro t ht
    induction t with
    | zero =>
        exact Nat.succ_le_of_lt
          (Finset.card_pos.mpr
            ⟨x, by
              simpa using
                (mem_reservoirBall_self
                  (G := G) (C := C) (r := 0) hxC)⟩)
    | succ t ih =>
        have ht_le_L : t ≤ L := Nat.le_of_succ_le ht
        have ih' := ih ht_le_L
        have hrad_le_final : D * t + D ≤ D * L := by
          rw [← Nat.mul_succ]
          exact Nat.mul_le_mul_left D ht
        have hhalf_end :
            2 * (reservoirBall G C x (D * t + D)).card ≤ C.card := by
          have hsubset :
              reservoirBall G C x (D * t + D) ⊆
                reservoirBall G C x (D * L) :=
            reservoirBall_mono_radius
              (G := G) (C := C) (x := x) hrad_le_final
          have hcard :
              (reservoirBall G C x (D * t + D)).card ≤
                (reservoirBall G C x (D * L)).card :=
            Finset.card_le_card hsubset
          exact (Nat.mul_le_mul_left 2 hcard).trans hfinalHalf
        have hdouble :
            2 * (reservoirBall G C x (D * t)).card <
              (reservoirBall G C x (D * t + D)).card :=
          reservoirBall_card_double_after_radius_add
            (G := G) (D := D) hDpos (C := C) (x := x)
            (r := D * t) hno hxC hhalf_end
        have hpow_succ :
            2 ^ (t + 1) ≤
              (reservoirBall G C x (D * t + D)).card := by
          have hmul :
              2 * 2 ^ t ≤
                2 * (reservoirBall G C x (D * t)).card :=
            Nat.mul_le_mul_left 2 ih'
          have hlt :
              2 * 2 ^ t <
                (reservoirBall G C x (D * t + D)).card :=
            hmul.trans_lt hdouble
          simpa [pow_succ', Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc] using hlt.le
        simpa [Nat.mul_succ] using hpow_succ
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨x, hxC⟩
  have hC_le_pow : C.card ≤ 2 ^ L :=
    Nat.le_pow_clog Nat.one_lt_two C.card
  have hC_le_ball :
      C.card ≤ (reservoirBall G C x (D * L)).card :=
    hC_le_pow.trans (hpow_le L le_rfl)
  omega

/-- Two subsets of the same finite reservoir, each larger than half of it, must
intersect. -/
theorem exists_mem_inter_of_two_mul_card_gt [DecidableEq V]
    {C X Y : Finset V}
    (hX : X ⊆ C) (hY : Y ⊆ C)
    (hXlarge : C.card < 2 * X.card)
    (hYlarge : C.card < 2 * Y.card) :
    ∃ z : V, z ∈ X ∧ z ∈ Y := by
  classical
  by_contra hdisjoint
  push Not at hdisjoint
  have hDisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro z hzX hzY
    exact hdisjoint z hzX hzY
  have hUnionSubset : X ∪ Y ⊆ C := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzX | hzY
    · exact hX hzX
    · exact hY hzY
  have hsum_le : X.card + Y.card ≤ C.card := by
    rw [← Finset.card_union_of_disjoint hDisj]
    exact Finset.card_le_card hUnionSubset
  omega

/-- If the two reservoir balls around `x` and `y` intersect, then there is a
walk from `x` to `y` of length at most the sum of the two radii, with support
inside the reservoir. -/
theorem exists_reservoir_walk_of_mem_ball_inter [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {C : Finset V} {x y z : V} {r s : ℕ}
    (hzx : z ∈ reservoirBall G C x r)
    (hzy : z ∈ reservoirBall G C y s) :
    ∃ p : G.Walk x y,
      p.length ≤ r + s ∧ ∀ w : V, w ∈ p.support → w ∈ C := by
  rcases mem_reservoirBall.1 hzx with ⟨_hzC₁, px, hpxLen, hpxC⟩
  rcases mem_reservoirBall.1 hzy with ⟨_hzC₂, py, hpyLen, hpyC⟩
  refine ⟨px.append py.reverse, ?_, ?_⟩
  · rw [_root_.SimpleGraph.Walk.length_append,
      _root_.SimpleGraph.Walk.length_reverse]
    omega
  · intro w hw
    rw [_root_.SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hwx | hwy
    · exact hpxC w hwx
    · rw [_root_.SimpleGraph.Walk.support_reverse] at hwy
      exact hpyC w (by simpa using hwy)

/-- If every radius-`m` reservoir ball has more than half of the reservoir,
then any two reservoir vertices can be connected by a walk of length at most
`2*m` whose support stays inside the reservoir. -/
theorem exists_reservoir_walk_of_large_reservoirBalls [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {C : Finset V} {m : ℕ}
    (hlarge :
      ∀ x : V, x ∈ C →
        C.card < 2 * (reservoirBall G C x m).card)
    {x y : V} (hxC : x ∈ C) (hyC : y ∈ C) :
    ∃ p : G.Walk x y,
      p.length ≤ 2 * m ∧ ∀ z : V, z ∈ p.support → z ∈ C := by
  rcases exists_mem_inter_of_two_mul_card_gt
      (reservoirBall_subset_reservoir C x m)
      (reservoirBall_subset_reservoir C y m)
      (hlarge x hxC) (hlarge y hyC) with
    ⟨z, hzx, hzy⟩
  rcases exists_reservoir_walk_of_mem_ball_inter
      (G := G) (C := C) (x := x) (y := y)
      (z := z) (r := m) (s := m) hzx hzy with
    ⟨p, hpLen, hpC⟩
  refine ⟨p, ?_, hpC⟩
  omega

/-- State-machine wrapper for
`exists_reservoir_walk_of_large_reservoirBalls`. -/
theorem reservoirDiameterBound_of_large_reservoirBalls
    [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {H : _root_.SimpleGraph W}
    {d r m : ℕ}
    (R : Theorem81InvariantState H G d r)
    (hlarge :
      ∀ x : V, x ∈ R.state.C →
        R.state.C.card < 2 * (reservoirBall G R.state.C x m).card) :
    Theorem81InvariantState.ReservoirDiameterBound R (2 * m) := by
  intro x hxC y hyC
  exact exists_reservoir_walk_of_large_reservoirBalls
    (G := G) (C := R.state.C) (m := m) hlarge hxC hyC

/-- Linear-diameter fallback from the no-small-expansion branch.  This is the
same BFS mechanism as Lemma 8.2, with the logarithmic growth estimate still to
be sharpened. -/
theorem exists_reservoir_walk_of_noSmallRelativeExpansion_card_bound
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} {C : Finset V}
    (hno : NoSmallRelativeExpansion G D C)
    {x y : V} (hxC : x ∈ C) (hyC : y ∈ C) :
    ∃ p : G.Walk x y,
      p.length ≤ 2 * C.card ∧ ∀ z : V, z ∈ p.support → z ∈ C := by
  exact exists_reservoir_walk_of_large_reservoirBalls
    (G := G) (C := C) (m := C.card)
    (fun z hzC =>
      reservoirBall_large_by_card_of_noSmallRelativeExpansion
        (G := G) (D := D) (C := C) (x := z) hno hzC)
    hxC hyC

/-- Logarithmic-diameter form of the no-small-expansion branch, using
`Nat.clog`. -/
theorem exists_reservoir_walk_of_noSmallRelativeExpansion_clog_bound
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} (hDpos : 0 < D) {C : Finset V}
    (hno : NoSmallRelativeExpansion G D C)
    {x y : V} (hxC : x ∈ C) (hyC : y ∈ C) :
    ∃ p : G.Walk x y,
      p.length ≤ 2 * (D * Nat.clog 2 C.card) ∧
        ∀ z : V, z ∈ p.support → z ∈ C := by
  exact exists_reservoir_walk_of_large_reservoirBalls
    (G := G) (C := C) (m := D * Nat.clog 2 C.card)
    (fun z hzC =>
      reservoirBall_large_by_mul_clog_of_noSmallRelativeExpansion
        (G := G) (D := D) hDpos (C := C) (x := z) hno hzC)
    hxC hyC

/-- Negating `NoSmallRelativeExpansion` gives the low-expansion branch with
the concrete paper frontier `N_G(U, C \ U)`. -/
theorem exists_lowExpansionSet_of_not_noSmallRelativeExpansion
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} {C : Finset V}
    (hnot : ¬ NoSmallRelativeExpansion G D C) :
    ∃ U frontierU : Finset V,
      U ⊆ C ∧
      U.Nonempty ∧
      2 * U.card ≤ C.card ∧
      IsRelativeExternalNeighborhood G U (C \ U) frontierU ∧
      D * frontierU.card ≤ U.card := by
  classical
  unfold NoSmallRelativeExpansion at hnot
  push Not at hnot
  rcases hnot with ⟨U, hUsubset, hUnonempty, hUhalf, hsmall⟩
  refine ⟨U, relativeExternalNeighborhood G U (C \ U),
    hUsubset, hUnonempty, hUhalf, ?_, hsmall⟩
  exact isRelativeExternalNeighborhood_relativeExternalNeighborhood G U (C \ U)

/-- A self-contained finite dichotomy following the first half of Lemma 8.2:
either there is a low-expansion set with the paper frontier `N_G(U, C \ U)`,
or the reservoir has a linear diameter bound.  The final Theorem 8.1 proof
needs the logarithmic strengthening of the right-hand side. -/
theorem lowExpansionSet_or_reservoirDiameter_card_bound
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    (D : ℕ) {C : Finset V} (hCnonempty : C.Nonempty) :
    (∃ U frontierU : Finset V,
      U ⊆ C ∧
      U.Nonempty ∧
      2 * U.card ≤ C.card ∧
      IsRelativeExternalNeighborhood G U (C \ U) frontierU ∧
      D * frontierU.card ≤ U.card) ∨
    (C.Nonempty ∧
      ∃ m : ℕ,
        (∀ x : V, x ∈ C →
          ∀ y : V, y ∈ C →
            ∃ p : G.Walk x y,
              p.length ≤ m ∧ ∀ z : V, z ∈ p.support → z ∈ C) ∧
        m ≤ 2 * C.card) := by
  by_cases hno : NoSmallRelativeExpansion G D C
  · right
    refine ⟨hCnonempty, 2 * C.card, ?_, le_rfl⟩
    intro x hxC y hyC
    exact exists_reservoir_walk_of_noSmallRelativeExpansion_card_bound
      (G := G) (D := D) (C := C) hno hxC hyC
  · left
    exact exists_lowExpansionSet_of_not_noSmallRelativeExpansion
      (G := G) (D := D) (C := C) hno

/-- Lemma 8.2 in the form proved so far: either the paper low-expansion set
exists, or the reservoir has diameter at most `2 * D * clog₂ |C|`. -/
theorem lowExpansionSet_or_reservoirDiameter_clog_bound
    [DecidableEq V]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {D : ℕ} (hDpos : 0 < D) {C : Finset V} (hCnonempty : C.Nonempty) :
    (∃ U frontierU : Finset V,
      U ⊆ C ∧
      U.Nonempty ∧
      2 * U.card ≤ C.card ∧
      IsRelativeExternalNeighborhood G U (C \ U) frontierU ∧
      D * frontierU.card ≤ U.card) ∨
    (C.Nonempty ∧
      ∃ m : ℕ,
        (∀ x : V, x ∈ C →
          ∀ y : V, y ∈ C →
            ∃ p : G.Walk x y,
              p.length ≤ m ∧ ∀ z : V, z ∈ p.support → z ∈ C) ∧
        m ≤ 2 * (D * Nat.clog 2 C.card)) := by
  by_cases hno : NoSmallRelativeExpansion G D C
  · right
    refine ⟨hCnonempty, 2 * (D * Nat.clog 2 C.card), ?_, le_rfl⟩
    intro x hxC y hyC
    exact exists_reservoir_walk_of_noSmallRelativeExpansion_clog_bound
      (G := G) (D := D) hDpos (C := C) hno hxC hyC
  · left
    exact exists_lowExpansionSet_of_not_noSmallRelativeExpansion
      (G := G) (D := D) (C := C) hno

/-- State-machine wrapper for the linear-diameter fallback. -/
theorem reservoirDiameterBound_of_noSmallRelativeExpansion_card_bound
    [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {H : _root_.SimpleGraph W}
    {d r D : ℕ}
    (R : Theorem81InvariantState H G d r)
    (hno : NoSmallRelativeExpansion G D R.state.C) :
    Theorem81InvariantState.ReservoirDiameterBound R
      (2 * R.state.C.card) := by
  intro x hxC y hyC
  exact exists_reservoir_walk_of_noSmallRelativeExpansion_card_bound
    (G := G) (D := D) (C := R.state.C) hno hxC hyC

/-- State-machine wrapper for the logarithmic `Nat.clog` diameter fallback. -/
theorem reservoirDiameterBound_of_noSmallRelativeExpansion_clog_bound
    [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {H : _root_.SimpleGraph W}
    {d r D : ℕ} (hDpos : 0 < D)
    (R : Theorem81InvariantState H G d r)
    (hno : NoSmallRelativeExpansion G D R.state.C) :
    Theorem81InvariantState.ReservoirDiameterBound R
      (2 * (D * Nat.clog 2 R.state.C.card)) := by
  intro x hxC y hyC
  exact exists_reservoir_walk_of_noSmallRelativeExpansion_clog_bound
    (G := G) (D := D) hDpos (C := R.state.C) hno hxC hyC

/-- State-machine version of the linear Lemma-8.2 dichotomy.  This theorem is
useful for checking the Theorem 8.1 state-machine wiring independently of the
remaining logarithmic growth estimate. -/
theorem theorem81_lowExpansion_or_reservoirDiameter_card_bound
    [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {H : _root_.SimpleGraph W}
    {d r : ℕ}
    (R : Theorem81InvariantState H G d r)
    (hCnonempty : R.state.C.Nonempty) :
    (∃ U frontierU : Finset V,
      U ⊆ R.state.C ∧
      U.Nonempty ∧
      2 * U.card ≤ R.state.C.card ∧
      IsRelativeExternalNeighborhood G U (R.state.C \ U) frontierU ∧
      d * frontierU.card ≤ U.card) ∨
    (R.state.C.Nonempty ∧
      ∃ m : ℕ,
        Theorem81InvariantState.ReservoirDiameterBound R m ∧
        m ≤ 2 * R.state.C.card) := by
  rcases lowExpansionSet_or_reservoirDiameter_card_bound
      (G := G) d hCnonempty with hlow | hdiam
  · exact Or.inl hlow
  · rcases hdiam with ⟨hC, m, hwalks, hm⟩
    exact Or.inr ⟨hC, m, hwalks, hm⟩

/-- State-machine version of the logarithmic `Nat.clog` Lemma-8.2 dichotomy. -/
theorem theorem81_lowExpansion_or_reservoirDiameter_clog_bound
    [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {H : _root_.SimpleGraph W}
    {d r : ℕ} (hdpos : 0 < d)
    (R : Theorem81InvariantState H G d r)
    (hCnonempty : R.state.C.Nonempty) :
    (∃ U frontierU : Finset V,
      U ⊆ R.state.C ∧
      U.Nonempty ∧
      2 * U.card ≤ R.state.C.card ∧
      IsRelativeExternalNeighborhood G U (R.state.C \ U) frontierU ∧
      d * frontierU.card ≤ U.card) ∨
    (R.state.C.Nonempty ∧
      ∃ m : ℕ,
        Theorem81InvariantState.ReservoirDiameterBound R m ∧
        m ≤ 2 * (d * Nat.clog 2 R.state.C.card)) := by
  rcases lowExpansionSet_or_reservoirDiameter_clog_bound
      (G := G) (D := d) hdpos hCnonempty with hlow | hdiam
  · exact Or.inl hlow
  · rcases hdiam with ⟨hC, m, hwalks, hm⟩
    exact Or.inr ⟨hC, m, hwalks, hm⟩

/-- State-machine Lemma-8.2 dichotomy with the diameter bound expressed using
the host logarithm rather than the reservoir ceiling logarithm. -/
theorem theorem81_lowExpansion_or_reservoirDiameter_log_bound
    [Fintype V] [DecidableEq V]
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} [DecidableRel G.Adj]
    {H : _root_.SimpleGraph W}
    {d r : ℕ} (hdpos : 0 < d)
    (hlog : 0 < Nat.log 2 (Fintype.card V))
    (R : Theorem81InvariantState H G d r)
    (hCnonempty : R.state.C.Nonempty) :
    (∃ U frontierU : Finset V,
      U ⊆ R.state.C ∧
      U.Nonempty ∧
      2 * U.card ≤ R.state.C.card ∧
      IsRelativeExternalNeighborhood G U (R.state.C \ U) frontierU ∧
      d * frontierU.card ≤ U.card) ∨
    (R.state.C.Nonempty ∧
      ∃ m : ℕ,
        Theorem81InvariantState.ReservoirDiameterBound R m ∧
        m ≤ 4 * d * Nat.log 2 (Fintype.card V)) := by
  rcases theorem81_lowExpansion_or_reservoirDiameter_clog_bound
      (G := G) (d := d) hdpos R hCnonempty with hlow | hdiam
  · exact Or.inl hlow
  · rcases hdiam with ⟨hC, m, hdiam, hm⟩
    right
    refine ⟨hC, m, hdiam, ?_⟩
    have hclog :
        Nat.clog 2 R.state.C.card ≤
          2 * Nat.log 2 (Fintype.card V) :=
      reservoir_clog_two_le_two_host_log_two
        (V := V) R.state.C hlog
    calc
      m ≤ 2 * (d * Nat.clog 2 R.state.C.card) := hm
      _ ≤ 2 * (d * (2 * Nat.log 2 (Fintype.card V))) := by
        exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left d hclog)
      _ = 4 * d * Nat.log 2 (Fintype.card V) := by
        ring_nf

/-- The formal Lemma-8.2 reservoir alternative for the Theorem 8.1 state
machine, conditional only on the proof that nonterminal states queried by the
algorithm have nonempty reservoirs.

The explicit branch scale `15 * separatorScale` absorbs the path-union factor
`3`, the two-sided diameter bound, and the `clog`/`log` conversion. -/
theorem theorem81ReservoirAlternativeAt_of_nonempty_reservoir
    {separatorScale targetScale n₀ : ℕ}
    (hsepPos : 0 < separatorScale)
    (hn₀ : 2 ≤ n₀)
    (hCnonempty :
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        {W : Type v} [Fintype W] [DecidableEq W]
        (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
        (H : _root_.SimpleGraph W) [DecidableRel H.Adj] [Fintype H.edgeSet],
          MaxDegreeAtMost H 3 →
            n₀ ≤ Fintype.card V →
              TargetSmallForHost (V := V) H targetScale →
                ∀ R : Theorem81InvariantState H G separatorScale
                    ((15 * separatorScale) *
                      Nat.log 2 (Fintype.card V)),
                  ¬ Theorem81InvariantState.FirstCrossingTerminal R →
                    R.state.C.Nonempty) :
    Theorem81ReservoirAlternativeAt.{u, v}
      separatorScale (15 * separatorScale) targetScale n₀ := by
  intro V _ _ W _ _ G _ H _ _ hmax hn hsmall R hnot
  have hlog : 0 < Nat.log 2 (Fintype.card V) := by
    rw [Nat.log_pos_iff]
    exact ⟨hn₀.trans hn, Nat.one_lt_two⟩
  have hC : R.state.C.Nonempty :=
    hCnonempty G H hmax hn hsmall R hnot
  rcases theorem81_lowExpansion_or_reservoirDiameter_log_bound
      (G := G) (H := H) (d := separatorScale)
      hsepPos hlog R hC with hlow | hdiam
  · left
    rcases hlow with
      ⟨U, frontierU, hUsubset, hUnonempty, _hUhalf,
        hfrontierU, hUsmall⟩
    exact ⟨U, frontierU, hUsubset, hUnonempty, hfrontierU, hUsmall⟩
  · right
    rcases hdiam with ⟨hCnonempty', m, hdiam, hm⟩
    refine ⟨hCnonempty', m, hdiam, ?_⟩
    let L := Nat.log 2 (Fintype.card V)
    have hLpos : 0 < L := hlog
    have hprodPos : 1 ≤ separatorScale * L := by
      exact Nat.succ_le_of_lt (Nat.mul_pos hsepPos hLpos)
    have hm' : m ≤ 4 * (separatorScale * L) := by
      simpa [L, Nat.mul_assoc] using hm
    have harith :
        3 * (m + 1) ≤ 15 * (separatorScale * L) := by
      omega
    calc
      3 * (m + 1) ≤ 15 * (separatorScale * L) := harith
      _ = (15 * separatorScale) * L := by ring_nf

end SimpleGraph

end Lax17Proofs
