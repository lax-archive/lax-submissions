import Lax17Proofs.Source.ChekuriChuzhoySection5Contraction
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Lax17Proofs

universe u v w

/-!
# Karger's finite cut-counting bound

This file proves the deterministic contraction lemma used in Step 3 of
Chekuri--Chuzhoy, *Degree-3 Treewidth Sparsifiers*.  Parallel edges are
retained by using the project's finite edge-indexed multigraph API.

The theorem is a slightly relaxed integer form of paper Theorem 5.5
(Karger, Corollary A.6): in a `C`-edge-connected `n`-vertex multigraph, the
number of oriented nontrivial cuts of value at most `a * C` is at most
`2 * n ^ (2 * a)`.  The harmless leading factor two accounts for the two
orientations of an undirected cut and keeps all small base cases uniform.
-/

namespace SimpleGraph
namespace TreewidthSparsifier
namespace Karger

open Finset
open ChekuriChuzhoySection5TerminalSkeleton
open ChekuriChuzhoySection5TerminalSkeleton.FiniteEdgeIndexedGraph


variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Named edges not crossing a vertex set. -/
noncomputable def noncrossingEdges
    (H : FiniteEdgeIndexedGraph W) (X : Finset W) : Finset H.Edge := by
  classical
  exact Finset.univ.filter fun e => ¬ H.Crosses X e

@[simp] theorem mem_noncrossingEdges
    (H : FiniteEdgeIndexedGraph W) (X : Finset W) (e : H.Edge) :
    e ∈ noncrossingEdges H X ↔ ¬ H.Crosses X e := by
  classical
  simp [noncrossingEdges]

theorem card_noncrossingEdges_add_boundary
    (H : FiniteEdgeIndexedGraph W) (X : Finset W) :
    (noncrossingEdges H X).card + (H.boundary X).card =
      Fintype.card H.Edge := by
  classical
  rw [noncrossingEdges, boundary]
  simpa [Nat.add_comm] using
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset H.Edge)) (p := H.Crosses X)

/-- Oriented nonempty proper cuts of value at most `a * C`. -/
noncomputable def smallCuts
    (H : FiniteEdgeIndexedGraph W) (C a : ℕ) :
    Finset (Finset W) := by
  classical
  exact Finset.univ.filter fun X =>
    X.Nonempty ∧ X ≠ Finset.univ ∧ (H.boundary X).card ≤ a * C

@[simp] theorem mem_smallCuts
    (H : FiniteEdgeIndexedGraph W) (C a : ℕ) (X : Finset W) :
    X ∈ smallCuts H C a ↔
      X.Nonempty ∧ X ≠ Finset.univ ∧
        (H.boundary X).card ≤ a * C := by
  classical
  simp [smallCuts]

/-- The two endpoints of a noncrossing edge lie on the same side. -/
theorem endpoint_mem_iff_of_not_crosses
    (H : FiniteEdgeIndexedGraph W) (X : Finset W) (e : H.Edge)
    (h : ¬ H.Crosses X e) :
    H.left e ∈ X ↔ H.right e ∈ X := by
  simp only [Crosses] at h
  tauto

namespace Contraction

variable (H : FiniteEdgeIndexedGraph W) (e : H.Edge)

abbrev Vertex :=
  ContractVertex W (H.left e) (H.right e)

abbrev projection : W → Vertex H e :=
  ContractVertex.projection
    (p := H.left e) (q := H.right e)

/-- Project a vertex set through one edge contraction. -/
noncomputable def image (X : Finset W) : Finset (Vertex H e) :=
  X.image (projection H e)

theorem preimage_image_eq
    (X : Finset W) (hncross : ¬ H.Crosses X e) :
    ContractVertex.preimageFinset (image H e X) = X := by
  classical
  ext w
  constructor
  · intro hw
    rw [ContractVertex.mem_preimageFinset] at hw
    rcases Finset.mem_image.mp hw with ⟨x, hx, hproj⟩
    rcases ContractVertex.eq_or_both_endpoints_of_projection_eq
        hproj with h | ⟨hxend, hwend⟩
    · simpa [h] using hx
    · have hsame :=
        endpoint_mem_iff_of_not_crosses H X e hncross
      rcases hxend with (rfl | rfl) <;>
        rcases hwend with (rfl | rfl)
      · exact hx
      · exact hsame.mp hx
      · exact hsame.mpr hx
      · exact hx
  · intro hw
    rw [ContractVertex.mem_preimageFinset]
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

theorem image_nonempty
    {X : Finset W} (hX : X.Nonempty) :
    (image H e X).Nonempty :=
  hX.image _

theorem image_ne_univ
    {X : Finset W} (hX : X ≠ Finset.univ)
    (hncross : ¬ H.Crosses X e) :
    image H e X ≠ Finset.univ := by
  intro himage
  have hpre :
      ContractVertex.preimageFinset (image H e X) =
        (Finset.univ : Finset W) := by
    ext w
    simp [himage]
  exact hX ((preimage_image_eq H e X hncross).symm.trans hpre)

/-- A small cut not crossed by the contracted edge descends to a small cut of
the contracted multigraph. -/
theorem image_mem_smallCuts
    {C a : ℕ} {X : Finset W}
    (hX : X ∈ smallCuts H C a)
    (hncross : ¬ H.Crosses X e) :
    image H e X ∈ smallCuts (H.contractEdge e) C a := by
  rw [mem_smallCuts] at hX ⊢
  refine ⟨image_nonempty H e hX.1,
    image_ne_univ H e hX.2.1 hncross, ?_⟩
  rw [contractEdge_boundary_card, preimage_image_eq H e X hncross]
  exact hX.2.2

/-- Projecting noncrossing cuts is injective. -/
theorem image_injective_on_noncrossing :
    Set.InjOn (image H e)
      {X : Finset W | ¬ H.Crosses X e} := by
  intro X hX Y hY hXY
  rw [← preimage_image_eq H e X hX,
    ← preimage_image_eq H e Y hY, hXY]

end Contraction

/-- Small cuts not crossed by a fixed named edge. -/
noncomputable def smallCutsNotCrossing
    (H : FiniteEdgeIndexedGraph W) (C a : ℕ) (e : H.Edge) :
    Finset (Finset W) := by
  classical
  exact (smallCuts H C a).filter fun X => ¬ H.Crosses X e

@[simp] theorem mem_smallCutsNotCrossing
    (H : FiniteEdgeIndexedGraph W) (C a : ℕ) (e : H.Edge)
    (X : Finset W) :
    X ∈ smallCutsNotCrossing H C a e ↔
      X ∈ smallCuts H C a ∧ ¬ H.Crosses X e := by
  classical
  simp [smallCutsNotCrossing]

/-- Small cuts avoiding a fixed edge inject into the small cuts after
contracting that edge. -/
theorem card_smallCuts_filter_not_crosses_le_contract
    (H : FiniteEdgeIndexedGraph W) (C a : ℕ) (e : H.Edge) :
    (smallCutsNotCrossing H C a e).card ≤
      (smallCuts (H.contractEdge e) C a).card := by
  classical
  let f :
      {X // X ∈ smallCutsNotCrossing H C a e} →
        {Y // Y ∈ smallCuts (H.contractEdge e) C a} :=
    fun X => ⟨Contraction.image H e X.1,
      Contraction.image_mem_smallCuts H e
        (mem_smallCutsNotCrossing H C a e X.1 |>.mp X.2).1
        (mem_smallCutsNotCrossing H C a e X.1 |>.mp X.2).2⟩
  have hf : Function.Injective f := by
    intro X Y hXY
    apply Subtype.ext
    apply Contraction.image_injective_on_noncrossing H e
    · exact (mem_smallCutsNotCrossing H C a e X.1 |>.mp X.2).2
    · exact (mem_smallCutsNotCrossing H C a e Y.1 |>.mp Y.2).2
    · exact congrArg Subtype.val hXY
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_le_of_injective f hf

/-! ## Degree sum -/

/-- An incidence with a named edge, represented as a dependent pair. -/
abbrev Incidence (H : FiniteEdgeIndexedGraph W) :=
  Σ w : W, {e : H.Edge // H.left e = w ∨ H.right e = w}

/-- Every named loopless edge has exactly two incidences. -/
noncomputable def incidenceEquiv
    (H : FiniteEdgeIndexedGraph W) :
    Incidence H ≃ H.Edge × Fin 2 := by
  classical
  let f : H.Edge × Fin 2 → Incidence H := fun x =>
    if x.2.1 = 0 then
      ⟨H.left x.1, ⟨x.1, Or.inl rfl⟩⟩
    else
      ⟨H.right x.1, ⟨x.1, Or.inr rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨e, i⟩ ⟨e', j⟩ hij
      fin_cases i <;> fin_cases j
      · have he : e = e' := by
          simpa only [f, if_pos rfl] using
            congrArg (fun z : Incidence H => z.2.1) hij
        simp [he]
      · have he : e = e' := by
          simpa only [f, if_pos rfl,
            if_neg (by omega : (1 : ℕ) ≠ 0)] using
              congrArg (fun z : Incidence H => z.2.1) hij
        subst e'
        simp only [f, if_pos rfl,
          if_neg (by omega : (1 : ℕ) ≠ 0)] at hij
        have := congrArg (fun z : Incidence H => z.1) hij
        exact (H.end_ne e this).elim
      · have he : e = e' := by
          simpa only [f, if_pos rfl,
            if_neg (by omega : (1 : ℕ) ≠ 0)] using
              congrArg (fun z : Incidence H => z.2.1) hij
        subst e'
        simp only [f, if_pos rfl,
          if_neg (by omega : (1 : ℕ) ≠ 0)] at hij
        have := congrArg (fun z : Incidence H => z.1) hij
        exact (H.end_ne e this.symm).elim
      · have he : e = e' := by
          simpa only [f, if_neg (by omega : (1 : ℕ) ≠ 0)] using
            congrArg (fun z : Incidence H => z.2.1) hij
        simp [he]
    · rintro ⟨w, e, he⟩
      rcases he with hleft | hright
      · subst w
        refine ⟨(e, 0), ?_⟩
        rfl
      · subst w
        refine ⟨(e, 1), ?_⟩
        rfl
  exact (Equiv.ofBijective f hf).symm

theorem sum_degree_eq_two_mul_edgeCard
    (H : FiniteEdgeIndexedGraph W) :
    (∑ w : W, H.degree w) = 2 * Fintype.card H.Edge := by
  classical
  have hdegree (w : W) :
      H.degree w =
        Fintype.card {e : H.Edge // H.left e = w ∨ H.right e = w} := by
    change (H.incidentEdges w).card =
      Fintype.card {e : H.Edge // H.left e = w ∨ H.right e = w}
    rw [← Fintype.card_coe]
    exact Fintype.card_congr {
      toFun := fun e => ⟨e.1, (H.mem_incidentEdges w e.1).mp e.2⟩
      invFun := fun e => ⟨e.1, (H.mem_incidentEdges w e.1).mpr e.2⟩
      left_inv := fun e => Subtype.ext rfl
      right_inv := fun e => Subtype.ext rfl
    }
  calc
    (∑ w : W, H.degree w) =
        ∑ w : W,
          Fintype.card
            {e : H.Edge // H.left e = w ∨ H.right e = w} := by
          apply Finset.sum_congr rfl
          intro w _hw
          exact hdegree w
    _ = Fintype.card (Incidence H) := by
          rw [Fintype.card_sigma]
    _ = Fintype.card (H.Edge × Fin 2) :=
          Fintype.card_congr (incidenceEquiv H)
    _ = 2 * Fintype.card H.Edge := by simp [Nat.mul_comm]

/-- Edge connectivity supplies the usual lower bound
`n * C <= 2m`. -/
theorem vertexCard_mul_connectivity_le_two_mul_edgeCard
    (H : FiniteEdgeIndexedGraph W) {C : ℕ}
    (hconn : H.IsEdgeConnected C)
    (hn : 2 ≤ Fintype.card W) :
    Fintype.card W * C ≤ 2 * Fintype.card H.Edge := by
  have hdegree : ∀ w : W, C ≤ H.degree w := by
    intro w
    have hex : ∃ z : W, z ≠ w := by
      by_contra h
      push Not at h
      have hsubsingleton : Subsingleton W := ⟨fun x y => (h x).trans (h y).symm⟩
      have : Fintype.card W ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun x y => hsubsingleton.elim x y)
      omega
    exact hconn.le_degree_of_exists_ne w hex
  calc
    Fintype.card W * C = ∑ _w : W, C := by simp
    _ ≤ ∑ w : W, H.degree w := Finset.sum_le_sum fun w _ => hdegree w
    _ = 2 * Fintype.card H.Edge := sum_degree_eq_two_mul_edgeCard H

/-! ## The contraction double count -/

/-- Count pairs consisting of a small cut and an edge that does not cross it,
first by edges and then by cuts. -/
theorem sum_smallCutsNotCrossing_eq_sum_noncrossingEdges
    (H : FiniteEdgeIndexedGraph W) (C a : ℕ) :
    (∑ e : H.Edge, (smallCutsNotCrossing H C a e).card) =
      ∑ X ∈ smallCuts H C a, (noncrossingEdges H X).card := by
  classical
  simp only [smallCutsNotCrossing, noncrossingEdges, Finset.card_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- The contraction injection bounds the double count from above whenever
every one-edge contraction has at most `B` small cuts. -/
theorem sum_smallCutsNotCrossing_le_of_contract_bound
    (H : FiniteEdgeIndexedGraph W) (C a B : ℕ)
    (hcontract :
      ∀ e : H.Edge, (smallCuts (H.contractEdge e) C a).card ≤ B) :
    (∑ e : H.Edge, (smallCutsNotCrossing H C a e).card) ≤
      Fintype.card H.Edge * B := by
  calc
    (∑ e : H.Edge, (smallCutsNotCrossing H C a e).card) ≤
        ∑ _e : H.Edge, B := by
      apply Finset.sum_le_sum
      intro e _he
      exact (card_smallCuts_filter_not_crosses_le_contract H C a e).trans
        (hcontract e)
    _ = Fintype.card H.Edge * B := by simp

/-- Every `a*C`-small cut avoids at least `m-a*C` named edges. -/
theorem smallCuts_mul_edgeCard_sub_le_sum_noncrossingEdges
    (H : FiniteEdgeIndexedGraph W) (C a : ℕ) :
    (smallCuts H C a).card * (Fintype.card H.Edge - a * C) ≤
      ∑ X ∈ smallCuts H C a, (noncrossingEdges H X).card := by
  have hpoint :
      ∀ X ∈ smallCuts H C a,
        Fintype.card H.Edge - a * C ≤
          (noncrossingEdges H X).card := by
    intro X hX
    have hboundary : (H.boundary X).card ≤ a * C :=
      (mem_smallCuts H C a X).mp hX |>.2.2
    have hpartition := card_noncrossingEdges_add_boundary H X
    omega
  calc
    (smallCuts H C a).card * (Fintype.card H.Edge - a * C) =
        ∑ _X ∈ smallCuts H C a,
          (Fintype.card H.Edge - a * C) := by simp
    _ ≤ ∑ X ∈ smallCuts H C a, (noncrossingEdges H X).card :=
      Finset.sum_le_sum fun X hX => hpoint X hX

/-- There are at most as many small cuts as vertex subsets. -/
theorem card_smallCuts_le_two_pow_vertexCard
    (H : FiniteEdgeIndexedGraph W) (C a : ℕ) :
    (smallCuts H C a).card ≤ 2 ^ Fintype.card W := by
  classical
  calc
    (smallCuts H C a).card ≤
        (Finset.univ : Finset (Finset W)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ Fintype.card W := by simp

/-- Exact binomial form of Karger's contraction bound.  The exponent
`d = 2*a` is the number of vertices at which the contraction recurrence
stops. -/
theorem card_smallCuts_le_two_pow_mul_choose
    (H : FiniteEdgeIndexedGraph W) {C a : ℕ}
    (hC : 0 < C) (ha : 0 < a)
    (hconn : H.IsEdgeConnected C)
    (hvertices : 2 * a ≤ Fintype.card W) :
    (smallCuts H C a).card ≤
      2 ^ (2 * a) * (Fintype.card W).choose (2 * a) := by
  classical
  induction hn : Fintype.card W using Nat.strong_induction_on generalizing W with
  | h n ih =>
      subst hn
      by_cases hbase : Fintype.card W = 2 * a
      · calc
          (smallCuts H C a).card ≤ 2 ^ Fintype.card W :=
            card_smallCuts_le_two_pow_vertexCard H C a
          _ = 2 ^ (2 * a) * (Fintype.card W).choose (2 * a) := by
            rw [hbase, Nat.choose_self, Nat.mul_one]
      · have hstrict : 2 * a < Fintype.card W := by omega
        let B : ℕ :=
          2 ^ (2 * a) * (Fintype.card W - 1).choose (2 * a)
        have hcontract :
            ∀ e : H.Edge,
              (smallCuts (H.contractEdge e) C a).card ≤ B := by
          intro e
          have hcard :
              Fintype.card
                  (ContractVertex W (H.left e) (H.right e)) =
                Fintype.card W - 1 :=
            ContractVertex.card (H.end_ne e)
          have hlt :
              Fintype.card
                  (ContractVertex W (H.left e) (H.right e)) <
                Fintype.card W := by
            rw [hcard]
            omega
          have hsize :
              2 * a ≤
                Fintype.card
                  (ContractVertex W (H.left e) (H.right e)) := by
            rw [hcard]
            omega
          have hi :=
            ih _ hlt (H.contractEdge e)
              (hconn.contractEdge e) hsize rfl
          simpa [B, hcard] using hi
        have hrec :
            (smallCuts H C a).card *
                (Fintype.card H.Edge - a * C) ≤
              Fintype.card H.Edge * B := by
          calc
            (smallCuts H C a).card *
                  (Fintype.card H.Edge - a * C) ≤
                ∑ X ∈ smallCuts H C a,
                  (noncrossingEdges H X).card :=
              smallCuts_mul_edgeCard_sub_le_sum_noncrossingEdges H C a
            _ = ∑ e : H.Edge,
                  (smallCutsNotCrossing H C a e).card :=
              (sum_smallCutsNotCrossing_eq_sum_noncrossingEdges H C a).symm
            _ ≤ Fintype.card H.Edge * B :=
              sum_smallCutsNotCrossing_le_of_contract_bound H C a B hcontract
        have hhandshake :
            Fintype.card W * C ≤ 2 * Fintype.card H.Edge :=
          vertexCard_mul_connectivity_le_two_mul_edgeCard H hconn (by
            have : 2 ≤ 2 * a := by omega
            omega)
        have hm : 0 < Fintype.card H.Edge := by
          nlinarith
        have haC : a * C ≤ Fintype.card H.Edge := by
          have hscaled := Nat.mul_le_mul_left a hhandshake
          nlinarith
        have hscaledHandshake :
            Fintype.card W * a * C ≤
              (2 * a) * Fintype.card H.Edge := by
          have hscaled := Nat.mul_le_mul_left a hhandshake
          nlinarith
        have hgap :
            (Fintype.card W - 2 * a) * Fintype.card H.Edge ≤
              Fintype.card W *
                (Fintype.card H.Edge - a * C) := by
          have hleft :
              (Fintype.card W - 2 * a) * Fintype.card H.Edge +
                  (2 * a) * Fintype.card H.Edge =
                Fintype.card W * Fintype.card H.Edge := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hvertices]
          have hright :
              Fintype.card W *
                    (Fintype.card H.Edge - a * C) +
                  Fintype.card W * (a * C) =
                Fintype.card W * Fintype.card H.Edge := by
            rw [← Nat.mul_add, Nat.sub_add_cancel haC]
          have hscaledHandshake' :
              Fintype.card W * (a * C) ≤
                (2 * a) * Fintype.card H.Edge := by
            simpa only [Nat.mul_assoc] using hscaledHandshake
          omega
        have hscaledGap := Nat.mul_le_mul_left
          (smallCuts H C a).card hgap
        have hscaledRec := Nat.mul_le_mul_left (Fintype.card W) hrec
        have hwithEdge :
            ((smallCuts H C a).card *
                (Fintype.card W - 2 * a)) *
                  Fintype.card H.Edge ≤
              (Fintype.card W * B) * Fintype.card H.Edge := by
          nlinarith
        have hcancel :
            (smallCuts H C a).card *
                (Fintype.card W - 2 * a) ≤
              Fintype.card W * B :=
          Nat.le_of_mul_le_mul_right hwithEdge hm
        have hchoose :
            (Fintype.card W - 2 * a) *
                (Fintype.card W).choose (2 * a) =
              Fintype.card W *
                (Fintype.card W - 1).choose (2 * a) := by
          have hc := Nat.choose_mul_succ_eq
            (Fintype.card W - 1) (2 * a)
          have hsucc : Fintype.card W - 1 + 1 = Fintype.card W := by
            omega
          rw [hsucc] at hc
          nlinarith
        have htargetMul :
            (smallCuts H C a).card *
                (Fintype.card W - 2 * a) ≤
              (2 ^ (2 * a) *
                  (Fintype.card W).choose (2 * a)) *
                (Fintype.card W - 2 * a) := by
          calc
            (smallCuts H C a).card *
                  (Fintype.card W - 2 * a) ≤
                Fintype.card W * B := hcancel
            _ = 2 ^ (2 * a) *
                  (Fintype.card W *
                    (Fintype.card W - 1).choose (2 * a)) := by
              simp only [B]
              ac_rfl
            _ = 2 ^ (2 * a) *
                  ((Fintype.card W - 2 * a) *
                    (Fintype.card W).choose (2 * a)) := by
              rw [hchoose]
            _ = (2 ^ (2 * a) *
                    (Fintype.card W).choose (2 * a)) *
                  (Fintype.card W - 2 * a) := by
              ac_rfl
        exact Nat.le_of_mul_le_mul_right htargetMul (by omega)

/-- Elementary factorial estimate used to simplify the exact binomial
contraction bound. -/
theorem two_pow_le_two_mul_factorial {d : ℕ} (hd : 0 < d) :
    2 ^ d ≤ 2 * d.factorial := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd0 : d = 0
      · subst d
        simp
      · have ih' := ih (Nat.pos_of_ne_zero hd0)
        calc
          2 ^ (d + 1) = 2 ^ d * 2 := by rw [pow_succ]
          _ ≤ (2 * d.factorial) * 2 :=
            Nat.mul_le_mul_right 2 ih'
          _ ≤ 2 * ((d + 1) * d.factorial) := by
            have : 2 ≤ d + 1 := by omega
            nlinarith [Nat.factorial_pos d]
          _ = 2 * (d + 1).factorial := by
            rw [Nat.factorial_succ]

/-- Karger's cut-counting theorem in the integer form used by the
Chekuri--Chuzhoy sparsifier proof.  Cuts are oriented vertex subsets, hence
the harmless leading factor `2`. -/
theorem card_smallCuts_le_two_mul_vertexCard_pow
    (H : FiniteEdgeIndexedGraph W) {C a : ℕ}
    (hC : 0 < C) (ha : 0 < a)
    (hconn : H.IsEdgeConnected C)
    (hvertices : 2 * a ≤ Fintype.card W) :
    (smallCuts H C a).card ≤
      2 * Fintype.card W ^ (2 * a) := by
  let d := 2 * a
  have hd : 0 < d := by simp [d, ha]
  have hbinomial :=
    card_smallCuts_le_two_pow_mul_choose H hC ha hconn hvertices
  have hfactorial := two_pow_le_two_mul_factorial hd
  have hchoose :
      (Fintype.card W).choose d * d.factorial ≤
        Fintype.card W ^ d := by
    rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  calc
    (smallCuts H C a).card ≤
        2 ^ d * (Fintype.card W).choose d := by
      simpa only [d] using hbinomial
    _ = (Fintype.card W).choose d * 2 ^ d := by
      rw [Nat.mul_comm]
    _ ≤ (Fintype.card W).choose d * (2 * d.factorial) :=
      Nat.mul_le_mul_left _ hfactorial
    _ = 2 * ((Fintype.card W).choose d * d.factorial) := by
      ac_rfl
    _ ≤ 2 * Fintype.card W ^ d :=
      Nat.mul_le_mul_left 2 hchoose
    _ = 2 * Fintype.card W ^ (2 * a) := by rfl

/-- The customary all-scales form of Karger's cut-counting estimate.  Above
half the vertex count the same bound follows from the trivial count of all
oriented vertex subsets. -/
theorem card_smallCuts_le_two_mul_vertexCard_pow_all
    (H : FiniteEdgeIndexedGraph W) {C a : ℕ}
    (hC : 0 < C) (ha : 0 < a)
    (hconn : H.IsEdgeConnected C)
    (hvertices : 2 ≤ Fintype.card W) :
    (smallCuts H C a).card ≤
      2 * Fintype.card W ^ (2 * a) := by
  by_cases hscale : 2 * a ≤ Fintype.card W
  · exact card_smallCuts_le_two_mul_vertexCard_pow
      H hC ha hconn hscale
  · have hall :=
      card_smallCuts_le_two_pow_vertexCard H C a
    have hbase : 2 ≤ Fintype.card W := hvertices
    have hpowBase :
        2 ^ Fintype.card W ≤
          Fintype.card W ^ Fintype.card W :=
      Nat.pow_le_pow_left hbase _
    have hexp :
        Fintype.card W ≤ 2 * a := by omega
    have hpowExp :
        Fintype.card W ^ Fintype.card W ≤
          Fintype.card W ^ (2 * a) :=
      Nat.pow_le_pow_right (by omega) hexp
    calc
      (smallCuts H C a).card ≤ 2 ^ Fintype.card W := hall
      _ ≤ Fintype.card W ^ (2 * a) :=
        hpowBase.trans hpowExp
      _ ≤ 2 * Fintype.card W ^ (2 * a) := by omega

end Karger
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
