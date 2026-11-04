import Lax185574.BallTypes
import Lax185574.DefinableFlipFormula
import Lax185574.ForbiddenPhiPatterns
import Lax185574.MatchedTuples
import Lax185574Proofs.BallTypesHelpers
import Lax185574Proofs.FlipDistanceFormula
import Lax185574Proofs.ForbiddenPhiPatterns
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lax185574Proofs.Interface.Shim.ForbiddenPhiPatterns

namespace Lax185574Proofs.BallTypes

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax185574.AtomicTypes Lax185574.DefinableFlips Lax185574.GraphBalls Lax185574.GaifmanGraph
open Lax185574.PhiPsiPatterns Lax185574.PhiPatterns Lax185574.AtomicMatching
open Lax185574.BipartiteGraphs
open Lax185574Proofs.BallTypesHelpers Lax185574Proofs.FlipDistanceFormula

/-- Relations on atomic types over `s`-tuples. -/
abbrev Rel (s : ℕ) : Type := (Fin s → PairType) → (Fin s → PairType) → Prop

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem ball_types_old (C : GraphClass) (hC : MonadicallyDependent C) (r s : ℕ) :
    ∃ k t a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ∀ A : Finset (Fin n), ∃ Astar : Finset (Fin n), A ⊆ Astar ∧
        Astar.card ≤ a * (A.card + 1) ^ k ∧
        ∀ H : SimpleGraph (Fin n), IsDefinableFlip G s H → ∀ v : Fin n,
          Disjoint (graphBall H r {v}) (Astar : Set (Fin n)) →
            atomicTypeCount H (graphBall H r {v}) (A : Set (Fin n)) ≤ t := by
  classical
  -- edge formulas of definable flips
  have hEex : ∀ R : Rel s, ∃ E : Language.graph.Formula (Fin 2 ⊕ Fin s),
      (∀ P Q, R P Q → R Q P) → ∀ (V : Type) (G : SimpleGraph V) (p : Fin s → V) (x y : V),
        (flipOver G p R).Adj x y ↔
          @Formula.Realize Language.graph V G.structure _ E (Sum.elim ![x, y] p) := by
    intro R
    by_cases hR : ∀ P Q, R P Q → R Q P
    · obtain ⟨E, -, hE⟩ :=
        Lax185574.DefinableFlipFormula.exists_isQF_flipOver_formula.{0} s R hR
      exact ⟨E, fun _ => hE⟩
    · exact ⟨⊥, fun h => absurd h hR⟩
  choose Ef hEf using hEex
  let φR : Rel s → Language.graph.Formula (Fin (s + 1) ⊕ Fin 1) := fun R => distFormula r (Ef R)
  have hforb := fun R => Lax185574Proofs.Shim.ForbiddenPhiPatterns.forbidden_phi_patterns C hC (φR R)
  choose tR htR using hforb
  have : Fintype (Rel s) := Fintype.ofFinite _
  let kk := Finset.univ.sup tR + 1
  have hkk : ∀ R, tR R ≤ kk := fun R =>
    (Finset.le_sup (f := tR) (Finset.mem_univ R)).trans (Nat.le_succ _)
  obtain ⟨Q, -, hQ⟩ := Lax185574.MatchedTuples.exists_atomicallyMatched.{0, 0}
  let ℓ₀ := kk * 9 ^ s
  refine ⟨kk, Q ℓ₀, 1 + Fintype.card (Rel s) * 2 * (kk * kk), fun n G hG A => ?_⟩
  -- patterns with a given base
  let P : Rel s → Bool → (Fin kk → Fin n) → ℕ → Prop := fun R N bb ℓ =>
    ∃ (a : Fin ℓ → Fin (s + 1) → Fin n) (c : Fin ℓ → Fin kk → Fin n),
      IsPattern G (φR R) (edgeOrNot N) a (fun j => ![bb j]) c
  have hP0 : ∀ R N bb, P R N bb 0 := fun R N bb =>
    ⟨Fin.elim0, Fin.elim0, fun i => i.elim0⟩
  have hPkk : ∀ R N bb, ¬ P R N bb kk := by
    rintro R N bb ⟨a, c, h⟩
    have hpat : HasPattern G (φR R) (edgeOrNot N) (tR R) (tR R) :=
      Lax185574Proofs.ForbiddenPhiPatterns.hasPattern_mono (hkk R) (hkk R) ⟨a, _, c, h⟩
    apply htR R n G hG
    cases N
    · exact Or.inr hpat
    · exact Or.inl hpat
  let ht : Rel s → Bool → (Fin kk → Fin n) → ℕ := fun R N bb => Nat.findGreatest (P R N bb) kk
  have hht : ∀ R N bb, P R N bb (ht R N bb) := fun R N bb =>
    Nat.findGreatest_spec (Nat.zero_le _) (hP0 R N bb)
  have hhtlt : ∀ R N bb, ht R N bb < kk := fun R N bb =>
    lt_of_le_of_ne (Nat.findGreatest_le _) fun e => hPkk R N bb (e ▸ hht R N bb)
  have hmax : ∀ R N bb, ¬ P R N bb (ht R N bb + 1) := fun R N bb =>
    Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hhtlt R N bb)
  choose pa pc hpat using hht
  let grid : Rel s → Bool → (Fin kk → Fin n) → Finset (Fin n) := fun R N bb =>
    Finset.univ.image fun ij : Fin (ht R N bb) × Fin kk => pc R N bb ij.1 ij.2
  let Astar := A ∪ (Finset.univ : Finset (Rel s × Bool × (Fin kk → A))).biUnion
    fun x => grid x.1 x.2.1 fun j => (x.2.2 j : Fin n)
  refine ⟨Astar, Finset.subset_union_left, ?_, ?_⟩
  · -- size
    have hgrid : ∀ x : Rel s × Bool × (Fin kk → A),
        (grid x.1 x.2.1 fun j => (x.2.2 j : Fin n)).card ≤ kk * kk := by
      intro x
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact Nat.mul_le_mul_right _ (hhtlt _ _ _).le
    have hu : (Finset.univ : Finset (Rel s × Bool × (Fin kk → A))).card ≤
        Fintype.card (Rel s) * 2 * (A.card + 1) ^ kk := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    have hA : A.card ≤ (A.card + 1) ^ kk :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
    calc Astar.card ≤ A.card + ((Finset.univ : Finset (Rel s × Bool × (Fin kk → A))).biUnion
          fun x => grid x.1 x.2.1 fun j => (x.2.2 j : Fin n)).card := Finset.card_union_le _ _
      _ ≤ A.card + (Finset.univ : Finset (Rel s × Bool × (Fin kk → A))).card * (kk * kk) := by
          refine Nat.add_le_add_left (Finset.card_biUnion_le.trans ?_) _
          rw [← smul_eq_mul]
          exact Finset.sum_le_card_nsmul _ _ _ fun x _ => hgrid x
      _ ≤ (A.card + 1) ^ kk + Fintype.card (Rel s) * 2 * (A.card + 1) ^ kk * (kk * kk) :=
          Nat.add_le_add hA (Nat.mul_le_mul_right _ hu)
      _ = (1 + Fintype.card (Rel s) * 2 * (kk * kk)) * (A.card + 1) ^ kk := by ring
  · -- few types
    intro H hH v hv
    by_contra hcount
    push Not at hcount
    have hvA : Disjoint (graphBall H r {v}) (A : Set (Fin n)) :=
      Set.disjoint_of_subset_right (by simp [Astar]) hv
    obtain ⟨p, R, hR, rfl⟩ := exists_eq_flipOver G H hH v
    rw [atomicTypeCount_eq_bipartite _ _ _ hvA] at hcount
    obtain ⟨a, b, hab⟩ := hQ ℓ₀ _ _ _ hcount
    -- pigeonhole on the pairs of atomic types over `p̄`
    let f : Fin ℓ₀ → (Fin s → PairType) × (Fin s → PairType) := fun i =>
      (atomicTypeOver G p (a i), atomicTypeOver G p (b i))
    have hcard : Fintype.card ((Fin s → PairType) × (Fin s → PairType)) * kk ≤
        Fintype.card (Fin ℓ₀) := by
      have h3 : Fintype.card PairType = 3 := rfl
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, h3, ← mul_pow]
      simp only [ℓ₀]; norm_num; ring_nf; exact le_rfl
    have : Nonempty PairType := ⟨.eq⟩
    obtain ⟨y, hy⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f hcard
    obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hy
    let σ := T.orderEmbOfFin hTcard
    have hσ : ∀ j, f (σ j) = y := fun j =>
      (Finset.mem_filter.mp (hT (T.orderEmbOfFin_mem hTcard j))).2
    let u : Fin kk → Fin n := fun j => a (σ j)
    let w : Fin kk → Fin n := fun j => b (σ j)
    have hu : ∀ j, atomicTypeOver G p (u j) = y.1 := fun j => congrArg Prod.fst (hσ j)
    have hw : ∀ j, atomicTypeOver G p (w j) = y.2 := fun j => congrArg Prod.snd (hσ j)
    have huB : ∀ j, u j ∈ graphBall (flipOver G p R) r {v} := fun j => (a (σ j)).2
    have hwA : ∀ j, w j ∈ A := fun j => (b (σ j)).2
    have huw : ∀ i j, u i ≠ w j := fun i j e =>
      Set.disjoint_left.mp hvA (huB i) (e ▸ hwA j)
    -- adjacency in `G` between the tuples
    have hG' : ∀ i j, G.Adj (u i) (w j) ↔
        Xor ((flipOver G p R).Adj (u i) (w j)) (R y.1 y.2) := by
      intro i j
      rw [flipOver_adj G p R hR, hu, hw]
      simp only [Xor, ne_eq, huw i j, not_false_eq_true, true_and]
      tauto
    have hmatch : ∃ c₀ : Prop, ∀ j j' : Fin kk,
        (j = j' → ((flipOver G p R).Adj (u j) (w j') ↔ c₀)) ∧
        (j < j' → ((flipOver G p R).Adj (u j) (w j') ↔ ¬ c₀)) := by
      rcases hab with h | h | h
      · have h' : ∀ i j, (flipOver G p R).Adj (u i) (w j) ↔ i = j := fun i j => by
          have := h (σ i) (σ j)
          simp only [Function.comp_apply, Lax185574Proofs.BipartiteBasics.adj_inl_inr] at this
          rw [this, σ.injective.eq_iff]
        exact ⟨True, fun j j' => ⟨fun e => by rw [h', e]; simp, fun hlt => by
          rw [h']; simp [hlt.ne]⟩⟩
      · have h' : ∀ i j, (flipOver G p R).Adj (u i) (w j) ↔ i ≠ j := fun i j => by
          have := h (σ i) (σ j)
          simp only [Function.comp_apply, Lax185574Proofs.BipartiteBasics.adj_inl_inr] at this
          rw [this, ne_eq, σ.injective.eq_iff]
        exact ⟨False, fun j j' => ⟨fun e => by rw [h', e]; simp, fun hlt => by
          rw [h']; simp [hlt.ne]⟩⟩
      · have h' : ∀ i j, (flipOver G p R).Adj (u i) (w j) ↔ j ≤ i := fun i j => by
          have := h (σ i) (σ j)
          simp only [Function.comp_apply, Lax185574Proofs.BipartiteBasics.adj_inl_inr] at this
          rw [this, σ.le_iff_le]
        exact ⟨True, fun j j' => ⟨fun e => by rw [h', e]; simp, fun hlt => by
          rw [h']; simp [hlt]⟩⟩
    obtain ⟨c₀, hc₀⟩ := hmatch
    obtain ⟨N, hN⟩ : ∃ N : Bool, (N = true ↔ Xor c₀ (R y.1 y.2)) :=
      ⟨decide (Xor c₀ (R y.1 y.2)), decide_eq_true_iff⟩
    have hN1 : ∀ j, G.Adj (w j) (u j) ↔ N = true := by
      intro j
      rw [hN, G.adj_comm, hG' j j, (hc₀ j j).1 rfl]
    have hN2 : ∀ j j', j < j' → ¬ (G.Adj (w j') (u j) ↔ N = true) := by
      intro j j' hlt
      rw [hN, G.adj_comm, hG' j j', (hc₀ j j').2 hlt]
      simp only [Xor]
      tauto
    -- extending the maximal pattern
    let bb : Fin kk → Fin n := w
    apply hmax R N bb
    refine ⟨Fin.snoc (pa R N bb) (Fin.snoc p v), Fin.snoc (pc R N bb) u,
      isPattern_snoc G (hpat R N bb) _ _ ?_ ?_ ?_ ?_⟩
    · intro j
      rw [holds_distFormula r R (Ef R) (hEf R hR (Fin n)) G]
      have e1 : (Fin.snoc p v : Fin (s + 1) → Fin n) ∘ Fin.castSucc = p := by
        funext i; simp
      rw [e1, Fin.snoc_last]
      obtain ⟨c, hc, hcu⟩ := huB j
      rwa [Set.mem_singleton_iff.mp hc] at hcu
    · intro i j hh
      rw [holds_distFormula r R (Ef R) (hEf R hR (Fin n)) G] at hh
      have e1 : (Fin.snoc p v : Fin (s + 1) → Fin n) ∘ Fin.castSucc = p := by
        funext i; simp
      rw [e1, Fin.snoc_last] at hh
      have hmem : pc R N bb i j ∈ Astar := by
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨(R, N, fun j => ⟨w j, hwA j⟩), Finset.mem_univ _, ?_⟩)
        exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
      exact Set.disjoint_left.mp hv ⟨v, rfl, hh⟩ hmem
    · intro j
      rw [holds_edgeOrNot]
      exact hN1 j
    · intro j j' hlt
      rw [holds_edgeOrNot]
      exact hN2 j j' hlt

end Lax185574Proofs.BallTypes

namespace Lax185574Proofs.BallTypes

open Lax185574.Graphs Lax185574.MonadicDependence
open Lax185574.AtomicTypes Lax185574.DefinableFlips Lax185574.GraphBalls
open Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.BallTypes.ball_types
---
The proof in the paper. For each symmetric `R ⊆ Π^s × Π^s` let `φ_R(z̄
x, y)` express distance at most `r` in `G ⊕ (z̄, R)`, using the
quantifier-free edge formula of the flip. Let `k` exceed all the bounds
on `φ_R`-patterns and put `t = Q(k · 9^s)`. For every `R`, every `N ∈
{E, ¬E}` and every base `b̄ ∈ A^k` fix a `(φ_R, N)`-pattern of maximum
height (less than `k`), and let `A*` consist of `A` and all their grid
points. If a ball `B = Ball^H_r[v]` in `H = G ⊕ (p̄, R)` avoids `A*` but
realizes more than `t` atomic types over `A`, the matching theorem gives
atomically matched tuples in `B` and `A` of length `k · 9^s`. By
pigeonhole `k` of the pairs have the same pair of atomic types over
`p̄`, so on them `H` agrees with `G` or with its complement, and this
yields `N` such that the tuple `w̄` from `A` and the tuple `ū` from `B`
satisfy `N(wⱼ, uⱼ)` and `¬N(wⱼ', uⱼ)` for `j < j'`. Then `p̄ v` and `ū`
extend the chosen pattern with base `w̄` by a row, as `ū` lies in `B`
and the old grid points do not, contradicting maximality.

The argument is carried out for the graph classes of the archive and
their monadic dependence, and transferred to the graph classes used
here.
-/
theorem ball_types (C : GraphClass) (hC : MonadicallyDependent C) (r s : ℕ) :
    ∃ k t a : ℕ, ∀ G ∈ C, ∀ A : Finset (Fin G.n), ∃ Astar ⊇ A,
      Astar.card ≤ a * (A.card + 1) ^ k ∧
      ∀ H : SimpleGraph (Fin G.n), IsDefinableFlip G.toSimpleGraph s H → ∀ v : Fin G.n,
        Disjoint (graphBall H r {v}) (Astar : Set (Fin G.n)) →
          atomicTypeCount H (graphBall H r {v}) (A : Set (Fin G.n)) ≤ t := by
  obtain ⟨k, t, a, h⟩ := ball_types_old (toOld C) (monadicallyDependent_toOld hC) r s
  exact ⟨k, t, a, fun G hG => h G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.BallTypes
