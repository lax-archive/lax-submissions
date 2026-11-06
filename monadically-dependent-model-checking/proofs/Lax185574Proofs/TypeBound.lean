import Lax185574.TypeBound
import Lax185574.ClosureTheoremTuples
import Lax185574.SeparatingTypesTuples
import Lax185574Proofs.ClosureTheoremTuples
import Lax185574Proofs.TypeTransport
import Lax185574Proofs.FlipBridge
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lax185574Proofs.Interface.Shim.ClosureTheoremTuples

namespace Lax185574Proofs.TypeBound

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.MonadicDependence Lax710763.Transductions
open Lax185574.FirstOrderTypes Lax185574.Colorings Lax185574.Flips Lax185574.GraphBalls
open Lax185574.GaifmanGraph
open Lax185574Proofs.FormulaRank Lax185574Proofs.TypeTransport

universe z

theorem withinDist_symm {V : Type z} {G : SimpleGraph V} {r : ℕ} {x y : V}
    (h : WithinDist G r x y) : WithinDist G r y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w.reverse, by rw [SimpleGraph.Walk.length_reverse]; exact hw⟩

/-- Unions over a finite index set have at most the summed size. -/
theorem ncard_biUnion_le {ι β : Type*} (I : Finset ι) (Y : ι → Set β) :
    (⋃ i ∈ I, Y i).ncard ≤ ∑ i ∈ I, (Y i).ncard := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- A flip for a partition into at most `s` parts can be undone by a
toggle on a labeling with `s` labels. -/
theorem exists_flip_back {V : Type z} [Finite V] (G H : SimpleGraph V) (P : Setoid V) (s : ℕ)
    (hP : Nat.card (Quotient P) ≤ s) (hH : IsFlip G P H) :
    ∃ (lab : V → Fin s) (tog : Fin s → Fin s → Bool),
      ∀ x y, G.Adj x y ↔ x ≠ y ∧ Xor (H.Adj x y) (tog (lab x) (lab y) = true) := by
  classical
  let part := Lax185574Proofs.FlipBridge.labeling P
  have hH' : IsFlip G (Setoid.ker part) H := by
    rw [Lax185574Proofs.FlipBridge.ker_labeling]; exact hH
  have heq := Lax185574Proofs.FlipBridge.eq_flip_toggleOf G part H hH'
  let t := Lax185574Proofs.FlipBridge.toggleOf G part H
  let p := Nat.card (Quotient P)
  refine ⟨fun x => Fin.castLE hP (part x), fun i j =>
    if h : (i : ℕ) < p ∧ (j : ℕ) < p then t ⟨i, h.1⟩ ⟨j, h.2⟩ else false, fun x y => ?_⟩
  have ht : ∀ i j : Fin p, (if h : ((Fin.castLE hP i : Fin s) : ℕ) < p ∧
      ((Fin.castLE hP j : Fin s) : ℕ) < p then t ⟨_, h.1⟩ ⟨_, h.2⟩ else false) = t i j := by
    intro i j
    rw [dif_pos ⟨i.2, j.2⟩]
    rfl
  show G.Adj x y ↔ x ≠ y ∧ Xor (H.Adj x y) ((if h : ((Fin.castLE hP (part x) : Fin s) : ℕ) < p ∧
      ((Fin.castLE hP (part y) : Fin s) : ℕ) < p then t ⟨_, h.1⟩ ⟨_, h.2⟩ else false) = true)
  rw [ht]
  have hHxy : H.Adj x y ↔ x ≠ y ∧ Xor (G.Adj x y) (t (part x) (part y) = true) := by
    rw [heq]; rfl
  rw [hHxy]
  by_cases hxy : x = y
  · subst hxy; simp
  simp only [Xor, ne_eq, hxy, not_false_eq_true, true_and]
  tauto

/-- The positions of a `k`-tuple outside a set, followed by those inside. -/
noncomputable def splitEquiv {k : ℕ} (P : Finset (Fin k)) : Fin k ≃ Fin (P.card + Pᶜ.card) :=
  (Equiv.sumCompl (· ∈ P)).symm.trans
    ((Equiv.sumCongr P.equivFin
      ((Equiv.subtypeEquivRight fun x => by simp).trans Pᶜ.equivFin)).trans finSumFinEquiv)

theorem splitEquiv_symm_castAdd {k : ℕ} (P : Finset (Fin k)) (j : Fin P.card) :
    (splitEquiv P).symm (Fin.castAdd _ j) ∈ P := by
  simp [splitEquiv]

theorem splitEquiv_symm_natAdd {k : ℕ} (P : Finset (Fin k)) (j : Fin Pᶜ.card) :
    (splitEquiv P).symm (Fin.natAdd _ j) ∉ P := by
  have := (Pᶜ.equivFin.symm j).2
  simpa [splitEquiv] using Finset.mem_compl.mp this

/-- Relabeling along a bijection of positions transports types. -/
theorem rankTypeOver_comp {L : Language} {V : Type z} [L.Structure V] (q : ℕ) (W : Set V)
    {K K' : ℕ} (e : Fin K → Fin K') (w : Fin K' → V) :
    rankTypeOver (L := L) q W (w ∘ e) =
      {φ | (φ.relabel (Sum.map e id) : L.Formula (Fin K' ⊕ W)) ∈ rankTypeOver q W w} := by
  ext φ
  simp only [rankTypeOver, Set.mem_ofPred_eq, quantifierRank_formula_relabel,
    Formula.realize_relabel]
  refine and_congr_right fun _ => ?_
  have : (Sum.elim w Subtype.val ∘ Sum.map e id : Fin K ⊕ W → V) = Sum.elim (w ∘ e) Subtype.val := by
    funext x; rcases x with x | x <;> rfl
  rw [this]

/-- The type bound for a class with the closure theorem for tuples. -/
theorem typeCountOver_le_of_closureTuples (C : GraphClass)
    (hC : ∀ r k, ClosureTheoremTuples.ClosureTuplesAt C r k) (k q : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (colors : Fin c → Set (Fin n)) (U : Finset (Fin n)),
          @typeCountOver (withColors Language.graph c) (Fin n)
              (expansion G colors) k q Set.univ (U : Set (Fin n)) ≤
            F * (U.card + 1) ^ a := by
  classical
  obtain ⟨r, hsep⟩ := Lax185574.SeparatingTypesTuples.ncard_rankTypeOver_append_le.{0} q
  choose cf sf af hf using hC r
  let A := k + ∑ k' ∈ Finset.range (k + 1), cf k'
  refine ⟨A, fun c => ?_⟩
  have hT := fun k' => hsep k' (c + sf k')
  choose Tf hTf using hT
  let F := 2 ^ k * ∑ k' ∈ Finset.range (k + 1), af k' * Tf k'
  refine ⟨F, fun n G hG colors U => ?_⟩
  choose fam hfamcard hfamflip hfamsep using fun k' => hf k' n G hG U
  let _ : (withColors Language.graph c).Structure (Fin n) := expansion G colors
  -- the pieces
  let Far : SimpleGraph (Fin n) → (k' : ℕ) → Set (Fin k' → Fin n) := fun H k' =>
    {a | ∀ i, a i ∉ graphBall H r (U : Set (Fin n))}
  let Y : (P : Finset (Fin k)) → (Fin Pᶜ.card → U) → SimpleGraph (Fin n) →
      Set (Set ((withColors Language.graph c).Formula (Fin k ⊕ (U : Set (Fin n))))) :=
    fun P u H => (fun a : Fin P.card → Fin n =>
      rankTypeOver q (U : Set (Fin n))
        ((Fin.append a fun j => (u j : Fin n)) ∘ splitEquiv P)) '' Far H P.card
  -- every type is in some piece
  have hcover : typesOver (L := withColors Language.graph c) k q Set.univ (U : Set (Fin n)) ⊆
      ⋃ P ∈ (Finset.univ : Finset (Finset (Fin k))),
        ⋃ u ∈ (Finset.univ : Finset (Fin Pᶜ.card → U)), ⋃ H ∈ fam P.card, Y P u H := by
    rintro _ ⟨v, -, rfl⟩
    let P : Finset (Fin k) := Finset.univ.filter fun i => v i ∉ U
    let w := v ∘ (splitEquiv P).symm
    let a : Fin P.card → Fin n := fun j => w (Fin.castAdd _ j)
    have hu : ∀ j : Fin Pᶜ.card, w (Fin.natAdd _ j) ∈ U := by
      intro j
      have := splitEquiv_symm_natAdd P j
      simpa [P, w] using this
    let u : Fin Pᶜ.card → U := fun j => ⟨w (Fin.natAdd _ j), hu j⟩
    have ha : ∀ i, a i ∉ U := by
      intro i
      have := splitEquiv_symm_castAdd P i
      simpa [P, a, w] using this
    obtain ⟨H, hH, hdisj⟩ := hfamsep P.card a ha
    have hw : (Fin.append a fun j => (u j : Fin n)) = w := by
      funext x
      refine Fin.addCases (fun i => ?_) (fun j => ?_) x
      · simp [a]
      · simp [u]
    have hv : v = (Fin.append a fun j => (u j : Fin n)) ∘ splitEquiv P := by
      rw [hw]; funext x; simp [w]
    simp only [Set.mem_iUnion]
    refine ⟨P, Finset.mem_univ _, u, Finset.mem_univ _, H, hH, a, ?_, by rw [hv]⟩
    intro i ⟨c', hc', hw'⟩
    exact Set.disjoint_left.mp hdisj ⟨a i, ⟨i, rfl⟩, withinDist_symm hw'⟩ hc'
  -- each piece is small
  have hpiece : ∀ P u, ∀ H ∈ fam P.card, (Y P u H).ncard ≤ Tf P.card := by
    intro P u H hH
    obtain ⟨Pt, hPt, hflip⟩ := hfamflip P.card H hH
    obtain ⟨lab, tog, hGH⟩ := exists_flip_back G H Pt (sf P.card) hPt hflip
    let colors' : Fin (c + sf P.card) → Set (Fin n) := Fin.append colors fun i => {y | lab y = i}
    have h1 : (Y P u H).ncard ≤ ((fun a : Fin P.card → Fin n =>
        rankTypeOver (L := withColors Language.graph c) q (U : Set (Fin n))
          (Fin.append a fun j => (u j : Fin n))) ''
          Far H P.card).ncard := by
      have : Y P u H = (fun τ => {φ | (φ.relabel (Sum.map (splitEquiv P) id) :
          (withColors Language.graph c).Formula (Fin (P.card + Pᶜ.card) ⊕ (U : Set (Fin n)))) ∈ τ}) ''
          ((fun a : Fin P.card → Fin n =>
            rankTypeOver (L := withColors Language.graph c) q (U : Set (Fin n))
              (Fin.append a fun j => (u j : Fin n))) ''
              Far H P.card) := by
        simp only [Y, Set.image_image]
        congr 1
        funext a
        exact rankTypeOver_comp q _ _ _
      rw [this]
      exact Set.ncard_image_le (Set.toFinite _)
    refine h1.trans ((ncard_image_le_of_factor _
      (fun a : Fin P.card → Fin n => @rankTypeOver _ (Fin n) (expansion H colors') q
        (U : Set (Fin n)) _ (Fin.append a fun j => (u j : Fin n))) ?_ (Set.toFinite _)).trans ?_)
    · intro x _ y _ hxy
      exact rankTypeOver_eq_of_flip G H colors lab tog hGH q _ _ _ hxy
    · exact hTf P.card (Fin n) H colors' (U : Set (Fin n)) Pᶜ.card (fun j => (u j : Fin n))
        (fun j => (u j).2)
  -- counting
  unfold typeCountOver
  have hfin : (⋃ P ∈ (Finset.univ : Finset (Finset (Fin k))),
      ⋃ u ∈ (Finset.univ : Finset (Fin Pᶜ.card → U)), ⋃ H ∈ fam P.card, Y P u H).Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun P _ =>
      Set.Finite.biUnion (Finset.finite_toSet _) fun u _ =>
        Set.Finite.biUnion (Finset.finite_toSet _) fun H _ => (Set.toFinite _).image _
  refine (Set.ncard_le_ncard hcover hfin).trans ((ncard_biUnion_le _ _).trans ?_)
  have hm : 1 ≤ U.card + 1 := by omega
  have hP : ∀ P : Finset (Fin k),
      (⋃ u ∈ (Finset.univ : Finset (Fin Pᶜ.card → U)), ⋃ H ∈ fam P.card, Y P u H).ncard ≤
        (∑ k' ∈ Finset.range (k + 1), af k' * Tf k') * (U.card + 1) ^ A := by
    intro P
    have hPk : P.card ∈ Finset.range (k + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.card_le_univ P).trans (by simp)))
    refine (ncard_biUnion_le _ _).trans ?_
    calc ∑ u ∈ (Finset.univ : Finset (Fin Pᶜ.card → U)), (⋃ H ∈ fam P.card, Y P u H).ncard
        ≤ ∑ _u ∈ (Finset.univ : Finset (Fin Pᶜ.card → U)), (fam P.card).card * Tf P.card := by
          refine Finset.sum_le_sum fun u _ => (ncard_biUnion_le _ _).trans ?_
          rw [← smul_eq_mul]
          exact Finset.sum_le_card_nsmul _ _ _ fun H hH => hpiece P u H hH
      _ = (U.card ^ Pᶜ.card) * ((fam P.card).card * Tf P.card) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_coe, smul_eq_mul]
      _ ≤ (U.card + 1) ^ k * ((af P.card * (U.card + 1) ^ cf P.card) * Tf P.card) := by
          refine Nat.mul_le_mul ((Nat.pow_le_pow_left (by omega) _).trans
            (Nat.pow_le_pow_right hm ((Finset.card_le_univ _).trans (by simp))))
            (Nat.mul_le_mul_right _ (hfamcard P.card))
      _ = (af P.card * Tf P.card) * ((U.card + 1) ^ k * (U.card + 1) ^ cf P.card) := by ring
      _ ≤ (∑ k' ∈ Finset.range (k + 1), af k' * Tf k') * (U.card + 1) ^ A := by
          refine Nat.mul_le_mul (Finset.single_le_sum (f := fun k' => af k' * Tf k')
            (fun _ _ => Nat.zero_le _) hPk) ?_
          rw [← pow_add]
          exact Nat.pow_le_pow_right hm (Nat.add_le_add_left
            (Finset.single_le_sum (f := cf) (fun _ _ => Nat.zero_le _) hPk) _)
  calc ∑ P ∈ (Finset.univ : Finset (Finset (Fin k))),
        (⋃ u ∈ (Finset.univ : Finset (Fin Pᶜ.card → U)), ⋃ H ∈ fam P.card, Y P u H).ncard
      ≤ ∑ _P ∈ (Finset.univ : Finset (Finset (Fin k))),
          (∑ k' ∈ Finset.range (k + 1), af k' * Tf k') * (U.card + 1) ^ A :=
        Finset.sum_le_sum fun P _ => hP P
    _ = F * (U.card + 1) ^ A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          smul_eq_mul]
        ring

/-- The statement for the graph classes of the archive and their
monadic dependence. -/
theorem typeCountOver_le_old (C : GraphClass) (hC : MonadicallyDependent C) (k q : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        ∀ (colors : Fin c → Set (Fin n)) (U : Finset (Fin n)),
          @typeCountOver (withColors Language.graph c) (Fin n)
              (expansion G colors) k q Set.univ (U : Set (Fin n)) ≤
            F * (U.card + 1) ^ a :=
  typeCountOver_le_of_closureTuples C
    (fun r k => Lax185574Proofs.Shim.ClosureTheoremTuples.closure_theorem_tuples C hC r k) k q

end Lax185574Proofs.TypeBound

namespace Lax185574Proofs.TypeBound

open Lax185574.Graphs Lax185574.MonadicDependence
open Lax185574.FirstOrderTypes Lax185574.Colorings Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.TypeBound.typeCountOver_le
---
The proof in the paper, with the padding step replaced by a split of
each tuple into its entries outside `U` and its entries inside `U`. Let
`r = r(q)` be the separation radius. For each `k' ≤ k`, the closure
theorem for tuples gives polynomially many `s`-flips `H` of `G` such
that every `k'`-tuple outside `U` is at distance more than `r` from `U`
in one of them. A flip `H` is undone by a toggle on at most `s` parts,
so the edges of `G` are quantifier-free definable in `H` expanded by the
colors and by predicates for the parts, and the type of a tuple in this
expansion `H⁺` determines its type in `G⁺`. A `k`-tuple `v̄` is a
rearrangement of `ā ū` with `ā` outside `U` and `ū` inside `U`, and its
type is determined by the type of `ā ū` and the positions. For fixed
positions, `ū`, and `H`, the tuples `ā` far from `U` in `H` realize at
most `T(q, k', c + s)` types in `H⁺`. Summing over at most `2^k`
position sets, `(|U| + 1)^k` tuples `ū` and the flips gives the bound,
whose exponent does not depend on `c`.

The argument is carried out for any graph class of the archive with the
closure theorem for tuples, which holds for a monadically dependent
class, and transferred to the graph classes used here.
-/
theorem typeCountOver_le (C : GraphClass) (hC : MonadicallyDependent C)
    (k q : ℕ) :
    ∃ a : ℕ, ∀ c : ℕ, ∃ F : ℕ, ∀ G ∈ C,
      ∀ (colors : Fin c → Set (Fin G.n)) (U : Finset (Fin G.n)),
        typeCountOver (expansion G.toSimpleGraph colors) k q Set.univ (U : Set (Fin G.n)) ≤
          F * (U.card + 1) ^ a := by
  obtain ⟨a, h⟩ := typeCountOver_le_old (toOld C) (monadicallyDependent_toOld hC) k q
  refine ⟨a, fun c => ?_⟩
  obtain ⟨F, hF⟩ := h c
  exact ⟨F, fun G hG => hF G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.TypeBound
