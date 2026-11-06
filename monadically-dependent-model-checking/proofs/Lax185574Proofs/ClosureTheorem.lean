import Lax185574.ClosureTheorem
import Lax185574.BallTypes
import Lax185574.BallFlip
import Lax185574.DpMinimalFlips
import Lax185574.DpMinimalVC
import Lax185574.DefinableFlipTransitivity
import Lax185574.NeighborhoodComplexityBound
import Lax185574Proofs.BallTypes
import Lax185574Proofs.ClosureHelpers
import Lax185574Proofs.AtomicTypeBridge
import Lax185574Proofs.Interface.Shim.BallTypes

namespace Lax185574Proofs.ClosureTheorem

open Lax199508.GraphClasses
open Lax185574.Flips Lax185574.GraphBalls Lax185574.Partitions Lax185574.GaifmanGraph
open Lax185574.DefinableFlips Lax185574.AtomicTypes Lax185574.VCDimension
open Lax185574Proofs.ClosureHelpers

/-- For every `s`, some `d` bounds the VC-dimension of every
`s`-definable flip of a graph of `C`. -/
def BoundedVCOfDefinableFlips (C : GraphClass) : Prop :=
  ∀ s : ℕ, ∃ d : ℕ, ∀ (n : ℕ) (G H : SimpleGraph (Fin n)), C n G →
    IsDefinableFlip G s H → vcDim H ≤ d

/-- The closure theorem at a fixed radius. -/
def ClosureAt (C : GraphClass) (r : ℕ) : Prop :=
  ∃ c s a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    ∀ A : Finset (Fin n), ∃ Astar : Finset (Fin n),
      Astar.card ≤ a * (A.card + 1) ^ c ∧
      ∀ v : Fin n, v ∉ A →
        ∃ S : Finset (Fin n), S ⊆ Astar ∧ S.card ≤ s ∧
          ∃ H : SimpleGraph (Fin n),
            IsFlip G (atomicTypes G (S : Set (Fin n))) H ∧
            Disjoint (graphBall H r {v}) (A : Set (Fin n))

theorem closureAt_zero (C : GraphClass) : ClosureAt C 0 := by
  refine ⟨1, 0, 1, fun n G _ A => ⟨A, by simp, fun v hv => ⟨∅, by simp, le_rfl, G,
    Lax185574Proofs.FlipBasics.isFlip_refl G _, ?_⟩⟩⟩
  rw [graphBall_zero_singleton, Set.disjoint_singleton_left]
  exact hv

section Classes

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The part of `w` in the partition into atomic types over `A` in `H`,
as a finite set. -/
noncomputable def classSet (H : SimpleGraph V) (A : Finset V) (w : V) : Finset V :=
  open Classical in Finset.univ.filter fun u => atomicTypes H (A : Set V) u w

omit [DecidableEq V] in
theorem classSet_eq_iff (H : SimpleGraph V) (A : Finset V) (x y : V) :
    classSet H A x = classSet H A y ↔ atomicTypes H (A : Set V) x y := by
  constructor
  · intro h
    have := congrArg (fun T => x ∈ T) h
    simp only [classSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.mp (Setoid.refl' _ x)
  · intro h
    ext u
    simp only [classSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hu => Setoid.trans' _ hu h, fun hu => Setoid.trans' _ hu (Setoid.symm' _ h)⟩

theorem atomicTypeCount_eq_card_image (H : SimpleGraph V) (X : Finset V) (A : Finset V) :
    atomicTypeCount H (X : Set V) (A : Set V) = (X.image (classSet H A)).card := by
  rw [Lax185574Proofs.AtomicTypeBridge.atomicTypeCount_eq_partCount, partCount,
    ← Set.ncard_coe_finset, Finset.coe_image]
  refine Lax185574Proofs.AtomicTypeBridge.ncard_image_congr _ _ fun x _ y _ => ?_
  rw [Quotient.eq, classSet_eq_iff]

theorem card_image_classSet_univ (H : SimpleGraph V) (A : Finset V) :
    (Finset.univ.image (classSet H A)).card = Nat.card (Quotient (atomicTypes H (A : Set V))) := by
  have h := atomicTypeCount_eq_card_image H Finset.univ A
  rw [Lax185574Proofs.AtomicTypeBridge.atomicTypeCount_eq_partCount, partCount,
    Finset.coe_univ, Set.image_univ_of_surjective Quotient.mk_surjective,
    Set.ncard_univ] at h
  exact h.symm

end Classes

theorem add_one_le_mul_pow {x a m e : ℕ} (hm : 1 ≤ m) (h : x ≤ a * m ^ e) :
    x + 1 ≤ (a + 1) * m ^ e := by
  have : 1 ≤ m ^ e := Nat.one_le_pow _ _ hm
  nlinarith

theorem closureAt_succ (C : GraphClass) (hBT : ∀ r s, BallTypes.BallTypesAt C r s)
    (hVC : BoundedVCOfDefinableFlips C) (r : ℕ)
    (hIH : ClosureAt C r) : ClosureAt C (r + 1) := by
  classical
  obtain ⟨c, s, a, hIH⟩ := hIH
  obtain ⟨d, hd⟩ := hVC s
  obtain ⟨k, t, a₁, hBT⟩ := hBT r s
  obtain ⟨z, hz⟩ := Lax185574.BallFlip.exists_ball_flip d t
  let K := 2 ^ (3 ^ s * 3 ^ s)
  let b₀ := a * (a₁ + 1) ^ c + 1
  refine ⟨k + k * c * s + (d + 1) * t, s + z + 1, a₁ + b₀ ^ s * K * 2 ^ t * (s + z),
    fun n G hG A => ?_⟩
  have : Fintype (SimpleGraph (Fin n)) := Fintype.ofFinite _
  obtain ⟨A₁, hAA₁, hA₁card, hA₁types⟩ := hBT n G hG A
  obtain ⟨B, hBcard, hBsep⟩ := hIH n G hG A₁
  -- the flips from the induction hypothesis
  let Ss := B.powerset.filter fun S => S.card ≤ s
  let Hs := Ss.biUnion fun S =>
    Finset.univ.filter fun H => IsFlip G (atomicTypes G (S : Set (Fin n))) H
  have hHs : ∀ H ∈ Hs, IsDefinableFlip G s H := by
    intro H hH
    obtain ⟨S, hS, hH⟩ := Finset.mem_biUnion.mp hH
    exact ⟨S, (Finset.mem_filter.mp hS).2, (Finset.mem_filter.mp hH).2⟩
  -- profiles and groups
  let sep : SimpleGraph (Fin n) → Fin n → Prop := fun H v =>
    Disjoint (graphBall H r {v}) (A₁ : Set (Fin n))
  let prof : SimpleGraph (Fin n) → Fin n → Finset (Finset (Fin n)) := fun H v =>
    (graphBall H r {v}).toFinset.image (classSet H A)
  let Pi : SimpleGraph (Fin n) → Finset (Finset (Finset (Fin n))) := fun H =>
    (Finset.univ.filter (sep H)).image (prof H)
  let grp : SimpleGraph (Fin n) → Finset (Finset (Fin n)) → Set (Fin n) := fun H π =>
    {v | sep H v ∧ prof H v = π}
  let E : SimpleGraph (Fin n) → Finset (Finset (Fin n)) → Prop := fun H π =>
    ∃ U : Finset (Fin n), U.card ≤ s + z ∧ ∃ H' : SimpleGraph (Fin n),
      IsFlip G (atomicTypes G (U : Set (Fin n))) H' ∧
      Disjoint (graphBall H' (r + 1) (grp H π)) (A : Set (Fin n))
  let U : SimpleGraph (Fin n) → Finset (Finset (Fin n)) → Finset (Fin n) := fun H π =>
    if h : E H π then Classical.choose h else ∅
  have hUcard : ∀ H π, (U H π).card ≤ s + z := by
    intro H π
    by_cases h : E H π
    · simp only [U, h, dite_true]; exact (Classical.choose_spec h).1
    · simp only [U, h, dite_false, Finset.card_empty]; omega
  -- profiles of balls avoiding `A₁` are small
  have hprof : ∀ H ∈ Hs, ∀ v, sep H v → (prof H v).card ≤ t := by
    intro H hH v hv
    have := hA₁types H (hHs H hH) v hv
    rw [← Set.coe_toFinset (graphBall H r {v}), atomicTypeCount_eq_card_image] at this
    exact this
  -- the key step: every group can be separated by a definable flip
  have hE : ∀ H ∈ Hs, ∀ π ∈ Pi H, E H π := by
    intro H hH π hπ
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp hπ
    have hv₀ : sep H v₀ := (Finset.mem_filter.mp hv₀).2
    have hv₀grp : v₀ ∈ grp H (prof H v₀) := ⟨hv₀, rfl⟩
    have hdisj : Disjoint (graphBall H r (grp H (prof H v₀))) (A : Set (Fin n)) := by
      rw [Set.disjoint_left]
      rintro x ⟨w, hw, hwx⟩ hxA
      exact Set.disjoint_left.mp hw.1 ⟨w, rfl, hwx⟩ (hAA₁ hxA)
    have himage : (graphBall H r (grp H (prof H v₀))).toFinset.image (classSet H A) =
        prof H v₀ := by
      ext P
      simp only [Finset.mem_image, Set.mem_toFinset]
      constructor
      · rintro ⟨x, ⟨w, hw, hwx⟩, rfl⟩
        rw [← hw.2]
        exact Finset.mem_image.mpr ⟨x, Set.mem_toFinset.mpr ⟨w, rfl, hwx⟩, rfl⟩
      · intro hP
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
        obtain ⟨w, hw, hwx⟩ := Set.mem_toFinset.mp hx
        rw [Set.mem_singleton_iff.mp hw] at hwx
        exact ⟨x, ⟨v₀, hv₀grp, hwx⟩, rfl⟩
    have hcount : atomicTypeCount H (graphBall H r (grp H (prof H v₀))) (A : Set (Fin n)) ≤ t := by
      rw [← Set.coe_toFinset (graphBall H r (grp H (prof H v₀))),
        atomicTypeCount_eq_card_image, himage]
      exact hprof H hH v₀ hv₀
    have hvc : vcDim H ≤ d := by
      obtain ⟨S, hS, hflip⟩ := hHs H hH
      exact hd n G H hG ⟨S, hS, hflip⟩
    obtain ⟨H', hH', hH'disj⟩ := hz (Fin n) H hvc r A (grp H (prof H v₀)) hdisj hcount
    obtain ⟨W, hW, hWflip⟩ :=
      Lax185574.DefinableFlipTransitivity.isDefinableFlip_trans (hHs H hH) hH'
    exact ⟨W, hW, H', hWflip, hH'disj⟩
  -- the closure
  let A₂ := A₁ ∪ Hs.biUnion fun H => (Pi H).biUnion fun π => U H π
  refine ⟨A₂, ?_, ?_⟩
  · -- size
    have hm : 1 ≤ A.card + 1 := by omega
    set m := A.card + 1 with hm_def
    have hB1 : B.card + 1 ≤ b₀ * m ^ (k * c) := by
      have h1 : A₁.card + 1 ≤ (a₁ + 1) * m ^ k := add_one_le_mul_pow hm hA₁card
      have h2 : B.card ≤ a * (a₁ + 1) ^ c * m ^ (k * c) := by
        calc B.card ≤ a * (A₁.card + 1) ^ c := hBcard
          _ ≤ a * ((a₁ + 1) * m ^ k) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
          _ = a * (a₁ + 1) ^ c * m ^ (k * c) := by rw [mul_pow, ← pow_mul]; ring
      exact add_one_le_mul_pow hm h2
    have hSs : Ss.card ≤ b₀ ^ s * m ^ (k * c * s) := by
      calc Ss.card ≤ (B.card + 1) ^ s := card_small_subsets_le B s
        _ ≤ (b₀ * m ^ (k * c)) ^ s := Nat.pow_le_pow_left hB1 _
        _ = b₀ ^ s * m ^ (k * c * s) := by rw [mul_pow, ← pow_mul]
    have hHscard : Hs.card ≤ b₀ ^ s * m ^ (k * c * s) * K := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ S ∈ Ss, (Finset.univ.filter fun H => IsFlip G (atomicTypes G (S : Set (Fin n))) H).card
          ≤ ∑ _S ∈ Ss, K := Finset.sum_le_sum fun S hS => by
            refine (card_flips_le G _).trans (Nat.pow_le_pow_right (by omega) ?_)
            have h3 := (Lax185574Proofs.AtomicPartitionCount.card_quotient_atomicTypes_le G S).trans
              (Nat.pow_le_pow_right (by omega : 1 ≤ 3) (Finset.mem_filter.mp hS).2)
            exact Nat.mul_le_mul h3 h3
        _ = Ss.card * K := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ hSs
    have hPi : ∀ H ∈ Hs, (Pi H).card ≤ 2 ^ t * m ^ ((d + 1) * t) := by
      intro H hH
      let Q := Finset.univ.image (classSet H A)
      have hsub : Pi H ⊆ Q.powerset.filter fun P => P.card ≤ t := by
        intro P hP
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hP
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hprof H hH v
          (Finset.mem_filter.mp hv).2⟩
        intro x hx
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
      have hQ : Q.card + 1 ≤ 2 * m ^ (d + 1) := by
        have hvc : vcDim H ≤ d := by
          obtain ⟨S, hS, hflip⟩ := hHs H hH
          exact hd n G H hG ⟨S, hS, hflip⟩
        have h1 : Q.card ≤ A.card + m ^ d := by
          rw [card_image_classSet_univ]
          exact (card_quotient_atomicTypes_le_nc H A).trans (Nat.add_le_add_left
            (Lax185574.NeighborhoodComplexityBound.neighborhoodComplexity_le H d hvc _) _)
        have h2 : m ≤ m ^ (d + 1) := by
          calc m = m ^ 1 := (pow_one m).symm
            _ ≤ m ^ (d + 1) := Nat.pow_le_pow_right hm (by omega)
        have h3 : m ^ d ≤ m ^ (d + 1) := Nat.pow_le_pow_right hm (by omega)
        omega
      calc (Pi H).card ≤ (Q.card + 1) ^ t :=
            (Finset.card_le_card hsub).trans (card_small_subsets_le Q t)
        _ ≤ (2 * m ^ (d + 1)) ^ t := Nat.pow_le_pow_left hQ _
        _ = 2 ^ t * m ^ ((d + 1) * t) := by rw [mul_pow, ← pow_mul]
    have hunion : (Hs.biUnion fun H => (Pi H).biUnion fun π => U H π).card ≤
        (b₀ ^ s * m ^ (k * c * s) * K) * ((2 ^ t * m ^ ((d + 1) * t)) * (s + z)) := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_card_nsmul _ _ ((2 ^ t * m ^ ((d + 1) * t)) * (s + z)) ?_).trans ?_
      · intro H hH
        refine Finset.card_biUnion_le.trans ?_
        refine (Finset.sum_le_card_nsmul _ _ (s + z) fun π _ => hUcard H π).trans ?_
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ (hPi H hH)
      · rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ hHscard
    calc A₂.card ≤ A₁.card + (Hs.biUnion fun H => (Pi H).biUnion fun π => U H π).card :=
          Finset.card_union_le _ _
      _ ≤ a₁ * m ^ k + (b₀ ^ s * m ^ (k * c * s) * K) *
            ((2 ^ t * m ^ ((d + 1) * t)) * (s + z)) := Nat.add_le_add hA₁card hunion
      _ = a₁ * m ^ k + b₀ ^ s * K * 2 ^ t * (s + z) * m ^ (k * c * s + (d + 1) * t) := by
          rw [pow_add]; ring
      _ ≤ a₁ * m ^ (k + k * c * s + (d + 1) * t) +
            b₀ ^ s * K * 2 ^ t * (s + z) * m ^ (k + k * c * s + (d + 1) * t) := by
          gcongr <;> first | exact hm | omega
      _ = (a₁ + b₀ ^ s * K * 2 ^ t * (s + z)) * m ^ (k + k * c * s + (d + 1) * t) := by ring
  · -- separation
    intro v hv
    by_cases hv₁ : v ∈ A₁
    · refine ⟨{v}, by simp [A₂, hv₁], by simp, isolate G v, ?_, ?_⟩
      · simpa using isFlip_isolate G v
      · refine Set.disjoint_left.mpr fun x hx hxA => ?_
        rw [Set.mem_singleton_iff.mp (graphBall_isolate G v (r + 1) hx)] at hxA
        exact hv hxA
    · obtain ⟨S, hSB, hSs, H, hH, hHdisj⟩ := hBsep v hv₁
      have hHmem : H ∈ Hs := Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hSB, hSs⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH⟩⟩
      have hπ : prof H v ∈ Pi H := Finset.mem_image.mpr
        ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHdisj⟩, rfl⟩
      have hEv := hE H hHmem (prof H v) hπ
      have hUeq : U H (prof H v) = Classical.choose hEv := by simp only [U, hEv, dite_true]
      obtain ⟨hcard, H', hH'flip, hH'disj⟩ := Classical.choose_spec hEv
      refine ⟨U H (prof H v), ?_, by rw [hUeq]; omega, H', ?_, ?_⟩
      · intro x hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨H, hHmem,
          Finset.mem_biUnion.mpr ⟨prof H v, hπ, hx⟩⟩)
      · rw [hUeq]; exact hH'flip
      · exact Set.disjoint_of_subset_left
          (graphBall_mono_center H' (r + 1) (Set.singleton_subset_iff.mpr (show v ∈ grp H (prof H v) from ⟨hHdisj, rfl⟩)))
          hH'disj

/-- The statement for the graph classes of the archive. -/
theorem closure_theorem_old (C : GraphClass)
    (hC : Lax185574.DpMinimality.DpMinimal (Lax185574Proofs.Interface.ofOld C)) (r : ℕ) :
    ClosureAt C r := by
  have hBT : ∀ r s, BallTypes.BallTypesAt C r s :=
    fun r s => Lax185574Proofs.Shim.BallTypes.ball_types C hC r s
  have hVC : BoundedVCOfDefinableFlips C := fun s => by
    obtain ⟨d, hd⟩ := Lax185574.DpMinimalVC.exists_vcDim_le _
      (Lax185574.DpMinimalFlips.dpMinimal_definableFlipClass _ hC s)
    exact ⟨d, fun n G H hG hH => hd (Lax185574.Graphs.Graph.ofSimpleGraph H)
      ⟨Lax185574.Graphs.Graph.ofSimpleGraph G, hG, H, hH, rfl⟩⟩
  induction r with
  | zero => exact closureAt_zero C
  | succ r ih => exact closureAt_succ C hBT hVC r ih

end Lax185574Proofs.ClosureTheorem

namespace Lax185574Proofs.ClosureTheorem

open Lax185574.Graphs Lax185574.DpMinimality
open Lax185574.Flips Lax185574.GraphBalls Lax185574.Partitions
open Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.ClosureTheorem.closure_theorem
---
Induction on `r`, as in the paper. At radius 0 take `A* = A` and no
flip. For the step, enlarge `A` to `A₁` by the ball-types lemma for the
current parameter bound `s`, and apply the induction hypothesis to `A₁`,
giving `B`. The `s`-definable flips of graphs of the class form a
dp-minimal class, so they have VC-dimension at most some `d`.
For every set `S ⊆ B` of at most `s` vertices and every `S`-flip `H` (at
most `2^{9^s}` of them), group the vertices whose radius-`r` ball in `H`
avoids `A₁` by the set of atomic types over `A` that the ball meets. By
the ball-types lemma these profiles have at most `t` members, and by the
Sauer–Shelah lemma there are at most `|A| + (|A| + 1)^d` atomic types
over `A`, so there are polynomially many groups. The ball flip lemma
gives a `z`-definable flip of `H` that `(r + 1)`-separates each group
from `A`, which is an `(s + z)`-definable flip of `G` by transitivity.
The new closure is `A₁` together with the parameters of all these flips.
Vertices of `A₁ ∖ A` are isolated by the flip over themselves.

The argument is carried out for the graph classes of the archive, and
transferred to the graph classes used here.
-/
theorem closure_theorem (C : GraphClass) (hC : DpMinimal C) (r : ℕ) :
    ∃ c s a : ℕ, ∀ G ∈ C, ∀ A : Finset (Fin G.n), ∃ Astar : Finset (Fin G.n),
      Astar.card ≤ a * (A.card + 1) ^ c ∧
      ∀ v ∉ A, ∃ S ⊆ Astar, S.card ≤ s ∧ ∃ H : SimpleGraph (Fin G.n),
        IsFlip G.toSimpleGraph (atomicTypes G.toSimpleGraph (S : Set (Fin G.n))) H ∧
        Disjoint (graphBall H r {v}) (A : Set (Fin G.n)) := by
  obtain ⟨c, s, a, h⟩ := closure_theorem_old (toOld C) hC r
  exact ⟨c, s, a, fun G hG => h G.n G.toSimpleGraph hG⟩

end Lax185574Proofs.ClosureTheorem
