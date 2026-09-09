import Lax485480.WelzlTrees
import Lax214022Proofs.ListCrossings
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# From a Welzl order to a Welzl tree

Join consecutive vertices in an order.  This produces a spanning path, and
its crossed edges are exactly the consecutive pairs counted by the order.
-/

namespace Lax485480Proofs.OrderPath

open Lax195003.WelzlOrders
open Lax485480.WelzlTrees
open Lax214022Proofs.ListCrossings

noncomputable section

local instance pathGraphDecidableAdj (n : ℕ) :
    DecidableRel (SimpleGraph.pathGraph n).Adj := Classical.decRel _

/-- The path whose vertices occur in the order encoded by `π`. -/
def orderPath {n : ℕ} (π : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) :=
  (SimpleGraph.pathGraph n).comap π.toEmbedding

@[simp] theorem orderPath_adj {n : ℕ} (π : Equiv.Perm (Fin n))
    (u v : Fin n) :
    (orderPath π).Adj u v ↔
      (π u).val + 1 = (π v).val ∨ (π v).val + 1 = (π u).val := by
  simp [orderPath, SimpleGraph.pathGraph_adj]

/-- The edge between positions `i` and `i+1` in the standard path. -/
def pathEdge (n : ℕ) (i : Fin (n - 1)) : Sym2 (Fin n) :=
  s(⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩)

theorem pathEdge_injective (n : ℕ) : Function.Injective (pathEdge n) := by
  intro i j hij
  simp only [pathEdge, Sym2.eq_iff, Fin.mk.injEq] at hij
  rcases hij with h | h
  · exact Fin.ext h.1
  · omega

theorem pathGraph_edgeFinset (n : ℕ) :
    (SimpleGraph.pathGraph n).edgeFinset =
      Finset.univ.image (pathEdge n) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      rw [SimpleGraph.pathGraph_adj]
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro huv
        rcases huv with huv | hvu
        · have hi : u.val < n - 1 := by omega
          refine ⟨⟨u.val, hi⟩, ?_⟩
          rw [pathEdge, Sym2.eq_iff]
          left
          exact ⟨Fin.ext rfl, Fin.ext huv⟩
        · have hi : v.val < n - 1 := by omega
          refine ⟨⟨v.val, hi⟩, ?_⟩
          rw [pathEdge, Sym2.eq_iff]
          right
          exact ⟨Fin.ext rfl, Fin.ext hvu⟩
      · rintro ⟨i, hi⟩
        simp only [pathEdge, Sym2.eq_iff] at hi
        rcases hi with hi | hi
        · left
          have hu : i.val = u.val := by
            simpa using congrArg Fin.val hi.1
          have hv : i.val + 1 = v.val := by
            simpa using congrArg Fin.val hi.2
          omega
        · right
          have hv : i.val = v.val := by
            simpa using congrArg Fin.val hi.1
          have hu : i.val + 1 = u.val := by
            simpa using congrArg Fin.val hi.2
          omega

theorem card_pathGraph_edgeFinset (n : ℕ) :
    (SimpleGraph.pathGraph n).edgeFinset.card = n - 1 := by
  classical
  rw [pathGraph_edgeFinset, Finset.card_image_of_injective _
    (pathEdge_injective n), Finset.card_univ, Fintype.card_fin]

theorem pathGraph_isTree (n : ℕ) (hn : 0 < n) :
    (SimpleGraph.pathGraph n).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact SimpleGraph.pathGraph_connected m
  · rw [Nat.card_eq_fintype_card
          (α := (SimpleGraph.pathGraph n).edgeSet),
      Nat.card_eq_fintype_card (α := Fin n),
      SimpleGraph.card_edgeSet, card_pathGraph_edgeFinset,
      Fintype.card_fin]
    omega

theorem orderPath_isTree {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) : (orderPath π).IsTree := by
  exact (SimpleGraph.Iso.comap π (SimpleGraph.pathGraph n)).isTree_iff.mpr
    (pathGraph_isTree n hn)

@[simp] theorem mem_cutEdges_pair {V : Type*} (X : Set V) (u v : V) :
    s(u, v) ∈ cutEdges X ↔ (u ∈ X ↔ v ∉ X) := by
  exact Sym2.fromRel_prop

/-- A set crosses the path of an order exactly as often as it crosses the
consecutive pairs of the order. -/
theorem treeCrossingCount_orderPath {n : ℕ} (π : Equiv.Perm (Fin n))
    (X : Set (Fin n)) :
    treeCrossingCount (orderPath π) X = crossingCount π X := by
  classical
  let A : Set (Fin n) :=
    {u | ∃ v : Fin n,
      (π v).val = (π u).val + 1 ∧ (u ∈ X ↔ v ∉ X)}
  let B : Set (Sym2 (Fin n)) := (orderPath π).edgeSet ∩ cutEdges X
  have next_lt {u : Fin n} (hu : u ∈ A) : (π u).val + 1 < n := by
    rcases hu with ⟨v, hv, -⟩
    omega
  let next (u : Fin n) (hu : u ∈ A) : Fin n :=
    π.symm ⟨(π u).val + 1, next_lt hu⟩
  have next_pos (u : Fin n) (hu : u ∈ A) :
      (π (next u hu)).val = (π u).val + 1 := by
    simp [next]
  have next_sep (u : Fin n) (hu : u ∈ A) :
      u ∈ X ↔ next u hu ∉ X := by
    have hu' := hu
    rcases hu' with ⟨v, hvpos, hvsep⟩
    have hv : v = next u hu := by
      apply π.injective
      apply Fin.ext
      simpa [next] using hvpos
    simpa [hv] using hvsep
  change B.ncard = A.ncard
  symm
  apply Set.ncard_congr (s := A) (t := B)
      (fun u hu => s(u, next u hu))
  · intro u hu
    constructor
    · rw [SimpleGraph.mem_edgeSet, orderPath_adj]
      exact Or.inl (next_pos u hu).symm
    · exact (mem_cutEdges_pair X u (next u hu)).mpr (next_sep u hu)
  · intro u w hu hw heq
    rw [Sym2.eq_iff] at heq
    rcases heq with heq | heq
    · exact heq.1
    · have huw := next_pos u hu
      have hwu := next_pos w hw
      have h₁ : (π u).val = (π (next w hw)).val :=
        congrArg (fun z : Fin n => (π z).val) heq.1
      have h₂ : (π (next u hu)).val = (π w).val :=
        congrArg (fun z : Fin n => (π z).val) heq.2
      omega
  · intro e he
    rcases he with ⟨heT, heX⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
        rw [SimpleGraph.mem_edgeSet, orderPath_adj] at heT
        rw [mem_cutEdges_pair] at heX
        rcases heT with huv | hvu
        · have huA : u ∈ A := ⟨v, huv.symm, heX⟩
          refine ⟨u, huA, ?_⟩
          rw [Sym2.eq_iff]
          left
          refine ⟨rfl, ?_⟩
          apply π.injective
          apply Fin.ext
          simpa using (next_pos u huA).trans huv
        · have hvsep : v ∈ X ↔ u ∉ X := by tauto
          have hvA : v ∈ A := ⟨u, hvu.symm, hvsep⟩
          refine ⟨v, hvA, ?_⟩
          rw [Sym2.eq_iff]
          right
          refine ⟨rfl, ?_⟩
          apply π.injective
          apply Fin.ext
          simpa using (next_pos v hvA).trans hvu

/-- Passing from an order to its path preserves the crossing number of the
entire set system. -/
theorem treeCrossingNumber_orderPath {n : ℕ} (𝓕 : SetSystem (Fin n))
    (π : Equiv.Perm (Fin n)) :
    treeCrossingNumber 𝓕 (orderPath π) = crossingNumber 𝓕 π := by
  unfold treeCrossingNumber crossingNumber
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨X, hX, rfl⟩
  · exact ⟨X, hX, treeCrossingCount_orderPath π X⟩
  · exact ⟨X, hX, (treeCrossingCount_orderPath π X).symm⟩

end

end Lax485480Proofs.OrderPath
