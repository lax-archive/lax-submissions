import Lax485480.WelzlTrees
import Lax214022Proofs.ListCrossings
import Lax214022Proofs.CographWelzlUpperBound
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Tactic.FinCases

/-!
# From a Welzl tree to a Welzl order

Repeatedly remove a leaf.  After ordering the smaller tree, reinsert the
leaf immediately beside its unique neighbour.  For every set, this creates
at most two new changes precisely when the removed tree edge crosses the
set.
-/

namespace Lax485480Proofs.TreeOrder

open Lax195003.WelzlOrders
open Lax485480.WelzlTrees
open Lax214022Proofs.ListCrossings

noncomputable section

local instance classicalDecidablePred {V : Type} (p : V → Prop) :
    DecidablePred p := Classical.decPred p

local instance classicalDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem changes_insert_after_le (A B : List Bool) (a b : Bool) :
    changes (A ++ a :: b :: B) ≤
      changes (A ++ a :: B) + (if a = b then 0 else 2) := by
  cases B with
  | nil =>
      rw [changes_append_cons_cons]
      simp
      split <;> omega
  | cons c B =>
      rw [changes_append_cons_cons, changes_append_cons_cons]
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        simp [changes_cons_cons] <;> omega

theorem crossingCountInList_insert_after_le {V : Type}
    (X : Set V) [DecidablePred fun x => x ∈ X]
    (A B : List V) (u v : V) [Decidable (SeparatedBy X u v)] :
    crossingCountInList (fun x => x ∈ X) (A ++ u :: v :: B) ≤
      crossingCountInList (fun x => x ∈ X) (A ++ u :: B) +
        (if SeparatedBy X u v then 2 else 0) := by
  classical
  unfold crossingCountInList
  simp only [List.map_append, List.map_cons]
  have h := changes_insert_after_le
    (A.map fun x => decide (x ∈ X))
    (B.map fun x => decide (x ∈ X))
    (decide (u ∈ X)) (decide (v ∈ X))
  by_cases huv : SeparatedBy X u v
  · have huv' := huv
    simp only [SeparatedBy] at huv'
    have hne : decide (u ∈ X) ≠ decide (v ∈ X) := by
      by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> simp_all
    simpa [huv, hne] using h
  · have huv' := huv
    simp only [SeparatedBy] at huv'
    have heq : decide (u ∈ X) = decide (v ∈ X) := by
      by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> simp_all
    simpa [huv, heq] using h

@[simp] theorem mem_cutEdges_pair {V : Type*} (X : Set V) (u v : V) :
    s(u, v) ∈ cutEdges X ↔ SeparatedBy X u v := by
  exact Sym2.fromRel_prop

/-- Removing a leaf deletes exactly its incident edge from every cut. -/
theorem ncard_restricted_cut {V : Type} [Fintype V]
    (T : SimpleGraph V) (v u : V)
    (huniq : ∀ w, T.Adj v w → w = u) (X : Set V) :
    let W := {w : V // w ≠ v}
    let T' := T.induce ({v}ᶜ : Set V)
    let X' : Set W := {w | w.1 ∈ X}
    (T'.edgeSet ∩ cutEdges X').ncard =
      ((T.edgeSet ∩ cutEdges X) \ {s(v, u)}).ncard := by
  classical
  dsimp only
  apply Set.ncard_congr
      (fun e _ => Sym2.map (fun w : {w : V // w ≠ v} => w.1) e)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        rcases he with ⟨heT, heX⟩
        simp only [Set.mem_diff, Set.mem_inter_iff,
          Set.mem_singleton_iff]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simpa [SimpleGraph.mem_edgeSet] using heT
        · simpa using heX
        · intro hleaf
          simp only [Sym2.map_mk] at hleaf
          rw [Sym2.eq_iff] at hleaf
          rcases hleaf with hleaf | hleaf
          · exact a.2 hleaf.1
          · exact b.2 hleaf.2
  · intro a b ha hb hab
    exact Sym2.map.injective Subtype.val_injective hab
  · intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
        simp only [Set.mem_diff, Set.mem_inter_iff,
          Set.mem_singleton_iff] at he
        rcases he with ⟨⟨heT, heX⟩, hne⟩
        rw [SimpleGraph.mem_edgeSet] at heT
        have ha : a ≠ v := by
          intro hav
          subst a
          have hb : b = u := huniq b heT
          apply hne
          simp [hb]
        have hb : b ≠ v := by
          intro hbv
          subst b
          have ha' : a = u := huniq a heT.symm
          apply hne
          simp [ha']
        refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, rfl⟩
        constructor
        · simpa [SimpleGraph.mem_edgeSet] using heT
        · simpa using heX

/-- Every finite tree admits a vertex list in which every set changes at
most twice for each tree edge crossing the set. -/
theorem exists_tree_list {V : Type} [Fintype V] (T : SimpleGraph V)
    (hT : T.IsTree) :
    ∃ L : List V, L.Nodup ∧ (∀ x : V, x ∈ L) ∧
      ∀ X : Set V,
        crossingCountInList (fun x => x ∈ X) L ≤
          2 * (T.edgeSet ∩ cutEdges X).ncard := by
  classical
  letI : Nonempty V := hT.connected.nonempty
  by_cases hsub : Subsingleton V
  · let x : V := Classical.choice (inferInstance : Nonempty V)
    refine ⟨[x], by simp, ?_, ?_⟩
    · intro y
      simp [hsub.elim y x]
    · intro X
      simp [crossingCountInList]
  · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
    letI : DecidableRel T.Adj := Classical.decRel _
    obtain ⟨v, hvdeg⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, huv, huniq⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hvdeg
    let W := {w : V // w ≠ v}
    let T' : SimpleGraph W := T.induce ({v}ᶜ : Set V)
    have hT' : T'.IsTree := by
      refine ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hvdeg, ?_⟩
      exact hT.isAcyclic.induce ({v}ᶜ : Set V)
    obtain ⟨L, hLn, hall, hbound⟩ := exists_tree_list T' hT'
    let u' : W := ⟨u, huv.ne.symm⟩
    obtain ⟨A, B, hL⟩ := List.mem_iff_append.mp (hall u')
    let R : List V :=
      A.map Subtype.val ++ u :: v :: B.map Subtype.val
    have hmapN : (L.map Subtype.val).Nodup :=
      hLn.map Subtype.val_injective
    have hvnot : v ∉ L.map Subtype.val := by simp
    have hbaseN : (v :: L.map Subtype.val).Nodup :=
      List.nodup_cons.mpr ⟨hvnot, hmapN⟩
    have hperm : R.Perm (v :: L.map Subtype.val) := by
      have hswap :
          (A.map Subtype.val ++ u :: v :: B.map Subtype.val).Perm
            (A.map Subtype.val ++ v :: u :: B.map Subtype.val) := by
        exact (List.Perm.swap v u (B.map Subtype.val)).append_left
          (A.map Subtype.val)
      have hmiddle :
          (A.map Subtype.val ++ v :: u :: B.map Subtype.val).Perm
            (v :: (A.map Subtype.val ++ u :: B.map Subtype.val)) :=
        List.perm_middle
      simpa [R, hL] using hswap.trans hmiddle
    have hRN : R.Nodup := hperm.nodup_iff.mpr hbaseN
    have hRall : ∀ x : V, x ∈ R := by
      intro x
      apply hperm.mem_iff.mpr
      by_cases hx : x = v
      · simp [hx]
      · simp only [List.mem_cons]
        right
        simp only [List.mem_map]
        exact ⟨⟨x, hx⟩, hall ⟨x, hx⟩, rfl⟩
    refine ⟨R, hRN, hRall, ?_⟩
    intro X
    let X' : Set W := {w | w.1 ∈ X}
    have hrec := hbound X'
    have hcross :
        crossingCountInList (fun x => x ∈ X)
            (A.map Subtype.val ++ u :: B.map Subtype.val) =
          crossingCountInList (fun x => x ∈ X') L := by
      unfold crossingCountInList
      rw [hL]
      simp only [List.map_append, List.map_cons, List.map_map]
      rfl
    have hrec' :
        crossingCountInList (fun x => x ∈ X)
            (A.map Subtype.val ++ u :: B.map Subtype.val) ≤
          2 * (T'.edgeSet ∩ cutEdges X').ncard := by
      exact hcross.trans_le hrec
    have hins := crossingCountInList_insert_after_le X
      (A.map Subtype.val) (B.map Subtype.val) u v
    have hrest := ncard_restricted_cut T v u huniq X
    let C : Set (Sym2 V) := T.edgeSet ∩ cutEdges X
    let e : Sym2 V := s(v, u)
    by_cases hsep : SeparatedBy X v u
    · have hsep' : SeparatedBy X u v := by
        simp only [SeparatedBy] at hsep ⊢
        tauto
      have heC : e ∈ C := by
        exact ⟨huv, (mem_cutEdges_pair X v u).mpr hsep⟩
      have hcard := Set.ncard_diff_singleton_add_one heC
      dsimp [T', X'] at hrest hrec'
      have hcut :
          ((T.induce ({v}ᶜ : Set V)).edgeSet ∩
                cutEdges {w : W | w.1 ∈ X}).ncard + 1 = C.ncard := by
        calc
          _ = (C \ {e}).ncard + 1 := congrArg (fun z => z + 1) hrest
          _ = C.ncard := hcard
      calc
        crossingCountInList (fun x => x ∈ X) R ≤
            crossingCountInList (fun x => x ∈ X)
                (A.map Subtype.val ++ u :: B.map Subtype.val) + 2 := by
          simpa [R, hsep'] using hins
        _ ≤ 2 * ((T.induce ({v}ᶜ : Set V)).edgeSet ∩
                cutEdges {w : W | w.1 ∈ X}).ncard + 2 :=
          Nat.add_le_add_right hrec' 2
        _ = 2 * (T.edgeSet ∩ cutEdges X).ncard := by
          dsimp [C, e] at hcut
          omega
    · have hsep' : ¬ SeparatedBy X u v := by
        intro huv'
        apply hsep
        simp only [SeparatedBy] at huv' ⊢
        tauto
      have heC : e ∉ C := by
        intro he
        exact hsep ((mem_cutEdges_pair X v u).mp he.2)
      have hdiff : C \ {e} = C := Set.diff_singleton_eq_self heC
      dsimp [T', X'] at hrest hrec'
      have hcard :
          ((T.induce ({v}ᶜ : Set V)).edgeSet ∩
              cutEdges {w : W | w.1 ∈ X}).ncard = C.ncard := by
        calc
          _ = (C \ {e}).ncard := hrest
          _ = C.ncard := congrArg Set.ncard hdiff
      calc
        crossingCountInList (fun x => x ∈ X) R ≤
            crossingCountInList (fun x => x ∈ X)
                (A.map Subtype.val ++ u :: B.map Subtype.val) := by
          simpa [R, hsep'] using hins
        _ ≤ 2 * ((T.induce ({v}ᶜ : Set V)).edgeSet ∩
                cutEdges {w : W | w.1 ∈ X}).ncard := hrec'
        _ = 2 * (T.edgeSet ∩ cutEdges X).ncard := by
          dsimp [C, e] at hcard
          omega
termination_by Fintype.card V
decreasing_by
  letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
  simp [Fintype.card_subtype_compl]
  exact Fintype.card_pos

theorem crossingNumber_le_of_members {n K : ℕ}
    (𝓅 : SetSystem (Fin n)) (π : Equiv.Perm (Fin n))
    (h : ∀ X ∈ 𝓅, crossingCount π X ≤ K) :
    crossingNumber 𝓅 π ≤ K := by
  unfold crossingNumber
  let S : Set ℕ := {q | ∃ X ∈ 𝓅, q = crossingCount π X}
  have hbound : ∀ q ∈ S, q ≤ K := by
    rintro q ⟨X, hX, rfl⟩
    exact h X hX
  have hbdd : ∃ m, ∀ q ∈ S, q ≤ m := ⟨K, hbound⟩
  change sSup S ≤ K
  rw [Nat.sSup_def hbdd]
  exact Nat.find_min' hbdd hbound

theorem treeCrossingCount_le_treeCrossingNumber {n : ℕ}
    (𝓅 : SetSystem (Fin n)) (T : SimpleGraph (Fin n))
    (X : Set (Fin n)) (hX : X ∈ 𝓅) :
    treeCrossingCount T X ≤ treeCrossingNumber 𝓅 T := by
  unfold treeCrossingNumber
  let S : Set ℕ := {q | ∃ Y ∈ 𝓅, q = treeCrossingCount T Y}
  have hbdd : BddAbove S := by
    refine ⟨Nat.card (Sym2 (Fin n)), ?_⟩
    rintro q ⟨Y, -, rfl⟩
    exact Set.ncard_le_card _
  apply le_csSup hbdd
  exact ⟨X, hX, rfl⟩

/-- A tree layout can be linearized at a factor-two loss in crossing
number. -/
theorem exists_order_crossingNumber_le_two_mul {n : ℕ}
    (𝓅 : SetSystem (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) :
    ∃ π : Equiv.Perm (Fin n),
      crossingNumber 𝓅 π ≤ 2 * treeCrossingNumber 𝓅 T := by
  classical
  obtain ⟨L, hLn, hall, hbound⟩ := exists_tree_list T hT
  have hfinset : L.toFinset = Finset.univ := by
    ext x
    simp [hall]
  have hlen : L.length = n := by
    calc
      L.length = L.toFinset.card :=
        (List.toFinset_card_of_nodup hLn).symm
      _ = Finset.univ.card := congrArg Finset.card hfinset
      _ = n := by simp
  obtain ⟨π, hπ⟩ :=
    Lax214022Proofs.CographWelzlUpperBound.exists_perm_of_nodup_complete
      L hLn hall hlen
  refine ⟨π, crossingNumber_le_of_members 𝓅 π ?_⟩
  intro X hX
  rw [crossingCount_eq_crossingCountInList, hπ]
  exact (hbound X).trans <| Nat.mul_le_mul_left 2 <|
    treeCrossingCount_le_treeCrossingNumber 𝓅 T X hX

end

end Lax485480Proofs.TreeOrder
