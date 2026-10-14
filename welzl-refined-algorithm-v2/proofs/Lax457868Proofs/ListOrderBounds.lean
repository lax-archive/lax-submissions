import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Lax195003.WelzlOrdersInGraphs
import Lax195003.WelzlOrdersNeighborhoodSetSystem
import Lax457868Proofs.CrossingStability
import Lax457868Proofs.TwinExpansion

/-!
Bridges between the recursive list crossing count, the registered
permutation crossing count, and radius-one graph Welzl orders.
-/

namespace Lax457868Proofs.ListOrderBounds

noncomputable section

open Lax195003.WelzlOrders
open Lax195003.WelzlOrdersInGraphs
open Lax195003.WelzlOrdersNeighborhoodSetSystem
open Lax457868Proofs.TwinExpansion

variable {α : Type*}

/-- Classical membership as a proof-side Boolean predicate. -/
noncomputable def contains (D : Set α) (a : α) : Bool := by
  classical
  exact decide (a ∈ D)

/-- Whether one pair crosses a set in the usual set-based presentation. -/
noncomputable def crosses (X : Set α) (a b : α) : Bool :=
  by
    classical
    exact decide (a ∈ X ↔ b ∉ X)

/-- The set-based crossing count over consecutive pairs in a list. -/
noncomputable def zipCrossingCount (X : Set α) (l : List α) : ℕ :=
  (l.zip l.tail).countP fun pair => crosses X pair.1 pair.2

/-- The first endpoints of the crossing consecutive pairs in `l`. -/
noncomputable def crossingEndpoints (X : Set α) (l : List α) : Set α :=
  {a | a ∈ ((l.zip l.tail).filter
    (fun pair => crosses X pair.1 pair.2)).map Prod.fst}

/-- Count the entries of a list that belong to a fixed set. -/
noncomputable def memberCount (D : Set α) (l : List α) : ℕ := by
  exact l.countP (contains D)

/-- The recursive count from `TwinExpansion` is the standard zipped
consecutive-pair count. -/
lemma crossingCount_eq_zip (X : Set α) (l : List α) :
    TwinExpansion.crossingCount (contains X) l =
      zipCrossingCount X l := by
  classical
  induction l with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b tail =>
          have hedge : pairCrossing (contains X) a b =
              if crosses X a b = true then 1 else 0 := by
            by_cases ha : a ∈ X <;> by_cases hb : b ∈ X <;>
              simp [pairCrossing, crosses, contains, ha, hb]
          rw [show TwinExpansion.crossingCount (contains X)
              (a :: b :: tail) =
                pairCrossing (contains X) a b +
                  TwinExpansion.crossingCount (contains X)
                    (b :: tail) by rfl]
          rw [show zipCrossingCount X (a :: b :: tail) =
              zipCrossingCount X (b :: tail) +
                (if crosses X a b = true then 1 else 0) by
                simp [zipCrossingCount, List.countP_cons]]
          rw [ih]
          rw [hedge, Nat.add_comm]

/-- The recursive count depends only on the predicate values at list entries. -/
lemma crossingCount_congr_on (p q : α → Bool) {l : List α}
    (h : ∀ a ∈ l, p a = q a) :
    TwinExpansion.crossingCount p l = TwinExpansion.crossingCount q l := by
  have hfrom : ∀ (prev : α) (tail : List α),
      p prev = q prev → (∀ a ∈ tail, p a = q a) →
      TwinExpansion.crossingCountFrom p prev tail =
        TwinExpansion.crossingCountFrom q prev tail := by
    intro prev tail
    induction tail generalizing prev with
    | nil => intro hp ht; rfl
    | cons a tail ih =>
        intro hp ht
        have ha := ht a (by simp)
        have htail : ∀ z ∈ tail, p z = q z := fun z hz => ht z (by simp [hz])
        simp [TwinExpansion.crossingCountFrom, TwinExpansion.pairCrossing, hp, ha,
          ih a ha htail]
  cases l with
  | nil => rfl
  | cons a tail =>
      have ha := h a (by simp)
      exact hfrom a tail ha (fun z hz => h z (by simp [hz]))

/-- A list's recursive crossing count is at most its length. -/
lemma crossingCount_le_length (p : α → Bool) (l : List α) :
    TwinExpansion.crossingCount p l ≤ l.length := by
  have hfrom : ∀ (prev : α) (tail : List α),
      TwinExpansion.crossingCountFrom p prev tail ≤ tail.length := by
    intro prev tail
    induction tail generalizing prev with
    | nil => simp [TwinExpansion.crossingCountFrom]
    | cons a tail ih =>
        simp only [TwinExpansion.crossingCountFrom, List.length_cons]
        have hp : TwinExpansion.pairCrossing p prev a ≤ 1 := by
          by_cases h : p prev = p a <;> simp [TwinExpansion.pairCrossing, h]
        have htail := ih a
        omega
  cases l with
  | nil => simp [TwinExpansion.crossingCount]
  | cons a tail =>
      simpa [TwinExpansion.crossingCount] using (hfrom a tail).trans (by simp)

/-- Changing a set at endpoints of an edge can only account for the original
crossing at that edge. -/
lemma edge_crossing_le (X Y : Set α) (a b : α) :
    (if crosses X a b = true then 1 else 0) ≤
      (if crosses Y a b = true then 1 else 0) +
        (if contains ((X \ Y) ∪ (Y \ X)) a then 1 else 0) +
        (if contains ((X \ Y) ∪ (Y \ X)) b then 1 else 0) := by
  classical
  by_cases hXa : a ∈ X <;> by_cases hXb : b ∈ X <;>
    by_cases hYa : a ∈ Y <;> by_cases hYb : b ∈ Y <;>
      simp_all [crosses, contains, Set.mem_union, Set.mem_sdiff]

/-- Sum the edge estimate over an arbitrary list of pairs. -/
lemma countPairCrossings_le (X Y : Set α) (pairs : List (α × α)) :
    pairs.countP (fun p => crosses X p.1 p.2) ≤
      pairs.countP (fun p => crosses Y p.1 p.2) +
        (pairs.map Prod.fst).countP (contains ((X \ Y) ∪ (Y \ X))) +
        (pairs.map Prod.snd).countP (contains ((X \ Y) ∪ (Y \ X))) := by
  classical
  induction pairs with
  | nil => simp
  | cons pair pairs ih =>
      simp only [List.countP_cons, List.map_cons]
      have hedge := edge_crossing_le X Y pair.1 pair.2
      omega

/-- The crossing-edge first endpoints form a sublist of the original list. -/
lemma map_fst_zip_tail_sublist (l : List α) :
    List.Sublist ((l.zip l.tail).map Prod.fst) l := by
  cases l with
  | nil => simp
  | cons a tail =>
      cases tail with
      | nil => simp
      | cons b tail =>
          simp only [List.tail_cons, List.zip_cons_cons, List.map_cons]
          exact List.Sublist.cons_cons a (map_fst_zip_tail_sublist (b :: tail))
termination_by l.length
decreasing_by simp_wf

/-- The second endpoints of adjacent pairs are exactly the tail of `l`. -/
lemma map_snd_zip_tail (l : List α) :
    (l.zip l.tail).map Prod.snd = l.tail := by
  apply List.map_snd_zip
  simp

/-- A pair is in `l.zip l.tail` exactly when its indices are consecutive. -/
lemma mem_zip_tail_iff_idxOf_succ [DecidableEq α] {l : List α}
    (hl : l.Nodup) (u v : α) :
    (u, v) ∈ l.zip l.tail ↔
      u ∈ l ∧ v ∈ l ∧ l.idxOf v = l.idxOf u + 1 := by
  constructor
  · intro huv
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp huv
    have hifst : i.val < l.length := by
      have hi' := i.isLt
      simp only [List.length_zip] at hi'
      omega
    have hisnd : i.val < l.tail.length := by
      have hi' := i.isLt
      simp only [List.length_zip] at hi'
      omega
    have hinext : i.val + 1 < l.length := by
      simp only [List.length_tail] at hisnd
      omega
    rw [List.get_eq_getElem, List.getElem_zip, List.getElem_tail] at hi
    have hpair :
        (l.get ⟨i.val, hifst⟩, l.get ⟨i.val + 1, hinext⟩) = (u, v) := hi
    have hu : l.get ⟨i.val, hifst⟩ = u := congrArg Prod.fst hpair
    have hv : l.get ⟨i.val + 1, hinext⟩ = v := congrArg Prod.snd hpair
    refine ⟨?_, ?_, ?_⟩
    · rw [← hu]
      exact List.get_mem l ⟨i.val, hifst⟩
    · rw [← hv]
      exact List.get_mem l ⟨i.val + 1, hinext⟩
    · rw [← hu, ← hv, List.get_idxOf hl, List.get_idxOf hl]
  · rintro ⟨hu_mem, hv_mem, hidx⟩
    have hu_bound : l.idxOf u < l.length := List.idxOf_lt_length_iff.mpr hu_mem
    have hv_bound : l.idxOf v < l.length := List.idxOf_lt_length_iff.mpr hv_mem
    have hu_get : l.get ⟨l.idxOf u, hu_bound⟩ = u := List.idxOf_get hu_bound
    have hv_get : l.get ⟨l.idxOf u + 1, by omega⟩ = v := by
      have := List.idxOf_get hv_bound
      simpa only [hidx] using this
    have htail : l.idxOf u < l.tail.length := by
      simp only [List.length_tail]
      omega
    have hzip : l.idxOf u < (l.zip l.tail).length := by
      simp only [List.length_zip]
      omega
    apply List.mem_iff_get.mpr
    refine ⟨⟨l.idxOf u, hzip⟩, ?_⟩
    rw [List.get_eq_getElem, List.getElem_zip, List.getElem_tail]
    exact Prod.ext hu_get hv_get

/-- The set of first crossing endpoints has the same cardinality as the
zipped crossing count on a duplicate-free list. -/
lemma ncard_crossingEndpoints [DecidableEq α] [Finite α]
    (X : Set α) {l : List α} (hl : l.Nodup) :
    (crossingEndpoints X l).ncard = zipCrossingCount X l := by
  classical
  let pairs := (l.zip l.tail).filter (fun pair => crosses X pair.1 pair.2)
  have hsub : List.Sublist (pairs.map Prod.fst) l :=
    ((List.filter_sublist.map Prod.fst).trans (map_fst_zip_tail_sublist l))
  have hnodup : (pairs.map Prod.fst).Nodup := hsub.nodup hl
  unfold crossingEndpoints zipCrossingCount
  rw [List.countP_eq_length_filter]
  change ({a | a ∈ pairs.map Prod.fst} : Set α).ncard = pairs.length
  calc
    ({a | a ∈ pairs.map Prod.fst} : Set α).ncard =
        (pairs.map Prod.fst).toFinset.card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext a
      simp
    _ = (pairs.map Prod.fst).length := List.toFinset_card_of_nodup hnodup
    _ = pairs.length := by simp

/-- Membership in the endpoint set exposes its crossing successor. -/
lemma mem_crossingEndpoints_iff [DecidableEq α] (X : Set α)
    (l : List α) (u : α) :
    u ∈ crossingEndpoints X l ↔
      ∃ v, (u, v) ∈ l.zip l.tail ∧ (u ∈ X ↔ v ∉ X) := by
  simp [crossingEndpoints, crosses]

/-- Counted membership changes bound the crossing-count change by two per
changed list entry. -/
lemma zipCrossingCount_le_add_two_mul_memberCount (X Y : Set α) (l : List α) :
    zipCrossingCount X l ≤
      zipCrossingCount Y l + 2 * memberCount ((X \ Y) ∪ (Y \ X)) l := by
  classical
  let pairs := l.zip l.tail
  have hpair := countPairCrossings_le X Y pairs
  have hfst :
      (pairs.map Prod.fst).countP
          (contains ((X \ Y) ∪ (Y \ X))) ≤
        l.countP (contains ((X \ Y) ∪ (Y \ X))) :=
    (map_fst_zip_tail_sublist l).countP_le
  have hsnd :
      (pairs.map Prod.snd).countP
          (contains ((X \ Y) ∪ (Y \ X))) ≤
        l.countP (contains ((X \ Y) ∪ (Y \ X))) := by
    rw [map_snd_zip_tail]
    exact (List.tail_sublist l).countP_le
  dsimp only [pairs] at hpair hfst hsnd
  change (l.zip l.tail).countP (fun p => crosses X p.1 p.2) ≤
    (l.zip l.tail).countP (fun p => crosses Y p.1 p.2) +
      2 * l.countP (contains ((X \ Y) ∪ (Y \ X)))
  have hpair' : zipCrossingCount X l ≤ zipCrossingCount Y l +
      List.countP (contains ((X \ Y) ∪ (Y \ X)))
        ((l.zip l.tail).map Prod.fst) +
      List.countP (contains ((X \ Y) ∪ (Y \ X)))
        ((l.zip l.tail).map Prod.snd) := by
    simpa [zipCrossingCount] using hpair
  rw [zipCrossingCount] at hpair'
  omega

/-- On a Nodup list, counted membership in a set is bounded by the set's
finite cardinality. -/
lemma memberCount_le_ncard [DecidableEq α] [Finite α]
    (D : Set α) {l : List α} (hl : l.Nodup) :
    memberCount D l ≤ D.ncard := by
  classical
  unfold memberCount contains
  rw [List.countP_eq_length_filter]
  rw [← List.toFinset_card_of_nodup (hl.filter (fun a => decide (a ∈ D)))]
  have hsub :
      ((l.filter (fun a => decide (a ∈ D))).toFinset : Set α) ⊆ D := by
    intro a ha
    simp at ha
    exact ha.2
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub

/-- The recursive Bool-valued crossing count satisfies the near-twin bound on
any Nodup list over a finite type. -/
lemma crossingCount_le_add_two_mul_symmDiff [DecidableEq α] [Finite α]
    (X Y : Set α) {l : List α} (hl : l.Nodup) :
    TwinExpansion.crossingCount (contains X) l ≤
      TwinExpansion.crossingCount (contains Y) l +
        2 * ((X \ Y) ∪ (Y \ X)).ncard := by
  rw [crossingCount_eq_zip, crossingCount_eq_zip]
  exact (zipCrossingCount_le_add_two_mul_memberCount X Y l).trans <| by
    have h := memberCount_le_ncard ((X \ Y) ∪ (Y \ X)) hl
    omega

end

end Lax457868Proofs.ListOrderBounds


namespace Lax457868Proofs.ListOrderBounds

noncomputable section

/-- The entry of a complete list at its corresponding finite index. -/
def vertexAt {n : ℕ} (l : List (Fin n)) (hlen : l.length = n)
    (i : Fin n) : Fin n := l.get ⟨i.val, by omega⟩

lemma vertexAt_bijective {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n) :
    Function.Bijective (vertexAt l hlen) := by
  constructor
  · intro i j hij
    apply Fin.ext
    have hget : (⟨i.val, by omega⟩ : Fin l.length) = ⟨j.val, by omega⟩ :=
      hl.get_inj_iff.mp hij
    exact congrArg (fun z : Fin l.length => z.val) hget
  · intro v
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hall v)
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    exact hi

def permutationOfList {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n) : Equiv.Perm (Fin n) :=
  (Equiv.ofBijective (vertexAt l hlen) (vertexAt_bijective l hl hall hlen)).symm

lemma ofFn_permutationOfList_symm {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n) :
    List.ofFn (permutationOfList l hl hall hlen).symm = l := by
  apply List.ext_get
  · simpa using hlen.symm
  · intro i hi h'i
    simp only [List.get_ofFn]
    rfl

lemma map_val_eq_ofFn {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n) :
    l.map Fin.val = List.ofFn
      (fun i : Fin n => ((permutationOfList l hl hall hlen).symm i).val) := by
  calc
    l.map Fin.val = (List.ofFn (permutationOfList l hl hall hlen).symm).map Fin.val := by
      rw [ofFn_permutationOfList_symm l hl hall hlen]
    _ = List.ofFn (fun i : Fin n => ((permutationOfList l hl hall hlen).symm i).val) := by
      rw [List.map_ofFn]
      rfl

lemma permutationOfList_val_eq_idxOf {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n)
    (v : Fin n) : ((permutationOfList l hl hall hlen) v).val = l.idxOf v := by
  let π := permutationOfList l hl hall hlen
  have hget : vertexAt l hlen (π v) = v := by
    exact Equiv.apply_symm_apply (Equiv.ofBijective (vertexAt l hlen)
      (vertexAt_bijective l hl hall hlen)) v
  have hidx := List.get_idxOf hl
    (⟨(π v).val, by have := (π v).isLt; omega⟩ : Fin l.length)
  change l.idxOf (vertexAt l hlen (π v)) = (π v).val at hidx
  rw [hget] at hidx
  exact hidx.symm

lemma crossingCount_permutationOfList {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n)
    (X : Set (Fin n)) :
    Lax195003.WelzlOrders.crossingCount (permutationOfList l hl hall hlen) X =
      TwinExpansion.crossingCount (contains X) l := by
  rw [crossingCount_eq_zip, ← ncard_crossingEndpoints X hl]
  unfold Lax195003.WelzlOrders.crossingCount
  congr 1
  ext u
  rw [Set.mem_ofPred_eq, mem_crossingEndpoints_iff]
  constructor
  · rintro ⟨v, hpos, hcross⟩
    refine ⟨v, ?_, hcross⟩
    rw [mem_zip_tail_iff_idxOf_succ hl]
    refine ⟨hall u, hall v, ?_⟩
    simpa only [← permutationOfList_val_eq_idxOf l hl hall hlen] using hpos
  · rintro ⟨v, huv, hcross⟩
    refine ⟨v, ?_, hcross⟩
    rw [mem_zip_tail_iff_idxOf_succ hl] at huv
    simpa only [← permutationOfList_val_eq_idxOf l hl hall hlen] using huv.2.2

lemma openNeighborhood_one_eq {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    {u : Fin n | u ≠ v ∧ ∃ w : G.Walk v u, w.length ≤ 1} = G.neighborSet v := by
  ext u
  constructor
  · rintro ⟨huv, w, hw⟩
    have hw0 : w.length ≠ 0 := by
      intro hzero
      exact huv (w.eq_of_length_eq_zero hzero).symm
    have hw1 : w.length = 1 := by omega
    exact w.adj_of_length_eq_one hw1
  · intro huv
    have hadj : G.Adj v u := by simpa using huv
    exact ⟨huv.ne.symm, hadj.toWalk, by simp⟩

lemma neighborhoodSetSystem_one {n : ℕ} (G : SimpleGraph (Fin n)) :
    Lax195003.WelzlOrdersNeighborhoodSetSystem.neighborhoodSetSystem G 1 =
      {X : Set (Fin n) | ∃ v : Fin n, X = G.neighborSet v} := by
  ext X
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, openNeighborhood_one_eq G v⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, (openNeighborhood_one_eq G v).symm⟩

lemma encodesGraphWelzlOrder_of_list_bound {n m : ℕ}
    (G : SimpleGraph (Fin n)) (l : List (Fin n)) (hl : l.Nodup)
    (hall : ∀ v : Fin n, v ∈ l) (hlen : l.length = n)
    (hbound : ∀ v : Fin n,
      TwinExpansion.crossingCount (contains (G.neighborSet v)) l ≤ m) :
    Lax195003.WelzlOrdersInGraphs.EncodesGraphWelzlOrder G 1 m (l.map Fin.val) := by
  let π := permutationOfList l hl hall hlen
  refine ⟨π, ?_, ?_⟩
  · exact map_val_eq_ofFn l hl hall hlen
  · apply (Lax457868Proofs.isWelzlOrder_iff_forall_crossingCount_le
      (Lax195003.WelzlOrdersNeighborhoodSetSystem.neighborhoodSetSystem G 1)
      π m).2
    intro X hX
    rw [neighborhoodSetSystem_one] at hX
    obtain ⟨v, rfl⟩ := hX
    rw [crossingCount_permutationOfList]
    exact hbound v

end

end Lax457868Proofs.ListOrderBounds
