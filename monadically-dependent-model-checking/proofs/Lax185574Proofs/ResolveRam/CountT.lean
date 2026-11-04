import Lax185574Proofs.ResolveRam.Count
import Lax185574Proofs.ResolveRam.Calls

/-!
The number of calls in terms of `T`, as in the paragraph "Number of
calls" of the proof of lem:resolve-lift.

An item of level `d` is the tree of a tuple `w` that is reached from a
vertex by guarded extensions in `H` (`lvR_goodH`). Its old extensions are
candidates, so there are at most `(d + 1) · T` of them by
`card_candidatesF_le`. The members of the far tree that pass the test
are trees of single vertices of the ball of radius `ρ⁺(k₀, q₀)` around
`w 0` in `H` (by lem:locality), so there are at most `T` of them. Hence
the expansion of an item has at most `(k₀ + q₀ + 2)² · T` members and the
number of calls is at most `callMaxT`, which is `|G|` times a polynomial
in `T`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.TypeTreeSizes
open Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- An item of level `d` is the tree of a tuple reached by guarded
extensions in `H`. -/
def GoodH (d : ℕ) (x : Item) : Prop :=
  ∃ w : Fin (d + 1) → Fin n, Guarded (resolveBy G s P Q) k₀ q₀ d w ∧
    x.2 = tree G (k₀ + d) (q₀ - d) w

theorem lvR_goodH (hk₀ : 1 ≤ k₀) : ∀ d ≤ q₀, ∀ x ∈ lvR G P Q s k₀ q₀ d, GoodH G P Q s k₀ q₀ d x
  | 0, _, x, hx => by
    simp only [lvR, levels, Function.iterate_zero, id, famItems, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    refine ⟨![b], fun i hi => absurd hi (by have := i.isLt; omega), ?_⟩
    simp [family]
  | d + 1, hd, x, hx => by
    unfold lvR at hx
    rw [levels_succ] at hx
    obtain ⟨i, hi, gc, hgc, rfl⟩ := mem_nextLevel.1 hx
    obtain ⟨w, hw, hwx⟩ := lvR_goodH hk₀ d (by omega) _ (List.getElem_mem hi)
    obtain ⟨m, hm⟩ : ∃ m, q₀ - d = m + 1 := ⟨q₀ - d - 1, by omega⟩
    rw [hwx, hm] at hgc
    obtain ⟨e, he, rfl⟩ := (expandOK_exR G P Q s k₀ q₀ (k₀ + d) m (d + 1) w (by omega) (by omega)
      (by omega) (by omega) gc).1 hgc
    obtain ⟨j, b, hb, rfl⟩ := (mem_candidatesF _ (farMapOf G) (dataOf_spec G P Q s k₀ q₀)
      (farSpec_farMapOf G) w (by omega) (by omega) (by omega) (by omega) e).1 he
    refine ⟨Fin.snoc w b, guarded_snoc hw j b ?_, ?_⟩
    · rw [show k₀ + (d + 1) = k₀ + d + 1 by omega, show q₀ - (d + 1) = m by omega]
      exact hb
    · simp only [tree]
      rw [show q₀ - (d + 1) = m by omega, show k₀ + (d + 1) = k₀ + d + 1 by omega]

theorem nodup_elems {α : Type*} [WordEncoding α] (S : Finset α) : (elems S).Nodup := by
  refine List.Nodup.of_map toWord ?_
  rw [map_elems]
  unfold Finset.words
  exact Finset.sort_nodup _ _

/-- At most `T` members of the far tree pass the test. -/
theorem length_faP_leT (hk₀ : 1 ≤ k₀) {d m : ℕ} (hdm : d + (m + 1) = q₀) (w : Fin (d + 1) → Fin n)
    (hw : Guarded (resolveBy G s P Q) k₀ q₀ d w) :
    (faP G (dataOf G P Q s k₀ q₀) (tree G (k₀ + d) (m + 1) w)).length ≤
      treeCount G (resolveBy G s P Q) k₀ q₀ := by
  classical
  set H := resolveBy G s P Q
  set D := dataOf G P Q s k₀ q₀
  set L := faP G D (tree G (k₀ + d) (m + 1) w)
  have hnd : L.Nodup := (nodup_elems _).filter _
  have hsub : (↑L.toFinset : Set TypeTree) ⊆ treeSet G H k₀ q₀ (w 0) := by
    intro ν hν
    rw [Finset.mem_coe, List.mem_toFinset] at hν
    obtain ⟨hν1, hν2⟩ := List.mem_filter.1 hν
    have hfa := ((ansOK_of G k₀ q₀).fa (k₀ + d) m (d + 1) w (by omega) (by omega) (by omega)
      (by omega) ν).1 hν1
    obtain ⟨b, -, rfl⟩ := (mem_ftree (G := G) (k₀ + d) m w ν).1 hfa
    rw [shOf_tree G w (by omega) (by omega)] at hν2
    have hhop : ∃ i : Fin (d + 1), Hop G P Q (rhoPlus (k₀ + d + 1) m) (w i) b := by
      unfold passF at hν2
      split_ifs at hν2 with h0
      · rw [decide_eq_true_eq] at hν2
        obtain ⟨i, hi⟩ := hν2
        exact ⟨i, (hop2_node D (dataOf_spec G P Q s k₀ q₀).1 w ![b] i 0 le_rfl).1 hi⟩
    obtain ⟨i, hi⟩ := hhop
    have hwd : WithinDist H.resolved (rhoPlus (k₀ + (d + 1)) (q₀ - (d + 1))) (w i) b := by
      rw [resolveBy_resolved, withinDist_resolve_iff,
        show k₀ + (d + 1) = k₀ + d + 1 by omega, show q₀ - (d + 1) = m by omega]
      exact Or.inr hi
    have hg := guarded_snoc hw i b hwd
    have hball := (Lax185574.TreeLocality.ball_of_guarded H k₀ q₀ (d + 1) (by omega)
      (Fin.snoc w b) hg).1 (Fin.last (d + 1))
    rw [Fin.snoc_last, snoc_zero] at hball
    refine ⟨d + 1, 1, ![b], by omega, le_rfl, by omega, fun j => ?_, ?_⟩
    · rw [Fin.fin_one_eq_zero j]; exact hball
    · simp only [tree]
      rw [show q₀ - (d + 1) = m by omega, show k₀ + (d + 1) = k₀ + d + 1 by omega]
  calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ = (↑L.toFinset : Set TypeTree).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (treeSet G H k₀ q₀ (w 0)).ncard := Set.ncard_le_ncard hsub (treeSet_finite G H k₀ q₀ (w 0))
    _ ≤ _ := ncard_treeSet_le G H k₀ q₀ (w 0)

theorem length_exAt_le' (D : ResolveData) {k q ℓ : ℕ} (t : Node (q + 1) ℓ) :
    (exAt D (shOf G) (faP G D) (coOf G) k q ℓ t).length ≤
      (Node.exts t).card * (ℓ + 1) + (faP G D ⟨k, q + 1, ℓ, t⟩).length * ℓ := by
  unfold exAt
  simp only [List.length_append, List.length_map]
  have he := length_elems_le (Node.exts t)
  have h2 := length_flatMap_le (elems (Node.exts t))
    (fun e => guarded D (rhoPlus (k + 1) q) e.2 ⟨k + 1, q, ℓ + 1, e.2⟩) ℓ
    (fun e _ => length_guarded_le D _ _ _)
  have h3 := length_flatMap_le (faP G D ⟨k, q + 1, ℓ, t⟩)
    (fun ν => (TypeTree.rootAs (coOf G (shOf G ⟨k, q + 1, ℓ, t⟩) ν) q (ℓ + 1)).toList.flatMap
      fun r => guarded D (rhoPlus (k + 1) q) r (coOf G (shOf G ⟨k, q + 1, ℓ, t⟩) ν)) ℓ
    (fun ν _ => by
      refine le_trans (length_flatMap_le _ _ ℓ fun r _ => length_guarded_le D _ _ _) ?_
      rcases TypeTree.rootAs _ q (ℓ + 1) with _ | r <;> simp)
  have e2 : (elems (Node.exts t)).length * ℓ ≤ (Node.exts t).card * ℓ := Nat.mul_le_mul_right _ he
  have e3 : (Node.exts t).card * (ℓ + 1) = (Node.exts t).card * ℓ + (Node.exts t).card := by ring
  omega

/-- The bound on the expansion of an item in terms of `T`. -/
noncomputable def exMaxT (k₀ q₀ : ℕ) (T : ℕ) : ℕ := (k₀ + q₀ + 2) ^ 2 * T

theorem length_exR_leT (hk₀ : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) {x : Item}
    (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    (exR G P Q s k₀ q₀ x.2).length ≤ exMaxT k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  obtain ⟨w, hw, hwx⟩ := lvR_goodH G P Q s k₀ q₀ hk₀ d hd x hx
  set T := treeCount G (resolveBy G s P Q) k₀ q₀
  rw [hwx]
  rcases Nat.lt_or_ge d q₀ with hlt | hge
  · obtain ⟨m, hm⟩ : ∃ m, q₀ - d = m + 1 := ⟨q₀ - d - 1, by omega⟩
    rw [hm]
    show (exAt _ (shOf G) (faP G _) (coOf G) (k₀ + d) m (d + 1) (node G (k₀ + d) (m + 1) w)).length ≤ _
    refine le_trans (length_exAt_le' G _ _) ?_
    have hsub : Node.exts (node G (k₀ + d) (m + 1) w) ⊆
        candidatesF (dataOf G P Q s k₀ q₀) (farMapOf G) (k₀ + d) m (d + 1) (node G (k₀ + d) (m + 1) w) := by
      intro e he
      unfold candidatesF
      exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
    have hc := card_candidatesF_le G (dataOf G P Q s k₀ q₀) (farMapOf G) hk₀
      (dataOf_spec G P Q s k₀ q₀) (farSpec_farMapOf G) (w 0) d m (by omega) w rfl hw
    have h1 : (Node.exts (node G (k₀ + d) (m + 1) w)).card ≤ (d + 1) * T :=
      le_trans (Finset.card_le_card hsub) hc
    have h2 := length_faP_leT G P Q s k₀ q₀ hk₀ (show d + (m + 1) = q₀ by omega) w hw
    have h2' : (faP G (dataOf G P Q s k₀ q₀) ⟨k₀ + d, m + 1, d + 1, node G (k₀ + d) (m + 1) w⟩).length ≤ T := h2
    unfold exMaxT
    have a1 : (Node.exts (node G (k₀ + d) (m + 1) w)).card * (d + 1 + 1) ≤ (d + 1) * T * (d + 2) :=
      Nat.mul_le_mul_right _ h1
    have a2 : (faP G (dataOf G P Q s k₀ q₀) ⟨k₀ + d, m + 1, d + 1, node G (k₀ + d) (m + 1) w⟩).length *
        (d + 1) ≤ T * (d + 1) := Nat.mul_le_mul_right _ h2'
    have a3 : (d + 1) * T * (d + 2) + T * (d + 1) ≤ (k₀ + q₀ + 2) ^ 2 * T := by
      have : (d + 1) * (d + 2) + (d + 1) ≤ (k₀ + q₀ + 2) ^ 2 := by nlinarith
      nlinarith
    omega
  · rw [show q₀ - d = 0 by omega]
    show ([] : List (ℕ × TypeTree)).length ≤ _
    simp

theorem length_lvR_leT (hk₀ : 1 ≤ k₀) : ∀ d ≤ q₀,
    (lvR G P Q s k₀ q₀ d).length ≤
      n * exMaxT k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) ^ d
  | 0, _ => by simp [lvR, levels, famItems]
  | d + 1, hd => by
    have ih := length_lvR_leT hk₀ d (by omega)
    unfold lvR at ih ⊢
    rw [levels_succ]
    refine le_trans (length_nextLevel_le _ _ _ fun x hx =>
      length_exR_leT G P Q s k₀ q₀ hk₀ (by omega) hx) ?_
    rw [pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul_right _ ih

/-- The bound on the number of calls in terms of `|G|` and `T`. -/
noncomputable def callMaxT (k₀ q₀ n T : ℕ) : ℕ :=
  1 + (q₀ + 1) * ((T + 6) * (n * (exMaxT k₀ q₀ T + 1) ^ q₀))

/-- **The number of calls.** -/
theorem length_rcalls_leT (hk₀ : 1 ≤ k₀) :
    (rcalls G P Q s k₀ q₀).length ≤ callMaxT k₀ q₀ n (treeCount G (resolveBy G s P Q) k₀ q₀) := by
  set T := treeCount G (resolveBy G s P Q) k₀ q₀ with hT
  have hL : ∀ d ≤ q₀, (lvR G P Q s k₀ q₀ d).length ≤ n * (exMaxT k₀ q₀ T + 1) ^ q₀ := by
    intro d hd
    refine le_trans (length_lvR_leT G P Q s k₀ q₀ hk₀ d hd) (Nat.mul_le_mul_left _ ?_)
    exact le_trans (Nat.pow_le_pow_left (Nat.le_succ _) d) (Nat.pow_le_pow_right (by omega) hd)
  set N := n * (exMaxT k₀ q₀ T + 1) ^ q₀ with hN
  unfold rcalls
  split_ifs with hn
  · simp
  simp only [List.length_cons, List.length_append]
  have hdown : (downAll G P Q s k₀ q₀).length ≤ q₀ * ((T + 4) * N) := by
    unfold downAll
    refine le_trans (length_flatMap_le _ _ ((T + 4) * N) fun d hd => ?_) (by simp)
    have hd' : d < q₀ := List.mem_range.1 hd
    refine le_trans (length_flatMap_le _ _ (T + 4) fun x hx => ?_) ?_
    · obtain ⟨w, hw, hwx⟩ := lvR_goodH G P Q s k₀ q₀ hk₀ d hd'.le x hx
      simp only [downCalls, List.length_append, List.length_cons, List.length_nil, List.length_map]
      rw [hwx, show q₀ - d = q₀ - d - 1 + 1 by omega]
      have := length_faP_leT G P Q s k₀ q₀ hk₀ (show d + (q₀ - d - 1 + 1) = q₀ by omega) w hw
      omega
    · rw [mul_comm]; exact Nat.mul_le_mul_left _ (hL d hd'.le)
  have hup : (upAll G P Q s k₀ q₀).length ≤ (q₀ + 1) * (2 * N) := by
    unfold upAll
    refine le_trans (length_flatMap_le _ _ (2 * N) fun d hd => ?_) (by simp)
    have hd' : d ≤ q₀ := by simp at hd; omega
    refine le_trans (length_flatMap_le _ _ 2 fun y _ => ?_) ?_
    · simp only [upCalls]; split_ifs <;> simp
    · rw [List.length_zipIdx, mul_comm]; exact Nat.mul_le_mul_left _ (hL d hd')
  unfold callMaxT
  rw [← hN]
  have : q₀ * ((T + 4) * N) + (q₀ + 1) * (2 * N) ≤ (q₀ + 1) * ((T + 6) * N) := by nlinarith
  omega

end Lax185574Proofs.ResolveRam
