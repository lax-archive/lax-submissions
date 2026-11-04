import Lax185574Proofs.ResolveRam.CallList

/-!
A crude bound on the number of calls in terms of `|G|`.

A tree of a tuple of `G` of arity `ℓ` has at most `ℓ · |G|` extensions,
and its far tree at most `|G|` members. So the expansion of an item has
at most `(k₀ + q₀ + 2)² · |G|` members, level `d` has at most
`|G| · ((k₀ + q₀ + 2)² · |G|)^d` items, and the number of calls is at
most `callMax k₀ q₀ |G|`. The soundness of the composite uses this bound
when the input is small compared with the constants of the rank.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.WordEncoding Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoMinus rhoPlus)

theorem length_elems_le {α : Type*} [WordEncoding α] (S : Finset α) : (elems S).length ≤ S.card := by
  unfold elems
  refine le_trans (List.length_filterMap_le _ _) ?_
  unfold Finset.words
  rw [Finset.length_sort]
  exact Finset.card_image_le

variable {n : ℕ} (G : PartialGraph (Fin n))

theorem card_exts_le (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) :
    (Node.exts (node G k (q + 1) u)).card ≤ ℓ * n := by
  classical
  have hsub : Node.exts (node G k (q + 1) u) ⊆
      (Finset.univ : Finset (Fin ℓ × Fin n)).image fun p => (p.1, node G (k + 1) q (Fin.snoc u p.2)) := by
    intro e he
    obtain ⟨i, b, -, rfl⟩ := (mem_exts_node G k q u e).1 he
    exact Finset.mem_image.2 ⟨(i, b), Finset.mem_univ _, rfl⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
  simp

theorem card_ftree_le (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) : (ftree G k (q + 1) u).card ≤ n := by
  classical
  have hsub : ftree G k (q + 1) u ⊆ (Finset.univ : Finset (Fin n)).image fun b => tree G (k + 1) q ![b] := by
    intro ν hν
    obtain ⟨b, -, rfl⟩ := (mem_ftree (G := G) k q u ν).1 hν
    exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
  simp

theorem length_faOf_le {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    (faOf G (tree G k (q + 1) u)).length ≤ n := by
  show (elems (farMapOf G k q ℓ (node G k (q + 1) u) ∅)).length ≤ n
  have e : farMapOf G k q ℓ (node G k (q + 1) u) ∅ = ftree G k (q + 1) u :=
    farSpec_farMapOf G k q ℓ u h1 hk
  rw [e]
  exact le_trans (length_elems_le _) (card_ftree_le G k q u)

theorem length_faP_le (D : ResolveData) {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    (faP G D (tree G k (q + 1) u)).length ≤ n :=
  le_trans (List.length_filter_le _ _) (length_faOf_le G u h1 hk)

theorem length_guarded_le (D : ResolveData) {q ℓ : ℕ} (R : ℕ) (r : Node q (ℓ + 1)) (c : TypeTree) :
    (guarded D R r c).length ≤ ℓ := by
  unfold guarded
  exact le_trans (List.length_filterMap_le _ _) (by simp)

theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    have := h a (by simp)
    rw [Nat.succ_mul]; omega

theorem length_exAt_le (D : ResolveData) {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ)
    (hk : ℓ ≤ k) :
    (exAt D (shOf G) (faP G D) (coOf G) k q ℓ (node G k (q + 1) u)).length ≤ (ℓ + 2) ^ 2 * n := by
  unfold exAt
  simp only [List.length_append, List.length_map]
  have he := length_elems_le (Node.exts (node G k (q + 1) u))
  have hc := card_exts_le G k q u
  have h2 := length_flatMap_le (elems (Node.exts (node G k (q + 1) u)))
    (fun e => guarded D (rhoPlus (k + 1) q) e.2 ⟨k + 1, q, ℓ + 1, e.2⟩) ℓ
    (fun e _ => length_guarded_le D _ _ _)
  have hτ : (⟨k, q + 1, ℓ, node G k (q + 1) u⟩ : TypeTree) = tree G k (q + 1) u := rfl
  have h3 := length_flatMap_le (faP G D ⟨k, q + 1, ℓ, node G k (q + 1) u⟩)
    (fun ν => (TypeTree.rootAs (coOf G (shOf G ⟨k, q + 1, ℓ, node G k (q + 1) u⟩) ν) q (ℓ + 1)).toList.flatMap
      fun r => guarded D (rhoPlus (k + 1) q) r (coOf G (shOf G ⟨k, q + 1, ℓ, node G k (q + 1) u⟩) ν)) ℓ
    (fun ν _ => by
      refine le_trans (length_flatMap_le _ _ ℓ fun r _ => length_guarded_le D _ _ _) ?_
      rcases TypeTree.rootAs _ q (ℓ + 1) with _ | r <;> simp)
  have h4 := length_faP_le G D (q := q) u h1 hk
  rw [hτ] at h3
  have e1 : (elems (Node.exts (node G k (q + 1) u))).length ≤ ℓ * n := le_trans he hc
  have e2 : (elems (Node.exts (node G k (q + 1) u))).length * ℓ ≤ ℓ * n * ℓ :=
    Nat.mul_le_mul_right _ e1
  have e3 : (faP G D (tree G k (q + 1) u)).length * ℓ ≤ n * ℓ := Nat.mul_le_mul_right _ h4
  have e4 : ℓ * n + ℓ * n * ℓ + n * ℓ ≤ (ℓ + 2) ^ 2 * n := by ring_nf; nlinarith
  simp only [hτ] at h2 h3 ⊢
  omega

theorem length_nextLevel_le (ex : TypeTree → List (ℕ × TypeTree)) (L : List Item) (B : ℕ)
    (h : ∀ x ∈ L, (ex x.2).length ≤ B) : (nextLevel ex L).length ≤ L.length * B := by
  unfold nextLevel
  refine le_trans (length_flatMap_le _ _ B fun x hx => ?_) (by simp)
  rw [List.length_map]
  rw [List.mem_zipIdx_iff_getElem?] at hx
  exact h _ (List.mem_of_getElem? hx)

variable (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The bound on the expansion of an item. -/
def exMax (k₀ q₀ n : ℕ) : ℕ := (k₀ + q₀ + 2) ^ 2 * n

theorem length_exR_le (hk₀ : 1 ≤ k₀) {d : ℕ} (hd : d ≤ q₀) {x : Item} (hx : x ∈ lvR G P Q s k₀ q₀ d) :
    (exR G P Q s k₀ q₀ x.2).length ≤ exMax k₀ q₀ n := by
  obtain ⟨ℓ, u, hu, h1, hk⟩ := lvR_good G P Q s k₀ q₀ hk₀ hd hx
  rw [hu]
  rcases Nat.lt_or_ge d q₀ with hlt | hge
  · obtain ⟨m, hm⟩ : ∃ m, q₀ - d = m + 1 := ⟨q₀ - d - 1, by omega⟩
    rw [hm]
    show (exAt _ (shOf G) (faP G _) (coOf G) (k₀ + d) m ℓ (node G (k₀ + d) (m + 1) u)).length ≤ _
    refine le_trans (length_exAt_le G _ u h1 hk) ?_
    unfold exMax
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
  · rw [show q₀ - d = 0 by omega]
    show ([] : List (ℕ × TypeTree)).length ≤ _
    simp

theorem length_lvR_le (hk₀ : 1 ≤ k₀) : ∀ d ≤ q₀,
    (lvR G P Q s k₀ q₀ d).length ≤ n * exMax k₀ q₀ n ^ d
  | 0, _ => by simp [lvR, levels, famItems]
  | d + 1, hd => by
    have ih := length_lvR_le hk₀ d (by omega)
    unfold lvR at ih ⊢
    rw [levels_succ]
    refine le_trans (length_nextLevel_le _ _ (exMax k₀ q₀ n) fun x hx =>
      length_exR_le G P Q s k₀ q₀ hk₀ (by omega) hx) ?_
    rw [pow_succ, ← mul_assoc]
    exact Nat.mul_le_mul_right _ ih

/-- The bound on the number of calls. -/
def callMax (k₀ q₀ n : ℕ) : ℕ := 1 + (q₀ + 1) * ((n + 6) * (n * (exMax k₀ q₀ n + 1) ^ q₀))

theorem callMax_mono (k₀ q₀ : ℕ) {n m : ℕ} (h : n ≤ m) : callMax k₀ q₀ n ≤ callMax k₀ q₀ m := by
  unfold callMax exMax
  gcongr

theorem length_rcalls_le (hk₀ : 1 ≤ k₀) :
    (rcalls G P Q s k₀ q₀).length ≤ callMax k₀ q₀ n := by
  have hL : ∀ d ≤ q₀, (lvR G P Q s k₀ q₀ d).length ≤ n * (exMax k₀ q₀ n + 1) ^ q₀ := by
    intro d hd
    refine le_trans (length_lvR_le G P Q s k₀ q₀ hk₀ d hd) (Nat.mul_le_mul_left _ ?_)
    exact le_trans (Nat.pow_le_pow_left (Nat.le_succ _) d) (Nat.pow_le_pow_right (by omega) hd)
  set N := n * (exMax k₀ q₀ n + 1) ^ q₀ with hN
  unfold rcalls
  split_ifs with hn
  · simp
  simp only [List.length_cons, List.length_append]
  have hdown : (downAll G P Q s k₀ q₀).length ≤ q₀ * ((n + 4) * N) := by
    unfold downAll
    refine le_trans (length_flatMap_le _ _ ((n + 4) * N) fun d hd => ?_) (by simp)
    have hd' : d < q₀ := List.mem_range.1 hd
    refine le_trans (length_flatMap_le _ _ (n + 4) fun x hx => ?_) ?_
    · obtain ⟨ℓ, u, hu, h1, hk⟩ := lvR_good G P Q s k₀ q₀ hk₀ hd'.le hx
      simp only [downCalls, List.length_append, List.length_cons, List.length_nil, List.length_map]
      rw [hu, show q₀ - d = q₀ - d - 1 + 1 by omega]
      have := length_faP_le G (dataOf G P Q s k₀ q₀) (q := q₀ - d - 1) u h1 hk
      omega
    · rw [mul_comm]; exact Nat.mul_le_mul_left _ (hL d hd'.le)
  have hup : (upAll G P Q s k₀ q₀).length ≤ (q₀ + 1) * (2 * N) := by
    unfold upAll
    refine le_trans (length_flatMap_le _ _ (2 * N) fun d hd => ?_) (by simp)
    have hd' : d ≤ q₀ := by simp at hd; omega
    refine le_trans (length_flatMap_le _ _ 2 fun y _ => ?_) ?_
    · simp only [upCalls]; split_ifs <;> simp
    · rw [List.length_zipIdx, mul_comm]; exact Nat.mul_le_mul_left _ (hL d hd')
  unfold callMax
  rw [← hN]
  have : q₀ * ((n + 4) * N) + (q₀ + 1) * (2 * N) ≤ (q₀ + 1) * ((n + 6) * N) := by nlinarith
  omega

end Lax185574Proofs.ResolveRam
