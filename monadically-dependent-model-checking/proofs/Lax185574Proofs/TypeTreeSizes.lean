import Lax185574.TypeTreeSizes
import Lax185574.TreeEquivalence
import Lax185574.TreeLocality
import Lax185574Proofs.DistanceTranslation
import Mathlib.Algebra.Order.BigOperators.Group.List
import Lax185574Proofs.Legacy

/-!
Proof of lem:ball-tree-bound. Ordinary types of quantifier rank
`ρ⁺(k, q) + q` determine type trees of rank `(k, q)`, because a distance
formula translates into a first-order formula of that rank, and type trees
are distance types by cor:tp-tree. This bounds the number of type trees by
the number of types. The size of a type tree is then bounded by counting
its atoms and its extensions, all of which live in a ball around the root
vertex by lem:locality.
-/

namespace Lax185574Proofs.TypeTreeSizes

open FirstOrder FirstOrder.Language
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.FirstOrderTypes
open Lax185574.WordEncoding Lax185574.Width
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574Proofs.DistanceTranslation Lax185574Proofs.WalkDistance
open Lax185574Proofs.DistanceFormulaRank
open Lax3.DistFO (rhoMinus rhoPlus)

/-! ### Types determine type trees -/

section Types

variable {n : ℕ} (G : PartialGraph (Fin n))

/-- The type of quantifier rank `d` of a tuple in the partial graph `G`. -/
abbrev tp (d : ℕ) {ℓ : ℕ} (v : Fin ℓ → Fin n) : Set (language.Formula (Fin ℓ)) :=
  @rankType language (Fin n) G.structure d ℓ v

theorem tp_mono {d d' : ℕ} (h : d' ≤ d) {ℓ : ℕ} {v w : Fin ℓ → Fin n}
    (hvw : tp G d v = tp G d w) : tp G d' v = tp G d' w := by
  ext φ
  simp only [rankType, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hq, hr⟩
    have : φ ∈ tp G d v := ⟨hq.trans h, hr⟩
    rw [hvw] at this
    exact ⟨hq, this.2⟩
  · rintro ⟨hq, hr⟩
    have : φ ∈ tp G d w := ⟨hq.trans h, hr⟩
    rw [← hvw] at this
    exact ⟨hq, this.2⟩

/-- Restricting tuples to their first `ℓ` entries preserves equality of
types. -/
theorem tp_castLE {d ℓ m : ℕ} (h : ℓ ≤ m) {v w : Fin m → Fin n} (hvw : tp G d v = tp G d w) :
    tp G d (v ∘ Fin.castLE h) = tp G d (w ∘ Fin.castLE h) := by
  let _ := G.structure
  ext φ
  have key : ∀ u : Fin m → Fin n,
      φ ∈ tp G d (u ∘ Fin.castLE h) ↔ φ.relabel (Fin.castLE h) ∈ tp G d u := by
    intro u
    simp only [rankType, Set.mem_ofPred_eq, qr_formula_relabel, Formula.realize_relabel]
  rw [key, key, hvw]

/-- **Equation (eq:tp-to-tree).** Tuples with the same type of quantifier
rank `ρ⁺(k, q) + q` have the same type tree of rank `(k, q)`. -/
theorem tree_eq_of_tp_eq (k q : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ k) (a b : Fin ℓ → Fin n)
    (h : tp G (rhoPlus k q + q) a = tp G (rhoPlus k q + q) b) : tree G k q a = tree G k q b := by
  refine (Lax185574.TreeEquivalence.tree_eq_iff G k q hℓ a b).2 fun φ hφ => ?_
  have hmem : ∀ u : Fin ℓ → Fin n, toFO φ ∈ tp G (rhoPlus k q + q) u ↔ Sat G u φ := by
    intro u
    simp only [rankType, Set.mem_ofPred_eq, qr_toFO hφ, true_and]
    exact realize_toFO G φ u
  rw [← hmem a, ← hmem b, h]

end Types

theorem rhoPlus_shift_le (k q i : ℕ) (hi : i ≤ q) : rhoPlus (k + i) (q - i) ≤ rhoPlus k q :=
  Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul (by omega) (by omega))

/-! ### Part (i): counting type trees -/

/-- The tuple `v` padded to length `m` by repeating its last entry. -/
def pad {α : Type*} {ℓ : ℕ} (m : ℕ) (hℓ : 1 ≤ ℓ) (v : Fin ℓ → α) : Fin m → α :=
  fun j => v ⟨min j.val (ℓ - 1), by omega⟩

theorem pad_castLE {α : Type*} {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (h : ℓ ≤ m) (v : Fin ℓ → α) :
    pad m hℓ v ∘ Fin.castLE h = v := by
  funext i
  simp only [pad, Function.comp_apply, Fin.val_castLE]
  congr 1
  ext
  simp only
  omega

/--
---
conclusion: Lax185574.TypeTreeSizes.treeCount_le
---
A tuple `v̄ ∈ X^ℓ` is padded to a `d`-tuple by repeating its last entry.
The type of quantifier rank `d` of the padded tuple determines the type of
`v̄` of quantifier rank `d`, which determines `tree_{k+i,q−i}(v̄)` by
`tree_eq_of_tp_eq`, since `ρ⁺(k+i, q−i) + q − i ≤ d`. So the type trees
are the image of a function on `Types_{d,d}(X)`.
-/
theorem treeCount_le {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) (_hk : 1 ≤ k)
    (i ℓ : ℕ) (hi : i ≤ q) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k + i) (X : Set (Fin n)) :
    Set.ncard {τ : TypeTree | ∃ v : Fin ℓ → Fin n, (∀ j, v j ∈ X) ∧ τ = tree G (k + i) (q - i) v} ≤
      partialTypeCount G (rhoPlus k q + k + q) (rhoPlus k q + k + q) X := by
  classical
  set d := rhoPlus k q + k + q
  have hℓd : ℓ ≤ d := by omega
  let Xd : Set (Fin d → Fin n) := {w | ∀ j, w j ∈ X}
  let g : Set (language.Formula (Fin d)) → TypeTree := fun t =>
    if h : ∃ w : Fin d → Fin n, w ∈ Xd ∧ tp G d w = t then
      tree G (k + i) (q - i) (Classical.choose h ∘ Fin.castLE hℓd)
    else tree G 0 0 Fin.elim0
  have hsub : {τ : TypeTree | ∃ v : Fin ℓ → Fin n, (∀ j, v j ∈ X) ∧
      τ = tree G (k + i) (q - i) v} ⊆ g '' (tp G d '' Xd) := by
    rintro τ ⟨v, hv, rfl⟩
    refine ⟨tp G d (pad d hℓ v), ⟨pad d hℓ v, fun j => hv _, rfl⟩, ?_⟩
    have h : ∃ w : Fin d → Fin n, w ∈ Xd ∧ tp G d w = tp G d (pad d hℓ v) :=
      ⟨pad d hℓ v, fun j => hv _, rfl⟩
    simp only [g, dif_pos h]
    have hw := (Classical.choose_spec h).2
    have h1 := tp_castLE G hℓd hw
    rw [pad_castLE] at h1
    refine tree_eq_of_tp_eq G (k + i) (q - i) hℓk _ _ (tp_mono G ?_ h1)
    have := rhoPlus_shift_le k q i hi
    omega
  have hfin : (tp G d '' Xd).Finite := Set.toFinite _
  calc _ ≤ (g '' (tp G d '' Xd)).ncard := Set.ncard_le_ncard hsub (hfin.image g)
    _ ≤ (tp G d '' Xd).ncard := Set.ncard_image_le hfin
    _ = partialTypeCount G d d X := rfl

/-! ### Word lengths -/

theorem card_finsetOf {α : Type*} (S : Set α) : (finsetOf S).card = S.ncard := by
  classical
  unfold finsetOf
  split_ifs with h
  · exact (Set.ncard_eq_toFinset_card S h).symm
  · rw [Set.Infinite.ncard h]
    rfl

theorem mem_of_mem_finsetOf {α : Type*} {S : Set α} {x : α} (h : x ∈ finsetOf S) : x ∈ S := by
  classical
  unfold finsetOf at h
  split_ifs at h with hS
  · exact hS.mem_toFinset.1 h
  · simp at h

theorem wordLength_list {α : Type*} [WordEncoding α] (l : List α) :
    wordLength l = 1 + (l.map wordLength).sum := by
  show (l.length :: (l.map toWord).flatten).length = _
  simp only [List.length_cons, List.length_flatten, List.map_map]
  rw [add_comm]
  rfl

theorem wordLength_list_nat (w : List ℕ) : wordLength w = w.length + 1 := by
  rw [wordLength_list]
  have : w.map (wordLength (α := ℕ)) = w.map (fun _ => 1) := List.map_congr_left (fun _ _ => rfl)
  rw [this, List.map_const', List.sum_replicate, smul_eq_mul, mul_one, add_comm]

/-- A finite set of elements of word length at most `B` has word length at
most `1 + |S| (B + 1)`. -/
theorem wordLength_finset_le {α : Type*} [WordEncoding α] (S : Finset α) (B : ℕ)
    (h : ∀ x ∈ S, wordLength x ≤ B) : wordLength S ≤ 1 + S.card * (B + 1) := by
  classical
  have hw : ∀ w ∈ Finset.words S, wordLength w ≤ B + 1 := by
    intro w hw
    simp only [Finset.words, Finset.mem_sort, Finset.mem_image] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    rw [wordLength_list_nat]
    exact Nat.succ_le_succ (h x hx)
  have hlen : (Finset.words S).length ≤ S.card := by
    simp only [Finset.words, Finset.length_sort]
    exact Finset.card_image_le
  show wordLength (Finset.words S) ≤ _
  rw [wordLength_list]
  have h1 := List.sum_le_card_nsmul ((Finset.words S).map wordLength) (B + 1) (by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨w, hw', rfl⟩ := hx
    exact hw w hw')
  simp only [List.length_map, smul_eq_mul] at h1
  have := Nat.mul_le_mul_right (B + 1) hlen
  omega

theorem wordLength_atom_le {ℓ : ℕ} (φ : DistFO ℓ) (h : IsAtom φ) : wordLength φ ≤ 5 := by
  cases φ <;> simp_all [DistFO.IsAtom, wordLength, word_simps, code]

/-! ### Counting atoms -/

/-- A key of an atom: its kind, its radius, its color and its positions. -/
def atomKey {ℓ : ℕ} : DistFO ℓ → ℕ × ℕ × ℕ × ℕ × ℕ
  | .eq i j => (0, 0, 0, i, j)
  | .edge i j => (1, 0, 0, i, j)
  | .nonEdge i j => (2, 0, 0, i, j)
  | .color Y i => (3, 0, Y, i, i)
  | .distLe r i j => (4, r, 0, i, j)
  | .distColorLt r Y i => (5, r, Y, i, i)
  | _ => (6, 0, 0, 0, 0)

theorem atomKey_injOn {ℓ : ℕ} : Set.InjOn (atomKey (ℓ := ℓ)) {φ | DistFO.IsAtom φ} := by
  intro φ hφ ψ hψ h
  cases φ <;> cases ψ <;> simp_all [atomKey, DistFO.IsAtom, Fin.val_inj]

theorem drank_distLe {k q ℓ r : ℕ} {i j : Fin ℓ} (h : DRank k q (.distLe r i j)) :
    r ≤ rhoMinus k q := by
  cases h
  assumption

theorem drank_distColorLt {k q ℓ r Y : ℕ} {i : Fin ℓ} (h : DRank k q (.distColorLt r Y i)) :
    r ≤ rhoPlus k q := by
  cases h
  assumption

/-- The atoms that hold of a tuple of length `ℓ` have radii at most `R`
and mention only colors from `C`, so there are at most
`6 (R+1) (|C|+1) ℓ²` of them. -/
theorem ncard_atp_le {V : Type*} (G : PartialGraph V) (k q ℓ : ℕ) (w : Fin ℓ → V) (R : ℕ)
    (hR : rhoPlus k q ≤ R) (C : Set ℕ) (hC : C.Finite)
    (hcol : ∀ φ ∈ atp G k q w, ∀ Y, Lax185574.TreeLocality.MentionsColor Y φ → Y ∈ C) :
    (atp G k q w).ncard ≤ 6 * (R + 1) * (C.ncard + 1) * (ℓ * ℓ) := by
  classical
  let B : Set (ℕ × ℕ × ℕ × ℕ × ℕ) := (↑(Finset.range 6) : Set ℕ) ×ˢ
    ((↑(Finset.range (R + 1)) : Set ℕ) ×ˢ ((insert 0 C) ×ˢ
      ((↑(Finset.range ℓ) : Set ℕ) ×ˢ (↑(Finset.range ℓ) : Set ℕ))))
  have hB : B.Finite := (Finset.finite_toSet _).prod ((Finset.finite_toSet _).prod
    ((hC.insert 0).prod ((Finset.finite_toSet _).prod (Finset.finite_toSet _))))
  have hRm := rhoMinus_le_rhoPlus k q
  have hmaps : ∀ φ ∈ atp G k q w, atomKey φ ∈ B := by
    rintro φ ⟨hat, hr, hs⟩
    have hc := hcol φ ⟨hat, hr, hs⟩
    cases φ with
    | eq i j => simp [B, atomKey]
    | edge i j => simp [B, atomKey]
    | nonEdge i j => simp [B, atomKey]
    | color Y i =>
      have := hc Y rfl
      simp [B, atomKey, this]
    | distLe r i j =>
      have := drank_distLe hr
      simp only [B, atomKey, Set.mem_prod, Finset.coe_range, Set.mem_Iio, Set.mem_insert_iff,
        true_or, i.isLt, j.isLt, and_true]
      omega
    | distColorLt r Y i =>
      have := drank_distColorLt hr
      have hY := hc Y rfl
      simp only [B, atomKey, Set.mem_prod, Finset.coe_range, Set.mem_Iio, Set.mem_insert_iff,
        hY, or_true, i.isLt, and_true]
      omega
    | not => exact absurd hat id
    | and => exact absurd hat id
    | exLocal => exact absurd hat id
  calc (atp G k q w).ncard ≤ B.ncard :=
        Set.ncard_le_ncard_of_injOn atomKey hmaps
          (atomKey_injOn.mono fun φ hφ => hφ.1) hB
    _ = 6 * ((R + 1) * ((insert 0 C).ncard * (ℓ * ℓ))) := by
        simp only [B, Set.ncard_prod, Set.ncard_coe_finset, Finset.card_range]
    _ ≤ 6 * ((R + 1) * ((C.ncard + 1) * (ℓ * ℓ))) := by
        gcongr
        exact Set.ncard_insert_le 0 C
    _ = 6 * (R + 1) * (C.ncard + 1) * (ℓ * ℓ) := by ring

/-! ### Part (ii): the size of a type tree -/

/-- The tuple `w` is reached from `w 0` by guarded extensions, as in
lem:locality: every entry after the first is within `ρ⁺(k+i, q−i)` of an
earlier entry. -/
def Guarded {V : Type*} (G : PartialGraph V) (k q j : ℕ) (w : Fin (j + 1) → V) : Prop :=
  ∀ i : Fin (j + 1), 0 < i.val → ∃ i' : Fin (j + 1), i'.val < i.val ∧
    WithinDist G.resolved (rhoPlus (k + i.val) (q - i.val)) (w i') (w i)

theorem guarded_snoc {V : Type*} {G : PartialGraph V} {k q j : ℕ} {w : Fin (j + 1) → V}
    (hw : Guarded G k q j w) (i : Fin (j + 1)) (b : V)
    (hb : WithinDist G.resolved (rhoPlus (k + (j + 1)) (q - (j + 1))) (w i) b) :
    Guarded G k q (j + 1) (Fin.snoc w b) := by
  intro t ht
  induction t using Fin.lastCases with
  | last =>
    refine ⟨i.castSucc, by simp; omega, ?_⟩
    simpa [Fin.snoc_last, Fin.snoc_castSucc] using hb
  | cast t =>
    obtain ⟨i', hi', hw'⟩ := hw t (by simpa using ht)
    refine ⟨i'.castSucc, by simpa using hi', ?_⟩
    simpa [Fin.snoc_castSucc] using hw'

theorem snoc_zero {V : Type*} {j : ℕ} (w : Fin (j + 1) → V) (b : V) :
    (Fin.snoc w b : Fin (j + 2) → V) 0 = w 0 := by
  rw [← Fin.castSucc_zero, Fin.snoc_castSucc]

theorem wordLength_prod {α β : Type*} [WordEncoding α] [WordEncoding β] (a : α) (b : β) :
    wordLength (a, b) = wordLength a + wordLength b :=
  List.length_append

/-- The recursive size bound for nodes of depth `m`: `A` bounds the atoms,
`L` the arity and `K` the number of type trees per rank and arity. -/
def sizeBound (A L K : ℕ) : ℕ → ℕ
  | 0 => A
  | m + 1 => A + (1 + (L * K) * (sizeBound A L K m + 2))

section Size

variable {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) (hk : 1 ≤ k) (v : Fin n)

include hk in
/-- The number of colors that meet the ball is at most the number of type
trees of single vertices of the ball, since a type tree records the color
of its vertex. -/
theorem ncard_colors_le :
    (G.color '' G.ball (rhoPlus k q) v).ncard ≤
      partialTypeCount G (rhoPlus k q + k + q) (rhoPlus k q + k + q) (G.ball (rhoPlus k q) v) := by
  classical
  set X := G.ball (rhoPlus k q) v
  have hT := treeCount_le G k q hk 0 1 (Nat.zero_le q) le_rfl (by omega) X
  simp only [Nat.add_zero, Nat.sub_zero] at hT
  refine le_trans ?_ hT
  have : Nonempty (Fin n) := ⟨v⟩
  have hrep : ∀ Y ∈ G.color '' X, ∃ u ∈ X, G.color u = Y := fun Y hY => hY
  choose! rep hrepX hrepc using hrep
  refine Set.ncard_le_ncard_of_injOn (fun Y => tree G k q ![rep Y]) ?_ ?_ ?_
  · intro Y hY
    exact ⟨![rep Y], fun j => by fin_cases j; exact hrepX Y hY, rfl⟩
  · intro Y hY Y' hY' h
    have h' := (Lax185574.TreeEquivalence.tree_eq_iff G k q hk ![rep Y] ![rep Y']).1 h
      (.color Y 0) (.color Y 0)
    simp only [Sat] at h'
    have := h'.1 (by simpa using hrepc Y hY)
    simp only [Matrix.cons_val_fin_one] at this
    rw [← hrepc Y' hY', this]
  · exact Set.Finite.subset (Set.finite_range fun u : Fin 1 → Fin n => tree G k q u)
      (by rintro τ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)

include hk in
/-- The number of nodes of rank `(k+i, q−i)` and arity `ℓ` of tuples from
the ball is at most `K`. -/
theorem ncard_nodes_le (i m ℓ : ℕ) (hi : i ≤ q) (hm : m = q - i) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k + i)
    (X : Set (Fin n)) :
    {μ : Node m ℓ | ∃ u : Fin ℓ → Fin n, (∀ t, u t ∈ X) ∧ μ = node G (k + i) m u}.ncard ≤
      partialTypeCount G (rhoPlus k q + k + q) (rhoPlus k q + k + q) X := by
  subst hm
  refine le_trans (le_of_eq ?_) (treeCount_le G k q hk i ℓ hi hℓ hℓk X)
  have hinj : Function.Injective fun μ : Node (q - i) ℓ => (⟨k + i, q - i, ℓ, μ⟩ : TypeTree) := by
    intro μ μ' h
    simp only [TypeTree.mk.injEq, heq_eq_eq, true_and] at h
    exact h
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext τ
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨μ, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩

/-- `K`: the number of types of quantifier rank `d` of `d`-tuples from the
ball of radius `ρ⁺(k, q)` around `v`, where `d = ρ⁺(k, q) + k + q`. -/
noncomputable def ballTypes : ℕ :=
  partialTypeCount G (rhoPlus k q + k + q) (rhoPlus k q + k + q) (G.ball (rhoPlus k q) v)

/-- The bound on the word length of the atoms of a node. -/
def atomBound (k q K : ℕ) : ℕ := 1 + (6 * (rhoPlus k q + 1) * (K + 1) * ((q + 1) * (q + 1))) * 6

include hk in
/-- The atoms of a node of `tree_{k,q}(v)` have word length at most
`atomBound`: they have bounded radii, and their colors meet the ball
around `v` by lem:locality. -/
theorem atoms_length_le (j m : ℕ) (hj : j + m = q) (w : Fin (j + 1) → Fin n) (hw0 : w 0 = v)
    (hw : Guarded G k q j w) :
    wordLength (finsetOf (atp G (k + j) m w)) ≤ atomBound k q (ballTypes G k q v) := by
  have hloc := Lax185574.TreeLocality.ball_of_guarded G k q j (by omega) w hw
  rw [hw0, show q - j = m by omega] at hloc
  refine le_trans (wordLength_finset_le _ 5
    (fun φ hφ => wordLength_atom_le φ (mem_of_mem_finsetOf hφ).1)) ?_
  rw [card_finsetOf]
  have hR : rhoPlus (k + j) m ≤ rhoPlus k q := by
    have := rhoPlus_shift_le k q j (by omega)
    rwa [show q - j = m by omega] at this
  have hA := ncard_atp_le G (k + j) m (j + 1) w (rhoPlus k q) hR
    (G.color '' G.ball (rhoPlus k q) v) (Set.toFinite _)
    (fun φ hφ Y hY => by
      obtain ⟨u, hu, hc⟩ := hloc.2 φ hφ Y hY
      exact ⟨u, hu, hc⟩)
  have hC := ncard_colors_le G k q hk v
  have hle : 6 * (rhoPlus k q + 1) * ((G.color '' G.ball (rhoPlus k q) v).ncard + 1) *
      ((j + 1) * (j + 1)) ≤ 6 * (rhoPlus k q + 1) * (ballTypes G k q v + 1) * ((q + 1) * (q + 1)) := by
    unfold ballTypes
    gcongr <;> omega
  have := Nat.mul_le_mul_right 6 (hA.trans hle)
  unfold atomBound
  omega

include hk in
/-- **Size of the nodes.** A node of depth `j` of `tree_{k,q}(v)`, reached
by a guarded tuple, has word length at most `sizeBound` of its height. It
has at most `atomBound` for its atoms, and at most `(q+1) K` extensions,
since the extended tuples lie in the ball around `v` by lem:locality and
there are at most `K` of their trees by part (i). -/
theorem node_length_le : ∀ m j, j + m = q → ∀ w : Fin (j + 1) → Fin n, w 0 = v →
    Guarded G k q j w →
    wordLength (node G (k + j) m w) ≤
      sizeBound (atomBound k q (ballTypes G k q v)) (q + 1) (ballTypes G k q v) m := by
  intro m
  induction m with
  | zero =>
    intro j hj w hw0 hw
    exact atoms_length_le G k q hk v j 0 hj w hw0 hw
  | succ m ih =>
    intro j hj w hw0 hw
    classical
    set K := ballTypes G k q v
    set X := G.ball (rhoPlus k q) v
    let E : Set (Fin (j + 1) × Node m (j + 1 + 1)) := {e | ∃ (i : Fin (j + 1)) (b : Fin n),
      WithinDist G.resolved (rhoPlus (k + j + 1) m) (w i) b ∧
        e = (i, node G (k + j + 1) m (Fin.snoc w b))}
    show wordLength ((finsetOf (atp G (k + j) (m + 1) w), finsetOf E) :
      Finset (DistFO (j + 1)) × Finset (Fin (j + 1) × Node m (j + 1 + 1))) ≤ _
    rw [wordLength_prod]
    have hatoms : wordLength (finsetOf (atp G (k + j) (m + 1) w)) ≤ atomBound k q K :=
      atoms_length_le G k q hk v j (m + 1) hj w hw0 hw
    -- the guard condition of an extension, in the form of `Guarded`
    have hguard : ∀ (i : Fin (j + 1)) (b : Fin n),
        WithinDist G.resolved (rhoPlus (k + j + 1) m) (w i) b →
        Guarded G k q (j + 1) (Fin.snoc w b) := by
      intro i b hb
      refine guarded_snoc hw i b ?_
      rwa [show q - (j + 1) = m by omega]
    -- each extension has word length at most `B + 1`
    have hext : ∀ e ∈ finsetOf E, wordLength e ≤ sizeBound (atomBound k q K) (q + 1) K m + 1 := by
      intro e he
      obtain ⟨i, b, hb, rfl⟩ := mem_of_mem_finsetOf he
      rw [wordLength_prod]
      have := ih (j + 1) (by omega) (Fin.snoc w b) (by rw [snoc_zero, hw0]) (hguard i b hb)
      have hi : wordLength i = 1 := rfl
      have : wordLength (node G (k + j + 1) m (Fin.snoc w b)) ≤
          sizeBound (atomBound k q K) (q + 1) K m := this
      omega
    -- there are at most `(j+1) K` extensions
    let Ch : Set (Node m (j + 1 + 1)) :=
      {μ | ∃ u : Fin (j + 1 + 1) → Fin n, (∀ t, u t ∈ X) ∧ μ = node G (k + (j + 1)) m u}
    have hCh : Ch.ncard ≤ K :=
      ncard_nodes_le G k q hk (j + 1) m (j + 1 + 1) (by omega) (by omega) (by omega) (by omega) X
    have hChfin : Ch.Finite :=
      Set.Finite.subset (Set.finite_range fun u : Fin (j + 1 + 1) → Fin n => node G (k + (j + 1)) m u)
        (by rintro μ ⟨u, -, rfl⟩; exact ⟨u, rfl⟩)
    have hEsub : E ⊆ (Set.univ : Set (Fin (j + 1))) ×ˢ Ch := by
      rintro e ⟨i, b, hb, rfl⟩
      refine ⟨Set.mem_univ _, Fin.snoc w b, fun t => ?_, rfl⟩
      have hloc := (Lax185574.TreeLocality.ball_of_guarded G k q (j + 1) (by omega) (Fin.snoc w b)
        (hguard i b hb)).1 t
      rwa [snoc_zero, hw0] at hloc
    have hEcard : (finsetOf E).card ≤ (j + 1) * K := by
      rw [card_finsetOf]
      calc E.ncard ≤ ((Set.univ : Set (Fin (j + 1))) ×ˢ Ch).ncard :=
            Set.ncard_le_ncard hEsub (Set.finite_univ.prod hChfin)
        _ = (j + 1) * Ch.ncard := by rw [Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card,
            Fintype.card_fin]
        _ ≤ (j + 1) * K := Nat.mul_le_mul_left _ hCh
    have hE := wordLength_finset_le (finsetOf E) _ hext
    have h1 : (finsetOf E).card * (sizeBound (atomBound k q K) (q + 1) K m + 1 + 1) ≤
        ((q + 1) * K) * (sizeBound (atomBound k q K) (q + 1) K m + 2) :=
      Nat.mul_le_mul (hEcard.trans (Nat.mul_le_mul_right _ (by omega))) le_rfl
    simp only [sizeBound]
    omega

/-- The closed-form coefficient of the size bound. -/
def sizeCoeff (A0 L : ℕ) : ℕ → ℕ
  | 0 => A0
  | m + 1 => A0 + 1 + L * (sizeCoeff A0 L m + 2)

theorem sizeBound_le (A A0 L K : ℕ) (hA : A ≤ A0 * (K + 1)) :
    ∀ m, sizeBound A L K m ≤ sizeCoeff A0 L m * (K + 1) ^ (m + 1)
  | 0 => by simpa [sizeBound, sizeCoeff] using hA
  | m + 1 => by
    have ih := sizeBound_le A A0 L K hA m
    set P := (K + 1) ^ (m + 1)
    have hP : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos K)
    have e : (K + 1) ^ (m + 1 + 1) = (K + 1) * P := by rw [pow_succ]; ring
    rw [e]
    simp only [sizeBound, sizeCoeff]
    have h1 : A ≤ A0 * (K + 1) * P := hA.trans (Nat.le_mul_of_pos_right _ hP)
    have h2 : 1 ≤ (K + 1) * P := Nat.mul_pos (Nat.succ_pos K) hP
    have h3 : L * K * (sizeBound A L K m + 2) ≤ L * (K + 1) * (sizeCoeff A0 L m * P + 2 * P) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_succ K)) (by omega)
    calc A + (1 + L * K * (sizeBound A L K m + 2))
        ≤ A0 * (K + 1) * P + ((K + 1) * P + L * (K + 1) * (sizeCoeff A0 L m * P + 2 * P)) := by
          omega
      _ = (A0 + 1 + L * (sizeCoeff A0 L m + 2)) * ((K + 1) * P) := by ring

end Size

/--
---
conclusion: Lax185574.TypeTreeSizes.tree_length_le
---
Put `K = |Types_{d,d}(Ball_r(v))|`. By the locality lemma, every node of
`tree_{k,q}(v)` is the tree of a tuple from the ball, and every color in
a true atom of its root meets the ball. There are at most `K` such
colors and at most `K` trees per rank and arity by part (i). So every
root has `O_{k,q}(K)` atoms, every node has at most `(q+1) K` children,
and the depth is `q`. This gives the bound `(3 + D) (K+1)^(q+1)`, where
`D` depends on `k` and `q` only.
-/
theorem tree_length_le (k q : ℕ) (hk : 1 ≤ k) :
    ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (v : Fin n),
      wordLength (tree G k q ![v]) ≤
        c * (partialTypeCount G (rhoPlus k q + k + q) (rhoPlus k q + k + q)
          (G.ball (rhoPlus k q) v) + 1) ^ a := by
  let A0 := 1 + 36 * (rhoPlus k q + 1) * ((q + 1) * (q + 1))
  refine ⟨3 + sizeCoeff A0 (q + 1) q, q + 1, fun n G v => ?_⟩
  set K := ballTypes G k q v
  have hnode := node_length_le G k q hk v q 0 (by omega) ![v] rfl
    (fun i hi => absurd hi (by omega)) 
  have hA : atomBound k q K ≤ A0 * (K + 1) := by
    unfold atomBound
    have e : A0 * (K + 1) = (K + 1) + 6 * (rhoPlus k q + 1) * (K + 1) * ((q + 1) * (q + 1)) * 6 := by
      simp only [A0]
      ring
    omega
  have hB := sizeBound_le _ A0 (q + 1) K hA q
  have hlen : wordLength (tree G k q ![v]) = 3 + wordLength (node G k q ![v]) := by
    show (toWord (k, q, 1) ++ toWord (node G k q ![v])).length = _
    rw [List.length_append]
    rfl
  have hP : 1 ≤ (K + 1) ^ (q + 1) := Nat.one_le_pow _ _ (Nat.succ_pos K)
  show wordLength (tree G k q ![v]) ≤ (3 + sizeCoeff A0 (q + 1) q) * (K + 1) ^ (q + 1)
  rw [hlen]
  have : wordLength (node G k q ![v]) ≤ sizeCoeff A0 (q + 1) q * (K + 1) ^ (q + 1) :=
    hnode.trans hB
  nlinarith

end Lax185574Proofs.TypeTreeSizes
