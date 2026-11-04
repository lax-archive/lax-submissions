import Lax185574.Flips
import Lax185574Proofs.FlipBasics
import Mathlib

/-!
Basic notions for the chain theorem of the companion paper (Dreier,
Mählmann, Pilipczuk, Toruńczyk, *Monadically dependent graph classes have
almost bounded merge-width*): the closed symmetric difference `Δ[u,v]`,
completeness and crossing, the partitions `𝒯_{k+1}(G,A)` into
`(k+1)`-types as decidable relations, counting the classes that meet a
set, and growth ratios.

The relation `tpRel G A k` is the partition into `(k+1)`-types of the
companion paper, so `tpRel G A 0` is the partition into atomic types.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

section Basic

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed symmetric difference `Δ[u,v] = (N(u) △ N(v)) ∪ {u,v}`
for `u ≠ v`, and `Δ[v,v] = ∅`. -/
def sdiff (u v : V) : Finset V :=
  if u = v then ∅ else insert u (insert v (univ.filter fun x => ¬ (G.Adj u x ↔ G.Adj v x)))

/-- `u` is complete to `Q ∖ {u}`. -/
def IsComplete (u : V) (Q : Finset V) : Prop := ∀ z ∈ Q, z ≠ u → G.Adj u z

/-- `u` is anticomplete to `Q ∖ {u}`. -/
def IsAnticomplete (u : V) (Q : Finset V) : Prop := ∀ z ∈ Q, z ≠ u → ¬ G.Adj u z

instance (u : V) (Q : Finset V) : Decidable (IsComplete G u Q) := by
  unfold IsComplete; infer_instance

instance (u : V) (Q : Finset V) : Decidable (IsAnticomplete G u Q) := by
  unfold IsAnticomplete; infer_instance

/-- `u` crosses `Q`: `u ∉ Q` and `u` is neither complete nor anticomplete
to `Q`. -/
def Crosses (u : V) (Q : Finset V) : Prop :=
  u ∉ Q ∧ ¬ IsComplete G u Q ∧ ¬ IsAnticomplete G u Q

instance (u : V) (Q : Finset V) : Decidable (Crosses G u Q) := by
  unfold Crosses; infer_instance

theorem mem_sdiff {u v x : V} :
    x ∈ sdiff G u v ↔ u ≠ v ∧ (x = u ∨ x = v ∨ ¬ (G.Adj u x ↔ G.Adj v x)) := by
  unfold sdiff
  split_ifs with h
  · simp [h]
  · simp [h]

@[simp] theorem sdiff_self (v : V) : sdiff G v v = ∅ := by simp [sdiff]

theorem sdiff_comm (u v : V) : sdiff G u v = sdiff G v u := by
  ext x; simp only [mem_sdiff]; constructor <;> rintro ⟨h, h'⟩ <;>
    exact ⟨Ne.symm h, by tauto⟩

theorem sdiff_triangle (u v w : V) : sdiff G u w ⊆ sdiff G u v ∪ sdiff G v w := by
  intro x hx
  rw [mem_sdiff] at hx
  obtain ⟨huw, hx⟩ := hx
  rw [mem_union, mem_sdiff, mem_sdiff]
  by_cases huv : u = v
  · subst huv; exact Or.inr ⟨huw, hx⟩
  by_cases hvw : v = w
  · subst hvw; exact Or.inl ⟨huv, hx⟩
  rcases hx with rfl | rfl | hx
  · exact Or.inl ⟨huv, Or.inl rfl⟩
  · exact Or.inr ⟨hvw, Or.inr (Or.inl rfl)⟩
  · by_cases h : G.Adj u x ↔ G.Adj v x
    · exact Or.inr ⟨hvw, Or.inr (Or.inr fun h' => hx (h.trans h'))⟩
    · exact Or.inl ⟨huv, Or.inr (Or.inr h)⟩

theorem self_mem_sdiff {u v : V} (h : u ≠ v) : u ∈ sdiff G u v :=
  (mem_sdiff G).2 ⟨h, Or.inl rfl⟩

/-- A vertex outside `{u, v}` lies in `Δ[u,v]` exactly when it is
adjacent to exactly one of them. -/
theorem mem_sdiff_of_ne {u v x : V} (huv : u ≠ v) (hu : x ≠ u) (hv : x ≠ v) :
    x ∈ sdiff G u v ↔ ¬ (G.Adj u x ↔ G.Adj v x) := by
  rw [mem_sdiff]; simp [huv, hu, hv]

end Basic

/-! ### Counting classes -/

section Count

/-- The class of `x` under a relation given as a Boolean function. -/
def cls (P : V → V → Bool) (x : V) : Finset V := univ.filter fun z => P x z

/-- The number of classes of `P` that meet `X`. -/
def numCls (P : V → V → Bool) (X : Finset V) : ℕ := (X.image (cls P)).card

/-- A Boolean relation that is an equivalence relation. -/
structure IsEquiv (P : V → V → Bool) : Prop where
  refl : ∀ x, P x x
  symm : ∀ x y, P x y → P y x
  trans : ∀ x y z, P x y → P y z → P x z

theorem mem_cls {P : V → V → Bool} {x z : V} : z ∈ cls P x ↔ P x z := by simp [cls]

theorem cls_eq_iff {P : V → V → Bool} (hP : IsEquiv P) {x y : V} :
    cls P x = cls P y ↔ P x y := by
  constructor
  · intro h
    have : y ∈ cls P x := h ▸ mem_cls.2 (hP.refl y)
    exact mem_cls.1 this
  · intro h; ext z; simp only [mem_cls]
    exact ⟨fun h' => hP.trans _ _ _ (hP.symm _ _ h) h', fun h' => hP.trans _ _ _ h h'⟩

theorem numCls_mono (P : V → V → Bool) {X Y : Finset V} (h : X ⊆ Y) :
    numCls P X ≤ numCls P Y :=
  card_le_card (image_subset_image h)

theorem numCls_union_le (P : V → V → Bool) (X Y : Finset V) :
    numCls P (X ∪ Y) ≤ numCls P X + numCls P Y := by
  unfold numCls; rw [image_union]; exact card_union_le _ _

theorem numCls_le_card (P : V → V → Bool) (X : Finset V) : numCls P X ≤ X.card :=
  card_image_le

/-- If `P'`-equivalence implies `P`-equivalence on `X`, then `X` meets at
most as many classes of `P` as of `P'`. -/
theorem numCls_le_of_le {P P' : V → V → Bool} (hP : IsEquiv P) (hP' : IsEquiv P')
    {X : Finset V} (h : ∀ x ∈ X, ∀ y ∈ X, P' x y → P x y) : numCls P X ≤ numCls P' X := by
  unfold numCls
  have : X.image (cls P) = (X.image (cls P')).image
      (fun c => if hc : ∃ x ∈ X, cls P' x = c then cls P hc.choose else ∅) := by
    ext c
    simp only [mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨cls P' x, ⟨x, hx, rfl⟩, ?_⟩
      have hc : ∃ y ∈ X, cls P' y = cls P' x := ⟨x, hx, rfl⟩
      rw [dif_pos hc]
      have := hc.choose_spec.2
      rw [cls_eq_iff hP'] at this
      exact (cls_eq_iff hP).2 (h _ hc.choose_spec.1 _ hx this)
    · rintro ⟨c', ⟨x, hx, rfl⟩, rfl⟩
      have hc : ∃ y ∈ X, cls P' y = cls P' x := ⟨x, hx, rfl⟩
      rw [dif_pos hc]
      exact ⟨_, hc.choose_spec.1, rfl⟩
  rw [this]; exact card_image_le

theorem numCls_insert_of_rel {P : V → V → Bool} (hP : IsEquiv P) {a : V} {X : Finset V}
    {x : V} (hx : x ∈ X) (h : P a x) : numCls P (insert a X) = numCls P X := by
  unfold numCls
  rw [image_insert, insert_eq_of_mem]
  exact mem_image.2 ⟨x, hx, ((cls_eq_iff hP).2 h).symm⟩

theorem numCls_insert_of_not_rel {P : V → V → Bool} (hP : IsEquiv P) {a : V} {X : Finset V}
    (h : ∀ x ∈ X, ¬ P a x) : numCls P (insert a X) = numCls P X + 1 := by
  unfold numCls
  rw [image_insert, card_insert_of_notMem]
  rintro hmem
  obtain ⟨x, hx, hxa⟩ := mem_image.1 hmem
  exact h x hx ((cls_eq_iff hP).1 hxa.symm)

/-- The classes meeting `X` are those of the elements of `X`. -/
theorem numCls_eq_card_of_injOn {P : V → V → Bool} (hP : IsEquiv P) {X : Finset V}
    (h : ∀ x ∈ X, ∀ y ∈ X, P x y → x = y) : numCls P X = X.card := by
  unfold numCls
  refine card_image_of_injOn fun x hx y hy hxy => h x hx y hy ?_
  exact (cls_eq_iff hP).1 hxy

/-- If `X` meets at most `k` classes, then so does every subset. And a
set of pairwise inequivalent elements of `X` has at most `numCls P X`
elements. -/
theorem card_le_numCls_of_pairwise {P : V → V → Bool} (hP : IsEquiv P) {X Y : Finset V}
    (hYX : Y ⊆ X) (h : ∀ x ∈ Y, ∀ y ∈ Y, P x y → x = y) : Y.card ≤ numCls P X := by
  rw [← numCls_eq_card_of_injOn hP h]; exact numCls_mono P hYX

/-- The bridge between `numCls` and `Partitions.partCount`. -/
theorem partCount_eq_numCls (S : Setoid V) (P : V → V → Bool) (hSP : ∀ x y, S x y ↔ P x y)
    (X : Finset V) : Lax185574.Partitions.partCount S (X : Set V) = numCls P X := by
  classical
  have hP : IsEquiv P := ⟨fun x => (hSP x x).1 (S.refl x),
    fun x y h => (hSP y x).1 (S.symm ((hSP x y).2 h)),
    fun x y z h h' => (hSP x z).1 (S.trans ((hSP x y).2 h) ((hSP y z).2 h'))⟩
  unfold Lax185574.Partitions.partCount numCls
  rw [show (Quotient.mk S '' (X : Set V)) = ((X.image (Quotient.mk S) : Finset _) : Set _) by
    simp, Set.ncard_coe_finset]
  let f : Quotient S → Finset V := fun q => univ.filter fun z => Quotient.mk S z = q
  have hf : Function.Injective f := by
    intro a b hab
    induction a using Quotient.inductionOn
    rename_i a
    have : a ∈ f (Quotient.mk S a) := by simp [f]
    rw [hab] at this; simpa [f] using this
  have : X.image (cls P) = (X.image (Quotient.mk S)).image f := by
    rw [image_image]
    refine image_congr fun x _ => ?_
    ext z; simp only [mem_cls, f, Function.comp, mem_filter, mem_univ, true_and,
      Quotient.eq]
    exact ⟨fun h => S.symm ((hSP x z).2 h), fun h => (hSP x z).1 (S.symm h)⟩
  rw [this, card_image_of_injective _ hf]

end Count

/-! ### Types -/

section Types

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `tpRel G A k u v`: `u` and `v` have the same `(k+1)`-type over `A`.
For `k = 0` these are the atomic types. A vertex `u` and `v` have the
same `(k+2)`-type if they have the same `(k+1)`-type and agree on being
complete, and on being anticomplete, to `Q ∖ {·}` for every class `Q` of
`(k+1)`-types. -/
def tpRel (A : Finset V) : ℕ → V → V → Bool
  | 0, u, v => decide (u = v ∨ (u ∉ A ∧ v ∉ A ∧ ∀ y ∈ A, (G.Adj u y ↔ G.Adj v y)))
  | k + 1, u, v => tpRel A k u v &&
      decide (∀ y : V,
        (IsComplete G u (univ.filter fun z => tpRel A k y z) ↔
          IsComplete G v (univ.filter fun z => tpRel A k y z)) ∧
        (IsAnticomplete G u (univ.filter fun z => tpRel A k y z) ↔
          IsAnticomplete G v (univ.filter fun z => tpRel A k y z)))

variable {G}

theorem tpRel_zero {A : Finset V} {u v : V} :
    tpRel G A 0 u v ↔ (u = v ∨ (u ∉ A ∧ v ∉ A ∧ ∀ y ∈ A, (G.Adj u y ↔ G.Adj v y))) := by
  simp [tpRel]

theorem tpRel_succ {A : Finset V} {k : ℕ} {u v : V} :
    tpRel G A (k + 1) u v ↔ tpRel G A k u v ∧ ∀ y : V,
      (IsComplete G u (cls (tpRel G A k) y) ↔ IsComplete G v (cls (tpRel G A k) y)) ∧
      (IsAnticomplete G u (cls (tpRel G A k) y) ↔ IsAnticomplete G v (cls (tpRel G A k) y)) := by
  simp [tpRel, cls]

theorem tpRel_isEquiv (A : Finset V) (k : ℕ) : IsEquiv (tpRel G A k) := by
  induction k with
  | zero =>
    refine ⟨fun x => tpRel_zero.2 (Or.inl rfl), fun x y h => ?_, fun x y z h h' => ?_⟩
    · rw [tpRel_zero] at h ⊢
      rcases h with rfl | ⟨hx, hy, h⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx, fun a ha => (h a ha).symm⟩
    · rw [tpRel_zero] at h h' ⊢
      rcases h with rfl | ⟨hx, hy, h⟩
      · exact h'
      rcases h' with rfl | ⟨_, hz, h'⟩
      · exact Or.inr ⟨hx, hy, h⟩
      · exact Or.inr ⟨hx, hz, fun a ha => (h a ha).trans (h' a ha)⟩
  | succ k ih =>
    refine ⟨fun x => tpRel_succ.2 ⟨ih.refl x, fun _ => ⟨Iff.rfl, Iff.rfl⟩⟩,
      fun x y h => ?_, fun x y z h h' => ?_⟩
    · rw [tpRel_succ] at h ⊢
      exact ⟨ih.symm _ _ h.1, fun a => ⟨(h.2 a).1.symm, (h.2 a).2.symm⟩⟩
    · rw [tpRel_succ] at h h' ⊢
      exact ⟨ih.trans _ _ _ h.1 h'.1,
        fun a => ⟨(h.2 a).1.trans (h'.2 a).1, (h.2 a).2.trans (h'.2 a).2⟩⟩

theorem tpRel_of_succ {A : Finset V} {k : ℕ} {u v : V} (h : tpRel G A (k + 1) u v) :
    tpRel G A k u v := (tpRel_succ.1 h).1

theorem tpRel_of_le {A : Finset V} {j k : ℕ} (hjk : j ≤ k) {u v : V} (h : tpRel G A k u v) :
    tpRel G A j u v := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact h
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · exact ih (by omega) (tpRel_of_succ h)
    · obtain rfl : j = k + 1 := by omega
      exact h

/-- The types are respectful: they refine the atomic types. -/
theorem tpRel_zero_of {A : Finset V} {k : ℕ} {u v : V} (h : tpRel G A k u v) :
    tpRel G A 0 u v := tpRel_of_le (Nat.zero_le k) h

/-- Completeness to a union of classes is completeness to each class. -/
private theorem isComplete_iff_forall_cls {P P' : V → V → Bool} (hP : IsEquiv P)
    (hP' : IsEquiv P') (hle : ∀ x y, P' x y → P x y) (u y : V) :
    IsComplete G u (cls P y) ↔ ∀ z ∈ cls P y, IsComplete G u (cls P' z) := by
  constructor
  · intro h z hz w hw hwu
    refine h w ?_ hwu
    rw [mem_cls] at hz hw ⊢
    exact hP.trans _ _ _ hz (hle _ _ hw)
  · intro h w hw hwu
    exact h w hw w (mem_cls.2 (hP'.refl w)) hwu

private theorem isAnticomplete_iff_forall_cls {P P' : V → V → Bool} (hP : IsEquiv P)
    (hP' : IsEquiv P') (hle : ∀ x y, P' x y → P x y) (u y : V) :
    IsAnticomplete G u (cls P y) ↔ ∀ z ∈ cls P y, IsAnticomplete G u (cls P' z) := by
  constructor
  · intro h z hz w hw hwu
    refine h w ?_ hwu
    rw [mem_cls] at hz hw ⊢
    exact hP.trans _ _ _ hz (hle _ _ hw)
  · intro h w hw hwu
    exact h w hw w (mem_cls.2 (hP'.refl w)) hwu

/-- The types are monotone: a larger parameter set gives a finer
partition. -/
theorem tpRel_anti {A B : Finset V} (hAB : A ⊆ B) (k : ℕ) {u v : V}
    (h : tpRel G B k u v) : tpRel G A k u v := by
  induction k generalizing u v with
  | zero =>
    rw [tpRel_zero] at h ⊢
    rcases h with h | ⟨hu, hv, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨fun h' => hu (hAB h'), fun h' => hv (hAB h'), fun y hy => h y (hAB hy)⟩
  | succ k ih =>
    rw [tpRel_succ] at h ⊢
    refine ⟨ih h.1, fun y => ?_⟩
    have hle : ∀ x y, tpRel G B k x y → tpRel G A k x y := fun x y => ih
    rw [isComplete_iff_forall_cls (tpRel_isEquiv A k) (tpRel_isEquiv B k) hle,
      isComplete_iff_forall_cls (tpRel_isEquiv A k) (tpRel_isEquiv B k) hle,
      isAnticomplete_iff_forall_cls (tpRel_isEquiv A k) (tpRel_isEquiv B k) hle,
      isAnticomplete_iff_forall_cls (tpRel_isEquiv A k) (tpRel_isEquiv B k) hle]
    exact ⟨forall₂_congr fun z _ => (h.2 z).1, forall₂_congr fun z _ => (h.2 z).2⟩

/-- The atomic types are the `1`-types. -/
theorem atomicTypes_iff_tpRel (A : Finset V) (u v : V) :
    Lax185574.Partitions.atomicTypes G (A : Set V) u v ↔ tpRel G A 0 u v := by
  rw [Lax185574Proofs.FlipBasics.atomicTypes_rel_iff', tpRel_zero]
  simp

/-- The setoid of `(k+1)`-types. -/
def tpSetoid (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) : Setoid V where
  r u v := tpRel G A k u v
  iseqv := ⟨(tpRel_isEquiv A k).refl, fun h => (tpRel_isEquiv A k).symm _ _ h,
    fun h h' => (tpRel_isEquiv A k).trans _ _ _ h h'⟩

theorem atomicTypes_eq_tpSetoid (A : Finset V) :
    Lax185574.Partitions.atomicTypes G (A : Set V) = tpSetoid G A 0 := by
  ext u v; exact atomicTypes_iff_tpRel A u v

/-- A vertex of `A` is alone in its type. -/
theorem eq_of_tpRel_of_mem {A : Finset V} {k : ℕ} {u v : V} (h : tpRel G A k u v)
    (hu : u ∈ A) : u = v := by
  have := tpRel_zero.1 (tpRel_zero_of h)
  rcases this with h | ⟨hu', _, _⟩
  · exact h
  · exact absurd hu hu'

/-- Two vertices outside `A` with the same atomic type have the same
adjacency to every vertex of `A`. -/
theorem adj_iff_of_tpRel {A : Finset V} {k : ℕ} {u v y : V} (h : tpRel G A k u v)
    (hy : y ∈ A) : G.Adj u y ↔ G.Adj v y := by
  rcases tpRel_zero.1 (tpRel_zero_of h) with rfl | ⟨_, _, h⟩
  · exact Iff.rfl
  · exact h y hy

/-! ### Growth ratio -/

/-- The growth ratio of the selector `T` on the vertex type: the least
`γ` with `numCls (T A) univ ≤ γ · |A|` for every nonempty `A`. -/
def growth (T : Finset V → V → V → Bool) : ℕ :=
  (univ.powerset.filter (·.Nonempty)).sup fun A => (numCls (T A) univ + A.card - 1) / A.card

theorem numCls_le_growth_mul (T : Finset V → V → V → Bool) {A : Finset V}
    (hA : A.Nonempty) : numCls (T A) univ ≤ growth T * A.card := by
  have hle : (numCls (T A) univ + A.card - 1) / A.card ≤ growth T :=
    le_sup (f := fun A : Finset V => (numCls (T A) univ + A.card - 1) / A.card)
      (mem_filter.2 ⟨mem_powerset.2 (subset_univ _), hA⟩)
  have hpos : 0 < A.card := card_pos.2 hA
  have h1 := Nat.div_add_mod (numCls (T A) univ + A.card - 1) A.card
  have h2 := Nat.mod_lt (numCls (T A) univ + A.card - 1) hpos
  have h3 : A.card * ((numCls (T A) univ + A.card - 1) / A.card) ≤ A.card * growth T :=
    Nat.mul_le_mul_left _ hle
  rw [Nat.mul_comm (growth T)]
  omega

theorem growth_le {T : Finset V → V → V → Bool} {g : ℕ}
    (h : ∀ A : Finset V, A.Nonempty → numCls (T A) univ ≤ g * A.card) : growth T ≤ g := by
  refine Finset.sup_le fun A hA => ?_
  have hA := (mem_filter.1 hA).2
  have hpos : 0 < A.card := card_pos.2 hA
  rw [Nat.div_le_iff_le_mul_add_pred hpos]
  have := h A hA
  rw [Nat.mul_comm] at this
  omega

theorem growth_le_card (T : Finset V → V → V → Bool) : growth T ≤ Fintype.card V := by
  refine growth_le fun A hA => ?_
  calc numCls (T A) univ ≤ (univ : Finset V).card := numCls_le_card _ _
    _ = Fintype.card V * 1 := by simp
    _ ≤ Fintype.card V * A.card := Nat.mul_le_mul_left _ (card_pos.2 hA)

end Types

end Lax185574Proofs.Chain
