import Lax185574Proofs.Chain.Types
import Lax185574Proofs.WalkDistance

/-!
From the predamping set to a flip (Sections `sec:flip` and `sec:damping`
of the companion paper).

* `exists_mismatch_asymmetric` (`lem:mismatch-asymmetric`): from (A2) and
  (A3), a relation `ρ` on the atomic types over `S` whose mismatch is at
  most `M₂ + M₃`. Here `ρ(Q, Q')` holds when the chosen vertex `s_Q ∈ S`
  is adjacent to `Q'`.
* `exists_symmetric` (`lem:symmetrization`): a symmetric relation with
  three times the mismatch, by majority over pairs of representatives.
* `numCls_ball_le` (`lem:mismatch-ball`): in a flip whose neighborhoods
  meet at most `m` classes of `(r+1)`-types, a radius-`r` ball meets at
  most `(m+1)^r` atomic types.

A relation on the parts of a partition `Q` is a relation `ρ` on vertices
that is invariant under `Q`. Its mismatch with respect to `R` bounds, for
every vertex `v`, the number of classes of `R` met by
`{y | ¬ (G.Adj v y ↔ ρ v y)} = N(v) △ N_ρ(Q(v))`.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset Classical

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `N(v) △ N_ρ(v)` for a relation `ρ`. -/
noncomputable def misSet (G : SimpleGraph V) (ρ : V → V → Prop) (v : V) : Finset V :=
  univ.filter fun y => ¬ (G.Adj v y ↔ ρ v y)

/-- `ρ` is invariant under the equivalence `Q`. -/
def IsInvariant (Q : V → V → Bool) (ρ : V → V → Prop) : Prop :=
  ∀ v v' y y', Q v v' → Q y y' → (ρ v y ↔ ρ v' y')

/-! ### Representatives of a partition -/

/-- `Rp` contains exactly one vertex of every class of `R`. -/
structure IsRepSet (R : V → V → Bool) (Rp : Finset V) : Prop where
  ex : ∀ x, ∃ r ∈ Rp, R r x
  uniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, R r r' → r = r'

theorem numCls_le_reps {R : V → V → Bool} (hR : IsEquiv R) {Rp : Finset V}
    (hRp : IsRepSet R Rp) (X : Finset V) :
    numCls R X ≤ (Rp.filter fun r => ∃ x ∈ X, R r x).card := by
  unfold numCls
  choose f hf hfx using hRp.ex
  calc (X.image (cls R)).card = ((X.image f).image (cls R)).card := by
        rw [image_image]; congr 1
        refine image_congr fun x _ => ?_
        exact ((cls_eq_iff hR).2 (hfx x)).symm
    _ ≤ (X.image f).card := card_image_le
    _ ≤ _ := card_le_card fun r hr => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
        exact mem_filter.2 ⟨hf x, x, hx, hfx x⟩

/-! ### Mismatch and balls -/

section Ball

/-- A walk of length at most `j + 1` ends next to the end of a walk of
length at most `j`. -/
theorem withinDist_succ {H : SimpleGraph V} {j : ℕ} {u y : V}
    (h : Lax185574.GaifmanGraph.WithinDist H (j + 1) u y) :
    ∃ x, Lax185574.GaifmanGraph.WithinDist H j u x ∧ (x = y ∨ H.Adj x y) := by
  obtain ⟨p, hp⟩ := h
  by_cases hpj : p.length ≤ j
  · exact ⟨y, ⟨p, hpj⟩, Or.inl rfl⟩
  · cases hq : p.reverse with
    | nil =>
      have := congrArg SimpleGraph.Walk.length hq
      rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_nil] at this
      omega
    | cons hadj q =>
      rename_i x
      have hlen : q.length + 1 = p.length := by
        have := congrArg SimpleGraph.Walk.length hq
        simp at this; omega
      exact ⟨x, ⟨q.reverse, by simp; omega⟩, Or.inr hadj.symm⟩

/-- The closed `H`-neighborhood of a set. -/
noncomputable def closedNbhd (H : SimpleGraph V) (X : Finset V) : Finset V :=
  univ.filter fun y => ∃ x ∈ X, x = y ∨ H.Adj x y

/-- The `H`-ball of radius `j`. -/
noncomputable def ballF (H : SimpleGraph V) (j : ℕ) (u : V) : Finset V :=
  univ.filter fun y => Lax185574.GaifmanGraph.WithinDist H j u y

theorem numCls_biUnion_le_sum (P : V → V → Bool) {ι : Type*} (I : Finset ι)
    (F : ι → Finset V) : numCls P (I.biUnion F) ≤ ∑ i ∈ I, numCls P (F i) := by
  unfold numCls
  rw [biUnion_image]
  exact card_biUnion_le

variable {B : Finset V} {r m : ℕ} {H : SimpleGraph V}

/-- `cl:telescope`: the closed `H`-neighborhood of an `(i+2)`-type meets at
most `m + 1` classes of `(i+1)`-types. -/
theorem numCls_closedNbhd_le (hflip : Lax185574.Flips.IsFlip G (tpSetoid G B 0) H)
    (hmis : ∀ x, numCls (tpRel G B r) (univ.filter (H.Adj x)) ≤ m) {i : ℕ} (hi : i < r)
    (x0 : V) : numCls (tpRel G B i) (closedNbhd H (cls (tpRel G B (i + 1)) x0)) ≤ m + 1 := by
  have hEi := tpRel_isEquiv (G := G) B i
  have hEr := tpRel_isEquiv (G := G) B r
  -- every other class meeting the neighborhood contains an `H`-neighbor of `x0`
  have key : ∀ c ∈ (closedNbhd H (cls (tpRel G B (i + 1)) x0)).image (cls (tpRel G B i)),
      c ≠ cls (tpRel G B i) x0 → ∃ y, c = cls (tpRel G B i) y ∧ H.Adj x0 y := by
    intro c hc hne
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    obtain ⟨x, hx, hxy⟩ := (mem_filter.1 hy).2
    have hxx0 : tpRel G B (i + 1) x0 x := mem_cls.1 hx
    have hxx0i : tpRel G B i x0 x := tpRel_of_le (by omega) hxx0
    rcases hxy with rfl | hxy
    · exact absurd ((cls_eq_iff hEi).2 ((hEi.symm _ _ hxx0i))) hne
    have hy0 : ¬ tpRel G B i x0 y := fun h => hne ((cls_eq_iff hEi).2 (hEi.symm _ _ h))
    have hRx0 : x0 ∉ cls (tpRel G B i) y := fun h => hy0 (hEi.symm _ _ (mem_cls.1 h))
    have hRx : x ∉ cls (tpRel G B i) y := fun h =>
      hy0 (hEi.trans _ _ _ hxx0i (hEi.symm _ _ (mem_cls.1 h)))
    have hsucc := (tpRel_succ.1 hxx0).2 y
    -- the flip between the atomic types of `x0` and `y`
    have hx0y : x0 ≠ y := fun h => hy0 (h ▸ hEi.refl _)
    have hT1 : ∀ z, tpRel G B i y z → tpRel G B 0 y z := fun z h => tpRel_zero_of h
    rcases hflip x0 y with hf | hf
    · -- adjacency is kept between the two atomic types
      by_cases hc : IsComplete G x0 (cls (tpRel G B i) y)
      · refine ⟨y, rfl, ?_⟩
        have : G.Adj x0 y := hc y (mem_cls.2 (hEi.refl y)) (Ne.symm hx0y)
        exact (hf x0 y ((tpRel_isEquiv B 0).refl x0) ((tpRel_isEquiv B 0).refl y) hx0y).2 this
      by_cases ha : IsAnticomplete G x0 (cls (tpRel G B i) y)
      · exfalso
        have hax : IsAnticomplete G x (cls (tpRel G B i) y) := hsucc.2.1 ha
        have hxy' : x ≠ y := fun h => hRx (by rw [h]; exact mem_cls.2 (hEi.refl y))
        have := (hf x y (tpRel_zero_of (hEi.symm _ _ hxx0i) |> fun h => by
          exact (tpRel_isEquiv B 0).symm _ _ (tpRel_zero_of hxx0i)) ((tpRel_isEquiv B 0).refl y)
          hxy').1 hxy
        exact hax y (mem_cls.2 (hEi.refl y)) (Ne.symm hxy') this
      · simp only [IsComplete, not_forall] at hc
        obtain ⟨z, hz, hzx0, hadj⟩ := hc
        simp only [IsAnticomplete, not_forall, not_not] at ha
        obtain ⟨z', hz', hz'x0, hadj'⟩ := ha
        refine ⟨z', (cls_eq_iff hEi).2 (mem_cls.1 hz'), ?_⟩
        exact (hf x0 z' ((tpRel_isEquiv B 0).refl x0) (tpRel_zero_of (hEi.symm _ _ (mem_cls.1 hz')))
          (Ne.symm hz'x0)).2 hadj'
    · -- adjacency is complemented between the two atomic types
      by_cases ha : IsAnticomplete G x0 (cls (tpRel G B i) y)
      · refine ⟨y, rfl, ?_⟩
        have : ¬ G.Adj x0 y := ha y (mem_cls.2 (hEi.refl y)) (Ne.symm hx0y)
        exact (hf x0 y ((tpRel_isEquiv B 0).refl x0) ((tpRel_isEquiv B 0).refl y) hx0y).2 this
      by_cases hc : IsComplete G x0 (cls (tpRel G B i) y)
      · exfalso
        have hcx : IsComplete G x (cls (tpRel G B i) y) := hsucc.1.1 hc
        have hxy' : x ≠ y := fun h => hRx (by rw [h]; exact mem_cls.2 (hEi.refl y))
        have := (hf x y ((tpRel_isEquiv B 0).symm _ _ (tpRel_zero_of hxx0i))
          ((tpRel_isEquiv B 0).refl y) hxy').1 hxy
        exact this (hcx y (mem_cls.2 (hEi.refl y)) (Ne.symm hxy'))
      · simp only [IsComplete, not_forall] at hc
        obtain ⟨z, hz, hzx0, hadj⟩ := hc
        refine ⟨z, (cls_eq_iff hEi).2 (mem_cls.1 hz), ?_⟩
        exact (hf x0 z ((tpRel_isEquiv B 0).refl x0) (tpRel_zero_of (hEi.symm _ _ (mem_cls.1 hz)))
          (Ne.symm hzx0)).2 hadj
  -- count: the class of `x0` and the classes of `H`-neighbors of `x0`
  unfold numCls
  set T := (closedNbhd H (cls (tpRel G B (i + 1)) x0)).image (cls (tpRel G B i))
  have hsub : T ⊆ insert (cls (tpRel G B i) x0)
      ((univ.filter (H.Adj x0)).image (cls (tpRel G B i))) := by
    intro c hc
    by_cases hne : c = cls (tpRel G B i) x0
    · exact hne ▸ mem_insert_self _ _
    obtain ⟨y, rfl, hy⟩ := key c hc hne
    exact mem_insert_of_mem (mem_image.2 ⟨y, mem_filter.2 ⟨mem_univ _, hy⟩, rfl⟩)
  refine (card_le_card hsub).trans ((card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1))
  calc ((univ.filter (H.Adj x0)).image (cls (tpRel G B i))).card
      = numCls (tpRel G B i) (univ.filter (H.Adj x0)) := rfl
    _ ≤ numCls (tpRel G B r) (univ.filter (H.Adj x0)) :=
        numCls_le_of_le hEi hEr fun a _ b _ h => tpRel_of_le (by omega) h
    _ ≤ m := hmis x0

/-- **`lem:mismatch-ball`.** -/
theorem numCls_ball_le (hflip : Lax185574.Flips.IsFlip G (tpSetoid G B 0) H)
    (hmis : ∀ x, numCls (tpRel G B r) (univ.filter (H.Adj x)) ≤ m) (u : V) :
    numCls (tpRel G B 0) (ballF H r u) ≤ (m + 1) ^ r := by
  -- by induction, the ball of radius `j` meets few classes of `(r-j+1)`-types
  have step : ∀ j ≤ r, numCls (tpRel G B (r - j)) (ballF H j u) ≤ (m + 1) ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      have : ballF H 0 u = {u} := by
        ext y; simp only [ballF, mem_filter, mem_univ, true_and, mem_singleton]
        rw [Lax185574Proofs.WalkDistance.withinDist_zero]; exact eq_comm
      rw [this]; simp [numCls]
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      set i := r - (j + 1)
      have hi : r - j = i + 1 := by omega
      rw [hi] at ih
      set C := (ballF H j u).image (cls (tpRel G B (i + 1)))
      have hsub : ballF H (j + 1) u ⊆ C.biUnion (closedNbhd H) := by
        intro y hy
        obtain ⟨x, hx, hxy⟩ := withinDist_succ (mem_filter.1 hy).2
        refine mem_biUnion.2 ⟨cls (tpRel G B (i + 1)) x,
          mem_image.2 ⟨x, mem_filter.2 ⟨mem_univ _, hx⟩, rfl⟩,
          mem_filter.2 ⟨mem_univ _, x, mem_cls.2 ((tpRel_isEquiv B _).refl x), hxy⟩⟩
      calc numCls (tpRel G B i) (ballF H (j + 1) u)
          ≤ numCls (tpRel G B i) (C.biUnion (closedNbhd H)) := numCls_mono _ hsub
        _ ≤ ∑ c ∈ C, numCls (tpRel G B i) (closedNbhd H c) := numCls_biUnion_le_sum _ _ _
        _ ≤ ∑ c ∈ C, (m + 1) := by
            refine sum_le_sum fun c hc => ?_
            obtain ⟨x, -, rfl⟩ := mem_image.1 hc
            exact numCls_closedNbhd_le hflip hmis (by omega) x
        _ = C.card * (m + 1) := by simp
        _ ≤ (m + 1) ^ j * (m + 1) := Nat.mul_le_mul_right _ ih
        _ = (m + 1) ^ (j + 1) := by ring
  simpa using step r le_rfl

end Ball

/-! ### Symmetrization -/

section Symmetrization

variable {Q R : V → V → Bool} {Rp : Finset V} {ρ : V → V → Prop} {m : ℕ}

/-- **Symmetrization lemma** (`lem:symmetrization`). -/
theorem exists_symmetric (hQ : IsEquiv Q) (hR : IsEquiv R) (hRQ : ∀ x y, R x y → Q x y)
    (hRp : IsRepSet R Rp) (hρ : IsInvariant Q ρ)
    (hmis : ∀ v, numCls R (misSet G ρ v) ≤ m) :
    ∃ σ : V → V → Prop, IsInvariant Q σ ∧ (∀ v y, σ v y ↔ σ y v) ∧
      ∀ v, numCls R (misSet G σ v) ≤ 3 * m := by
  -- representatives of the parts of `R` inside the part of `Q` of `v`
  let RQ : V → Finset V := fun v => Rp.filter fun x => Q v x
  let adjCnt : V → V → ℕ := fun v y => ((RQ v ×ˢ RQ y).filter fun p => G.Adj p.1 p.2).card
  have hRQ_inv : ∀ v v', Q v v' → RQ v = RQ v' := by
    intro v v' h; ext x; simp only [RQ, mem_filter]
    exact and_congr_right fun _ => ⟨fun h' => hQ.trans _ _ _ (hQ.symm _ _ h) h',
      fun h' => hQ.trans _ _ _ h h'⟩
  have hadj_symm : ∀ v y, adjCnt v y = adjCnt y v := by
    intro v y
    refine card_bij (fun p _ => (p.2, p.1)) (fun p hp => ?_) (fun p _ p' _ h => ?_)
      (fun p hp => ⟨(p.2, p.1), ?_, rfl⟩)
    · simp only [mem_filter, mem_product] at hp ⊢; exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
    · simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · simp only [mem_filter, mem_product] at hp ⊢; exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  let σ : V → V → Prop := fun v y =>
    if (ρ v y ↔ ρ y v) then ρ v y else (RQ v).card * (RQ y).card < 2 * adjCnt v y
  have hσ_inv : IsInvariant Q σ := by
    intro v v' y y' hv hy
    simp only [σ, adjCnt, hRQ_inv v v' hv, hRQ_inv y y' hy, hρ v v' y y' hv hy,
      hρ y y' v v' hy hv]
  have hσ_symm : ∀ v y, σ v y ↔ σ y v := by
    intro v y
    simp only [σ]
    by_cases h : ρ v y ↔ ρ y v
    · rw [if_pos h, if_pos h.symm]; exact h
    · rw [if_neg h, if_neg (fun h' => h h'.symm), hadj_symm v y, Nat.mul_comm]
  refine ⟨σ, hσ_inv, hσ_symm, fun v => ?_⟩
  -- the parts where `σ` and `ρ` differ
  have hRQne : ∀ w, (RQ w).Nonempty := by
    intro w
    obtain ⟨x, hx, hxw⟩ := hRp.ex w
    exact ⟨x, mem_filter.2 ⟨hx, hQ.symm _ _ (hRQ _ _ hxw)⟩⟩
  -- `cl:char`
  have hchar : ∀ y, ¬ (σ v y ↔ ρ v y) → ¬ Q v y ∧
      (RQ v).card * (RQ y).card ≤
        2 * ((RQ v ×ˢ RQ y).filter fun p => ¬ (G.Adj p.1 p.2 ↔ ρ v y)).card := by
    intro y hy
    have hinc : ¬ (ρ v y ↔ ρ y v) := by
      intro h; apply hy; simp only [σ, if_pos h]
    refine ⟨fun hvy => hinc (hρ v y y v hvy (hQ.symm _ _ hvy)), ?_⟩
    have htot := card_filter_add_card_filter_not (s := RQ v ×ˢ RQ y)
      (fun p => G.Adj p.1 p.2)
    rw [card_product] at htot
    simp only [σ, if_neg hinc] at hy
    by_cases hρvy : ρ v y
    · have : ¬ (RQ v).card * (RQ y).card < 2 * adjCnt v y := fun h => hy ⟨fun _ => hρvy, fun _ => h⟩
      have e : ((RQ v ×ˢ RQ y).filter fun p => ¬ (G.Adj p.1 p.2 ↔ ρ v y)) =
          (RQ v ×ˢ RQ y).filter fun p => ¬ G.Adj p.1 p.2 := by
        ext p; simp [hρvy]
      rw [e]; simp only [adjCnt] at this; omega
    · have : (RQ v).card * (RQ y).card < 2 * adjCnt v y := by
        by_contra h; exact hy ⟨fun h' => absurd h' h, fun h' => absurd h' hρvy⟩
      have e : ((RQ v ×ˢ RQ y).filter fun p => ¬ (G.Adj p.1 p.2 ↔ ρ v y)) =
          (RQ v ×ˢ RQ y).filter fun p => G.Adj p.1 p.2 := by
        ext p; simp [hρvy]
      rw [e]; simp only [adjCnt] at this; omega
  set E := Rp.filter fun y => ¬ (σ v y ↔ ρ v y)
  -- `cl:error-parts`: `|E| ≤ 2m`
  have hE : E.card ≤ 2 * m := by
    set b := fun y => ((RQ v).filter fun x => ¬ (G.Adj x y ↔ ρ v y)).card
    -- per class of `Q`, at least half of the pairs disagree
    have h1 : (RQ v).card * E.card ≤ 2 * ∑ y ∈ E, b y := by
      rw [card_eq_sum_ones E, mul_sum, mul_sum]
      rw [← sum_fiberwise_of_maps_to (g := cls Q) (t := E.image (cls Q))
          (fun y hy => mem_image_of_mem _ hy),
        ← sum_fiberwise_of_maps_to (g := cls Q) (t := E.image (cls Q))
          (fun y hy => mem_image_of_mem _ hy) (f := fun y => 2 * b y)]
      refine sum_le_sum fun c hc => ?_
      obtain ⟨y0, hy0, rfl⟩ := mem_image.1 hc
      have hfib : (E.filter fun y => cls Q y = cls Q y0) = RQ y0 := by
        ext y
        simp only [mem_filter, E, RQ, cls_eq_iff hQ]
        constructor
        · rintro ⟨⟨hy, -⟩, h⟩; exact ⟨hy, hQ.symm _ _ h⟩
        · rintro ⟨hy, h⟩
          refine ⟨⟨hy, ?_⟩, hQ.symm _ _ h⟩
          have h1 := hσ_inv v v y0 y (hQ.refl v) h
          have h2 := hρ v v y0 y (hQ.refl v) h
          exact fun h' => (mem_filter.1 hy0).2 (h1.trans (h'.trans h2.symm))
      rw [hfib]
      have hy0' := (mem_filter.1 hy0).2
      obtain ⟨-, hc⟩ := hchar y0 hy0'
      simp only [mul_one, sum_const, smul_eq_mul]
      calc (RQ y0).card * (RQ v).card = (RQ v).card * (RQ y0).card := Nat.mul_comm _ _
        _ ≤ 2 * ((RQ v ×ˢ RQ y0).filter fun p => ¬ (G.Adj p.1 p.2 ↔ ρ v y0)).card := hc
        _ = ∑ y ∈ RQ y0, 2 * b y := by
            rw [← mul_sum]; congr 1
            rw [card_filter, sum_product_right]
            refine sum_congr rfl fun y hy => ?_
            have hyy0 : Q y0 y := (mem_filter.1 hy).2
            simp only [b, card_filter]
            refine sum_congr rfl fun x _ => ?_
            rw [hρ v v y0 y (hQ.refl v) hyy0]
    -- every representative disagrees with at most `m` others
    have h2 : ∑ y ∈ E, b y ≤ (RQ v).card * m := by
      have : ∑ y ∈ E, b y = ∑ x ∈ RQ v, (E.filter fun y => ¬ (G.Adj x y ↔ ρ v y)).card := by
        simp only [b, card_filter]; exact sum_comm
      rw [this, ← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun x hx => ?_
      obtain ⟨hxRp, hvx⟩ := mem_filter.1 hx
      refine le_trans ?_ (hmis x)
      refine card_le_numCls_of_pairwise hR (fun y hy => ?_) fun a ha b hb hab =>
        hRp.uniq a (mem_filter.1 (mem_filter.1 ha).1).1 b (mem_filter.1 (mem_filter.1 hb).1).1 hab
      obtain ⟨hyE, hdis⟩ := mem_filter.1 hy
      simp only [misSet, mem_filter, mem_univ, true_and]
      rwa [← hρ v x y y hvx (hQ.refl y)]
    have hpos : 0 < (RQ v).card := card_pos.2 (hRQne v)
    have : (RQ v).card * E.card ≤ (RQ v).card * (2 * m) := by
      calc (RQ v).card * E.card ≤ 2 * ∑ y ∈ E, b y := h1
        _ ≤ 2 * ((RQ v).card * m) := Nat.mul_le_mul_left _ h2
        _ = (RQ v).card * (2 * m) := by ring
    exact Nat.le_of_mul_le_mul_left this hpos
  -- the mismatch of `σ`
  have hsub : misSet G σ v ⊆ misSet G ρ v ∪ univ.filter fun y => ¬ (σ v y ↔ ρ v y) := by
    intro y hy
    simp only [misSet, mem_filter, mem_univ, true_and, mem_union] at hy ⊢
    tauto
  calc numCls R (misSet G σ v)
      ≤ numCls R (misSet G ρ v ∪ univ.filter fun y => ¬ (σ v y ↔ ρ v y)) := numCls_mono _ hsub
    _ ≤ numCls R (misSet G ρ v) + numCls R (univ.filter fun y => ¬ (σ v y ↔ ρ v y)) :=
        numCls_union_le _ _ _
    _ ≤ m + E.card := by
        refine Nat.add_le_add (hmis v) ((numCls_le_reps hR hRp _).trans (card_le_card ?_))
        intro r hr
        obtain ⟨hr, y, hy, hry⟩ := mem_filter.1 hr
        refine mem_filter.2 ⟨hr, ?_⟩
        have h1 := hσ_inv v v r y (hQ.refl v) (hRQ _ _ hry)
        have h2 := hρ v v r y (hQ.refl v) (hRQ _ _ hry)
        have := (mem_filter.1 hy).2
        exact fun h' => this (h1.symm.trans (h'.trans h2))
    _ ≤ 3 * m := by omega

end Symmetrization

/-! ### The asymmetric relation -/

section Asymmetric

/-- **`lem:mismatch-asymmetric`.** If every vertex is within Hamming
distance `M₂` of some vertex of `S` (A2), and vertices of the same atomic
type over `S` are within Hamming distance `M₃` (A3), then some relation
on the atomic types over `S` has mismatch at most `M₂ + M₃`. -/
theorem exists_mismatch_asymmetric {R : V → V → Bool} {S : Finset V}
    {M2 M3 : ℕ} (hA2 : ∀ u, ∃ s ∈ S, numCls R (sdiff G u s) ≤ M2)
    (hA3 : ∀ u v, tpRel G S 0 u v → numCls R (sdiff G u v) ≤ M3) :
    ∃ ρ : V → V → Prop, IsInvariant (tpRel G S 0) ρ ∧
      ∀ v, numCls R (misSet G ρ v) ≤ M2 + M3 := by
  have hQ := tpRel_isEquiv (G := G) S 0
  -- a chosen vertex of each class, depending only on the class
  let pick : Finset V → V → V := fun c d => if h : c.Nonempty then h.choose else d
  have hpick : ∀ v, tpRel G S 0 v (pick (cls (tpRel G S 0) v) v) := by
    intro v
    have hne : (cls (tpRel G S 0) v).Nonempty := ⟨v, mem_cls.2 (hQ.refl v)⟩
    simp only [pick, dif_pos hne]
    exact mem_cls.1 hne.choose_spec
  let xQ : V → V := fun v => pick (cls (tpRel G S 0) v) v
  choose sOf hsS hsOf using hA2
  let s : V → V := fun v => sOf (xQ v)
  let ρ : V → V → Prop := fun v y => G.Adj (s v) y
  have hxQ_inv : ∀ v v', tpRel G S 0 v v' → xQ v = xQ v' := by
    intro v v' h
    have hne' : (cls (tpRel G S 0) v').Nonempty := ⟨v', mem_cls.2 (hQ.refl v')⟩
    have hc := (cls_eq_iff hQ).2 h
    show pick (cls (tpRel G S 0) v) v = pick (cls (tpRel G S 0) v') v'
    rw [hc]; simp only [pick, dif_pos hne']
  refine ⟨ρ, fun v v' y y' hv hy => ?_, fun v => ?_⟩
  · simp only [ρ, s, hxQ_inv v v' hv]
    have hsv : sOf (xQ v') ∈ S := hsS _
    exact adj_iff_of_tpRel (G := G) hy hsv |> fun h => by
      rw [G.adj_comm, h, G.adj_comm]
  · -- `N(v) △ N(s_v) ⊆ Δ[v, s_v]`
    have hsub : misSet G ρ v ⊆ sdiff G v (s v) := by
      intro y hy
      simp only [misSet, mem_filter, mem_univ, true_and, ρ] at hy
      rw [mem_sdiff]
      refine ⟨fun h => hy (Iff.of_eq (congrArg (fun z => G.Adj z y) h)), ?_⟩
      by_cases h1 : y = v; · exact Or.inl h1
      by_cases h2 : y = s v; · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr hy)
    calc numCls R (misSet G ρ v) ≤ numCls R (sdiff G v (s v)) := numCls_mono _ hsub
      _ ≤ numCls R (sdiff G v (xQ v) ∪ sdiff G (xQ v) (s v)) :=
          numCls_mono _ (sdiff_triangle G _ _ _)
      _ ≤ numCls R (sdiff G v (xQ v)) + numCls R (sdiff G (xQ v) (s v)) := numCls_union_le _ _ _
      _ ≤ M3 + M2 := Nat.add_le_add (hA3 v (xQ v) (hpick v)) (hsOf _)
      _ = M2 + M3 := by ring

end Asymmetric

/-! ### The flip of a symmetric relation -/

/-- The flip `G ⊕ σ`. -/
noncomputable def flipOf (G : SimpleGraph V) (σ : V → V → Prop) (hσ : ∀ v y, σ v y ↔ σ y v) :
    SimpleGraph V where
  Adj x y := x ≠ y ∧ ¬ (G.Adj x y ↔ σ x y)
  symm := ⟨fun x y h => ⟨Ne.symm h.1, by rw [G.adj_comm, hσ]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem isFlip_flipOf {S : Finset V} {σ : V → V → Prop} (hσ : ∀ v y, σ v y ↔ σ y v)
    (hinv : IsInvariant (tpRel G S 0) σ) :
    Lax185574.Flips.IsFlip G (tpSetoid G S 0) (flipOf G σ hσ) := by
  intro a b
  by_cases hab : σ a b
  · refine Or.inr fun x y hx hy hxy => ?_
    have : σ x y := (hinv a x b y ((tpRel_isEquiv S 0).symm _ _ hx)
      ((tpRel_isEquiv S 0).symm _ _ hy)).1 hab
    simp only [flipOf, hxy, ne_eq, not_false_eq_true, true_and, this, iff_true]
  · refine Or.inl fun x y hx hy hxy => ?_
    have : ¬ σ x y := fun h => hab ((hinv a x b y ((tpRel_isEquiv S 0).symm _ _ hx)
      ((tpRel_isEquiv S 0).symm _ _ hy)).2 h)
    simp only [flipOf, hxy, ne_eq, not_false_eq_true, true_and, this, iff_false, not_not]

theorem neighbors_flipOf_subset {σ : V → V → Prop} (hσ : ∀ v y, σ v y ↔ σ y v) (x : V) :
    univ.filter ((flipOf G σ hσ).Adj x) ⊆ misSet G σ x := by
  intro y hy
  rw [mem_filter] at hy
  unfold misSet
  simp only [mem_filter, mem_univ, true_and]
  exact hy.2.2

end Lax185574Proofs.Chain
