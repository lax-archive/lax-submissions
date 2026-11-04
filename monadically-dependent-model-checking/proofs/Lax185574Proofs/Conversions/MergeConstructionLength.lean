import Lax185574Proofs.Conversions.MergeConstructionProps

/-!
The length of the construction sequence of cl:from-merge-to-construction.

There are at most n merges, since every merge lowers the number of parts.
For the resolves, charge the resolve of two parts X and Y in stage j to
the one of them that stops being a part first, say X in stage D, and
record its least vertex x, the stage D and the least vertex y of Y. The
part Y meets the radius-1 ball of x in R_{D+1}, so for fixed x and D
there are at most w₁ choices of y (at most one if D is the last stage).
A pair of parts is resolved at most once, so the charging is injective.
A part stops being a part when it is merged into another one, either as
a source of a merge or as the target of some source. So there are at
most 2n + 1 pairs (x, D), and at most (2n + 1) · max(1, w₁) resolves.
-/

namespace Lax185574Proofs.Conversions.MergeConstruction

open Lax185574.PartialGraphs Lax185574.ConstructionSequences Lax185574.SequenceEncoding
open Lax185574.MergeSequences Lax185574.Partitions Lax185574.GraphBalls
open Lax185574.GaifmanGraph Lax185574Proofs.WithinDistBasics

open Classical

noncomputable section

variable {n : ℕ} {G : SimpleGraph (Fin n)} {ms : List (Setoid (Fin n) × SimpleGraph (Fin n))}

/-! ### Counting merges -/

variable (ms) in
/-- The number of parts of `𝒫_j`, counted by their least vertices. -/
def partNum (j : ℕ) : ℕ := (Finset.univ.filter fun v : Fin n => rep (part ms j) v = v).card

theorem length_mergeSources (j : ℕ) :
    (mergeSources ms j).length = (Finset.univ.filter (IsSource ms j)).card := by
  unfold mergeSources
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext v
  simp

theorem sources_add_partNum (hm : IsMergeSequence G ms) (j : ℕ) :
    (Finset.univ.filter (IsSource ms j)).card + partNum ms (j + 1) ≤ partNum ms j := by
  unfold partNum
  rw [← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card ?_
    intro v hv
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with hv | hv
    · exact hv.1
    · exact rep_self_of_le (part_succ_le hm j) hv
  · rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h1.2 h2

theorem sum_sources_le (hm : IsMergeSequence G ms) (k : ℕ) :
    (∑ j ∈ Finset.range k, (Finset.univ.filter (IsSource ms j)).card) + partNum ms k ≤ n := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, partNum]
    exact (Finset.card_le_univ _).trans (by simp)
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have := sources_add_partNum hm k
    omega

/-! ### Death of a part -/

variable (ms) in
/-- The part of `x` in `𝒫_D` stops being a part after stage `D`: either
`D` is the last stage, or the part of `x` grows. -/
def Dies (D : ℕ) (x : Fin n) : Prop :=
  D + 1 = ms.length ∨ ∃ v, part ms (D + 1) v x ∧ ¬ part ms D v x

theorem exists_dies {j : ℕ} (hj : j < ms.length) (a : Fin n) : ∃ D, j ≤ D ∧ Dies ms D a :=
  ⟨ms.length - 1, by omega, Or.inl (by omega)⟩

variable (ms) in
/-- The last stage at which the part of `a` of stage `j` is a part. -/
def death (j : ℕ) (a : Fin n) : ℕ :=
  if h : ∃ D, j ≤ D ∧ Dies ms D a then Nat.find h else j

theorem death_spec {j : ℕ} (hj : j < ms.length) (a : Fin n) :
    j ≤ death ms j a ∧ Dies ms (death ms j a) a := by
  have h := exists_dies (ms := ms) hj a
  simp only [death, h, dite_true]
  exact Nat.find_spec h

theorem death_lt {j : ℕ} (hj : j < ms.length) (a : Fin n) : death ms j a < ms.length := by
  have h := exists_dies (ms := ms) hj a
  simp only [death, h, dite_true]
  have := Nat.find_min' h (m := ms.length - 1) ⟨by omega, Or.inl (by omega)⟩
  omega

/-- The part of `a` does not change between stage `j` and its death. -/
theorem part_stable (hm : IsMergeSequence G ms) {j : ℕ} (hj : j < ms.length) (a : Fin n) :
    ∀ j', j ≤ j' → j' ≤ death ms j a → ∀ v, part ms j' v a ↔ part ms j v a := by
  intro j' hj' hjd
  induction j', hj' using Nat.le_induction with
  | base => exact fun v => Iff.rfl
  | succ j' hj' ih =>
    intro v
    have hlt : j' < death ms j a := by omega
    have hnd : ¬ Dies ms j' a := by
      intro hd
      have h := exists_dies (ms := ms) hj a
      have := Nat.find_min h (m := j') (by simp only [death, h, dite_true] at hlt; exact hlt)
      exact this ⟨hj', hd⟩
    rw [← ih (by omega) v]
    refine ⟨fun h => ?_, fun h => part_succ_le hm j' h⟩
    by_contra h'
    exact hnd (Or.inr ⟨v, h, h'⟩)

/-! ### Counting deaths -/

/-- The parts that stop being parts after stage `D < m − 1` are at most
twice as many as the sources of the merges of stage `D`. -/
theorem card_dies_le (hm : IsMergeSequence G ms) {D : ℕ} (hD : D + 1 < ms.length) :
    (Finset.univ.filter fun x => rep (part ms D) x = x ∧ Dies ms D x).card ≤
      2 * (Finset.univ.filter (IsSource ms D)).card := by
  have hle := part_succ_le hm D
  -- split into sources and grown targets
  have hsub : (Finset.univ.filter fun x => rep (part ms D) x = x ∧ Dies ms D x) ⊆
      Finset.univ.filter (IsSource ms D) ∪
        (Finset.univ.filter (IsSource ms D)).image (rep (part ms (D + 1))) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hrep, hdies⟩ := hx
    rcases hdies with hdies | ⟨v, hv1, hv2⟩
    · omega
    by_cases hs : rep (part ms (D + 1)) x = x
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨rep (part ms D) v, ?_, ?_⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsSource]
        refine ⟨rep_rep _ _, ?_⟩
        rw [rep_rep_of_le hle, rep_eq_of_rel _ hv1, hs]
        intro h
        apply hv2
        have := rep_rel (part ms D) v
        rw [← h] at this
        exact (part ms D).symm this
      · rw [rep_rep_of_le hle, rep_eq_of_rel _ hv1, hs]
    · exact Finset.mem_union_left _ (by simp [IsSource, hrep, hs])
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have := Finset.card_image_le (s := Finset.univ.filter (IsSource ms D))
    (f := rep (part ms (D + 1)))
  omega

/-- At the last stage only one part dies. -/
theorem card_dies_last (hm : IsMergeSequence G ms) {D : ℕ} (hD : D + 1 = ms.length) :
    (Finset.univ.filter fun x => rep (part ms D) x = x ∧ Dies ms D x).card ≤ 1 := by
  have htop : part ms D = ⊤ := part_last hm (by omega)
  refine Finset.card_le_one.2 fun x hx y hy => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  rw [← hx.1, ← hy.1]
  exact rep_eq_of_rel _ (by rw [htop]; trivial)

/-! ### Charging the resolves -/

theorem length_resolvePairs (j : ℕ) :
    (resolvePairs ms j).length = (Finset.univ.filter (Resolves ms j)).card := by
  have hnd : (resolvePairs ms j).Nodup := by
    unfold resolvePairs
    exact List.Nodup.filter _ (show (List.product (List.finRange n) (List.finRange n)).Nodup from
      (List.nodup_finRange n).product (List.nodup_finRange n))
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext p
  simp [mem_resolvePairs]

variable (ms) in
/-- The resolve events: stage `j` resolves the pair `p`. -/
def events : Finset (Σ _ : ℕ, Fin n × Fin n) :=
  (Finset.range ms.length).sigma fun j => Finset.univ.filter (Resolves ms j)

variable (ms) in
/-- The charge of a resolve event: the least vertex of the part that
dies first, the stage of its death, and the least vertex of the other
part. -/
def charge (e : Σ _ : ℕ, Fin n × Fin n) : Fin n × ℕ × Fin n :=
  if death ms e.1 e.2.1 ≤ death ms e.1 e.2.2 then (e.2.1, death ms e.1 e.2.1, e.2.2)
  else (e.2.2, death ms e.1 e.2.2, e.2.1)

variable (ms) in
/-- The possible charges. -/
def Target (t : Fin n × ℕ × Fin n) : Prop :=
  t.2.1 < ms.length ∧ rep (part ms t.2.1) t.1 = t.1 ∧ Dies ms t.2.1 t.1 ∧
    rep (part ms t.2.1) t.2.2 = t.2.2 ∧ t.2.2 ∈ graphBall (rel ms (t.2.1 + 1)) 1 {t.1}

/-- A part with least vertex `a` at stage `j` has least vertex `a` until
its death. -/
theorem rep_stable (hm : IsMergeSequence G ms) {j : ℕ} (hj : j < ms.length) {a : Fin n}
    (ha : rep (part ms j) a = a) {D : ℕ} (hjD : j ≤ D) (hD : D ≤ death ms j a) :
    rep (part ms D) a = a := by
  have hst := part_stable hm hj a D hjD hD
  apply le_antisymm (rep_le _ ((part ms D).refl a))
  have h1 := (hst _).1 (rep_rel (part ms D) a)
  calc a = rep (part ms j) a := ha.symm
    _ ≤ rep (part ms D) a := rep_le _ h1

theorem charge_target (hm : IsMergeSequence G ms) {e : Σ _ : ℕ, Fin n × Fin n}
    (he : e ∈ events ms) : Target ms (charge ms e) := by
  obtain ⟨j, a, b⟩ := e
  simp only [events, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_univ,
    true_and] at he
  obtain ⟨hj, hab, ha, hb, hrect, -⟩ := he
  dsimp only at hab ha hb hrect
  -- the two least vertices are related in `R_{D+1}` for every later stage `D`
  have hadj : ∀ D, j ≤ D → a ∈ graphBall (rel ms (D + 1)) 1 {b} ∧
      b ∈ graphBall (rel ms (D + 1)) 1 {a} := by
    intro D hD
    by_cases heq : a = b
    · subst heq
      exact ⟨⟨a, rfl, withinDist_refl _ _⟩, ⟨a, rfl, withinDist_refl _ _⟩⟩
    have hr : (rect ms j a b).Adj a b := by
      rw [rect_adj]
      exact ⟨heq, Or.inl ⟨by rw [col, ha], by rw [col, hb]⟩⟩
    have hR : (rel ms (D + 1)).Adj a b := rel_mono hm (by omega) (hrect hr)
    exact ⟨⟨b, rfl, withinDist_adj hR.symm⟩, ⟨a, rfl, withinDist_adj hR⟩⟩
  have hda := death_spec (ms := ms) hj a
  have hdb := death_spec (ms := ms) hj b
  have hla := death_lt (ms := ms) hj a
  have hlb := death_lt (ms := ms) hj b
  unfold charge
  dsimp only
  split_ifs with hle
  · exact ⟨hla, rep_stable hm hj ha hda.1 le_rfl, hda.2,
      rep_stable hm hj hb hda.1 hle, (hadj _ hda.1).2⟩
  · exact ⟨hlb, rep_stable hm hj hb hdb.1 le_rfl, hdb.2,
      rep_stable hm hj ha hdb.1 (Nat.le_of_lt (Nat.lt_of_not_le hle)), (hadj _ hdb.1).1⟩

theorem col_eq_least_iff {k : ℕ} {a : Fin n} (ha : rep (part ms k) a = a) (u : Fin n) :
    col ms k u = (a : ℕ) ↔ part ms k u a := by
  rw [← rep_eq_iff, ha, col, Fin.val_inj]

/-- A rectangle of two parts that stay parts from stage `j` to stage `j'`
is resolved at most once. -/
theorem resolves_unique {j j' : ℕ} (hjj : j < j') {a b : Fin n}
    (hres : Resolves ms j (a, b))
    (hca : ∀ v, part ms j v a ↔ part ms j' v a) (hcb : ∀ v, part ms j v b ↔ part ms j' v b)
    (hres' : Resolves ms j' (a, b)) : False := by
  obtain ⟨-, ha, hb, hrect, -⟩ := hres
  obtain ⟨-, ha', hb', -, hnot⟩ := hres'
  dsimp only at ha hb hrect ha' hb' hnot
  apply hnot
  intro u w huw
  rw [resolvedAt_adj]
  refine ⟨j, hjj, ?_⟩
  rw [block_adj]
  refine ⟨huw.ne, fun a'' b'' ha'' hb'' hne => hrect ?_⟩
  rw [rect_adj] at huw ⊢
  rw [col_eq_least_iff ha' u, col_eq_least_iff ha' w, col_eq_least_iff hb' u,
    col_eq_least_iff hb' w] at huw
  rw [col_eq_least_iff ha a'', col_eq_least_iff ha b'', col_eq_least_iff hb a'',
    col_eq_least_iff hb b'']
  obtain ⟨-, ⟨hu, hw⟩ | ⟨hw, hu⟩⟩ := huw
  · exact ⟨hne, Or.inl ⟨(part ms j).trans ha'' ((hca u).2 hu), (part ms j).trans hb'' ((hcb w).2 hw)⟩⟩
  · exact ⟨hne, Or.inr ⟨(part ms j).trans hb'' ((hca w).2 hw), (part ms j).trans ha'' ((hcb u).2 hu)⟩⟩

theorem charge_stage (e : Σ _ : ℕ, Fin n × Fin n) :
    (charge ms e).2.1 = min (death ms e.1 e.2.1) (death ms e.1 e.2.2) := by
  unfold charge
  split_ifs with h
  · exact (min_eq_left h).symm
  · dsimp only
    exact (min_eq_right (by omega)).symm

theorem charge_injOn (hm : IsMergeSequence G ms) : Set.InjOn (charge ms) (events ms) := by
  rintro ⟨j, a, b⟩ he ⟨j', a', b'⟩ he' heq
  simp only [events, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio,
    Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he he'
  have hres := he.2
  have hres' := he'.2
  have hab : a ≤ b := hres.1
  have hab' : a' ≤ b' := hres'.1
  have key : a = a' ∧ b = b' := by
    have heq' := heq
    unfold charge at heq'
    dsimp only at heq'
    have hab2 := hab
    have hab2' := hab'
    split_ifs at heq' <;> simp only [Prod.mk.injEq] at heq' <;> obtain ⟨h1, -, h2⟩ := heq' <;>
      simp only [Fin.ext_iff, Fin.le_iff_val_le_val] at h1 h2 hab2 hab2' ⊢ <;> omega
  obtain ⟨rfl, rfl⟩ := key
  have hs := congrArg (fun t => t.2.1) heq
  simp only [charge_stage] at hs
  have hda := death_spec (ms := ms) he.1 a
  have hdb := death_spec (ms := ms) he.1 b
  have hda' := death_spec (ms := ms) he'.1 a
  have hdb' := death_spec (ms := ms) he'.1 b
  set D := min (death ms j a) (death ms j b) with hD
  have hca : ∀ v, part ms j v a ↔ part ms j' v a := fun v =>
    ((part_stable hm he.1 a D (by omega) (by omega) v).symm.trans
      (part_stable hm he'.1 a D (by omega) (by omega) v))
  have hcb : ∀ v, part ms j v b ↔ part ms j' v b := fun v =>
    ((part_stable hm he.1 b D (by omega) (by omega) v).symm.trans
      (part_stable hm he'.1 b D (by omega) (by omega) v))
  rcases lt_trichotomy j j' with hlt | rfl | hlt
  · exact (resolves_unique hlt hres hca hcb hres').elim
  · rfl
  · exact (resolves_unique hlt hres' (fun v => (hca v).symm) (fun v => (hcb v).symm) hres).elim

/-! ### Counting the charges -/

variable (ms) in
/-- The least vertices of the parts that die at stage `D`. -/
def dying (D : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun x => rep (part ms D) x = x ∧ Dies ms D x

variable (ms) in
/-- The least vertices of the parts of `𝒫_D` meeting the radius-`1`
ball of `x` in `R_{D+1}`. -/
def partners (x : Fin n) (D : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun y => rep (part ms D) y = y ∧ y ∈ graphBall (rel ms (D + 1)) 1 {x}

theorem card_partners_le (hm : IsMergeSequence G ms) {D : ℕ} (hD : D < ms.length) (x : Fin n) :
    (partners ms x D).card ≤ max 1 (mergeWidth 1 ms) := by
  by_cases h1 : D + 1 < ms.length
  · refine le_max_of_le_right ((?_ : _ ≤ partCount (part ms D) _).trans
      (partCount_le_mergeWidth h1 1 x))
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (Quotient.mk (part ms D)) ?_ ?_ (Set.toFinite _)
    · intro y hy
      simp only [partners, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
      exact ⟨y, hy.2, rfl⟩
    · intro y hy y' hy' h
      simp only [partners, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
      rw [← hy.1, ← hy'.1]
      exact rep_eq_of_rel _ (Quotient.exact h)
  · refine le_max_of_le_left (Finset.card_le_one.2 fun y hy y' hy' => ?_)
    simp only [partners, Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
    rw [← hy.1, ← hy'.1]
    exact rep_eq_of_rel _ (by rw [part_last hm (by omega)]; trivial)

theorem card_dying_le (hm : IsMergeSequence G ms) {D : ℕ} (hD : D < ms.length) :
    (dying ms D).card ≤ 2 * (Finset.univ.filter (IsSource ms D)).card +
      (if D + 1 = ms.length then 1 else 0) := by
  by_cases h1 : D + 1 < ms.length
  · have := card_dies_le hm h1
    unfold dying
    omega
  · have := card_dies_last hm (D := D) (by omega)
    unfold dying
    simp only [show D + 1 = ms.length by omega, if_true]
    omega

theorem sum_ite_last (m : ℕ) : (∑ D ∈ Finset.range m, if D + 1 = m then 1 else 0) ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    omega

/-- **The number of resolves** is at most `(2n + 1) · max(1, w₁)`. -/
theorem card_events_le (hm : IsMergeSequence G ms) :
    (events ms).card ≤ (2 * n + 1) * max 1 (mergeWidth 1 ms) := by
  set B := max 1 (mergeWidth 1 ms)
  let pairs : Finset (Fin n × ℕ) :=
    (Finset.range ms.length).biUnion fun D => (dying ms D).image fun x => (x, D)
  let T : Finset (Fin n × ℕ × Fin n) :=
    pairs.biUnion fun p => (partners ms p.1 p.2).image fun y => (p.1, p.2, y)
  have h1 : (events ms).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (charge ms) (fun e he => ?_) (charge_injOn hm)
    obtain ⟨hD, hx, hdies, hy, hball⟩ := charge_target hm he
    exact Finset.mem_biUnion.2 ⟨((charge ms e).1, (charge ms e).2.1),
      Finset.mem_biUnion.2 ⟨(charge ms e).2.1, Finset.mem_range.2 hD,
        Finset.mem_image.2 ⟨(charge ms e).1, by simp [dying, hx, hdies], rfl⟩⟩,
      Finset.mem_image.2 ⟨(charge ms e).2.2, by simp [partners, hy, hball], rfl⟩⟩
  have h2 : T.card ≤ pairs.card * B := by
    refine Finset.card_biUnion_le.trans ?_
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun p hp => Finset.card_image_le.trans ?_
    simp only [pairs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨D, hD, x, -, rfl⟩ := hp
    exact card_partners_le hm hD x
  have h3 : pairs.card ≤ 2 * n + 1 := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun D hD => Finset.card_image_le.trans
      (card_dying_le hm (Finset.mem_range.1 hD))).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have := sum_sources_le hm ms.length
    have := sum_ite_last ms.length
    omega
  calc (events ms).card ≤ pairs.card * B := h1.trans h2
    _ ≤ (2 * n + 1) * B := Nat.mul_le_mul_right _ h3

/-! ### The length -/

theorem length_steps_range (k : ℕ) :
    ((List.range k).flatMap (stageSteps G ms)).length =
      ∑ j ∈ Finset.range k, ((resolvePairs ms j).length + (mergeSources ms j).length) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]
    simp [stageSteps]

theorem card_events :
    (events ms).card = ∑ j ∈ Finset.range ms.length, (resolvePairs ms j).length := by
  rw [events, Finset.card_sigma]
  exact Finset.sum_congr rfl fun j _ => (length_resolvePairs j).symm

/-- **The length bound** `ℓ ≤ 3 (n + 1)(w₁ + 1)`. -/
theorem length_run_le (hm : IsMergeSequence G ms) :
    (script G ms).run.length ≤ 3 * (n + 1) * (mergeWidth 1 ms + 1) := by
  rw [Script.run, List.length_scanl]
  change ((List.range ms.length).flatMap (stageSteps G ms)).length + 1 ≤ _
  rw [length_steps_range, Finset.sum_add_distrib, ← card_events]
  have h1 := card_events_le hm (G := G)
  have h2 := sum_sources_le hm ms.length
  have h3 : ∑ j ∈ Finset.range ms.length, (mergeSources ms j).length ≤ n := by
    simp only [length_mergeSources]
    omega
  have h4 : max 1 (mergeWidth 1 ms) ≤ mergeWidth 1 ms + 1 := max_le (by omega) (by omega)
  have h5 := Nat.mul_le_mul_left (2 * n + 1) h4
  nlinarith

end

end Lax185574Proofs.Conversions.MergeConstruction
