import Lax185574Proofs.Chain.Sampling

/-!
The Predamping Lemma (`lem:predamping` of the companion paper).

The procedure grows a set `S`, maintaining the partition `𝒫(G, A ∪ S)` of
a monotone and respectful partition selector `𝒫` and the representatives
of its parts, the first vertex of each part in a fixed vertex ordering. It
adds the first vertex `w` (in the linear order of the vertex type) to
which one of the following rules applies, the first applicable rule
first, until none applies:

* (R1) `w` crosses more than `q' κ` parts;
* (R2) `ham(w, s) > 5 q' κ²` for every `s ∈ S`;
* (R3) for every `s ∈ S`, at least `ζ = 2 q' κ` representatives lie
  strictly between `w` and `s` in the ordering.

Here `q' = 3(q+1)` and `κ ≥ 1` stands for both the growth ratio `γ` and
the packing ratio `β` of the paper. The output satisfies (A2) and (A3)
for every `κ`, and (A1), `q |S| ≤ |A|`, whenever `κ` bounds the growth
ratio of `𝒫` and the packing ratio of `G` and `|A| ≥ 2q'`.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- A vertex ordering, given by injective positions whose range is an
initial segment of `ℕ`. -/
structure VOrder (V : Type u) where
  pos : V → ℕ
  inj : Function.Injective pos
  dense : ∀ x i, i < pos x → ∃ y, pos y = i

/-- A monotone and respectful partition selector, given as Boolean
relations. -/
structure IsSelector (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V → V → V → Bool) : Prop where
  equiv : ∀ B, IsEquiv (P B)
  anti : ∀ {B B' : Finset V}, B ⊆ B' → ∀ x y, P B' x y → P B x y
  resp : ∀ B x y, P B x y → tpRel G B 0 x y

section Defs

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V → V → V → Bool) (o : VOrder V)

/-- The representatives: the first vertex of each part. -/
def reps (B : Finset V) : Finset V := univ.filter fun x => ∀ y, P B x y → o.pos x ≤ o.pos y

/-- The number of parts crossed by `w`. -/
def crossCnt (B : Finset V) (w : V) : ℕ :=
  ((reps P o B).filter fun r => Crosses G w (cls (P B) r)).card

/-- `ham(u, v)`: the number of parts meeting `Δ[u,v]`. -/
def ham (B : Finset V) (u v : V) : ℕ :=
  ((reps P o B).filter fun r => ∃ y ∈ sdiff G u v, P B r y).card

/-- The number of representatives strictly between `w` and `s`. -/
def betw (B : Finset V) (w s : V) : ℕ :=
  ((reps P o B).filter fun r => (o.pos w < o.pos r ∧ o.pos r < o.pos s) ∨
    (o.pos s < o.pos r ∧ o.pos r < o.pos w)).card

variable (A : Finset V) (q κ : ℕ)

/-- Rule (R1). -/
def Rule1 (S : Finset V) (w : V) : Prop := 3 * (q + 1) * κ < crossCnt G P o (A ∪ S) w

/-- Rule (R2). -/
def Rule2 (S : Finset V) (w : V) : Prop :=
  ∀ s ∈ S, 5 * (3 * (q + 1)) * κ * κ < ham G P o (A ∪ S) w s

/-- Rule (R3). -/
def Rule3 (S : Finset V) (w : V) : Prop :=
  ∀ s ∈ S, 2 * (3 * (q + 1)) * κ ≤ betw P o (A ∪ S) w s

instance (S : Finset V) (w : V) : Decidable (Rule1 G P o A q κ S w) := by
  unfold Rule1; infer_instance
instance (S : Finset V) (w : V) : Decidable (Rule2 G P o A q κ S w) := by
  unfold Rule2; infer_instance
instance (S : Finset V) (w : V) : Decidable (Rule3 P o A q κ S w) := by
  unfold Rule3; infer_instance

/-- The first vertex to which the first applicable rule applies. -/
def pdStep (S : Finset V) : Option V :=
  (((univ : Finset V).sort (· ≤ ·)).find? fun w => decide (Rule1 G P o A q κ S w)) <|>
  (((univ : Finset V).sort (· ≤ ·)).find? fun w => decide (Rule2 G P o A q κ S w)) <|>
  (((univ : Finset V).sort (· ≤ ·)).find? fun w => decide (Rule3 P o A q κ S w))

/-- Apply rules while one applies. -/
def pdRun : ℕ → Finset V → Finset V
  | 0, S => S
  | f + 1, S => match pdStep G P o A q κ S with
    | none => S
    | some w => pdRun f (insert w S)

/-- The output of the predamping procedure. -/
def predamp : Finset V := pdRun G P o A q κ (Fintype.card V + 1) ∅

end Defs

variable {G : SimpleGraph V} [DecidableRel G.Adj] {P : Finset V → V → V → Bool} {o : VOrder V}

/-! ### Representatives -/

section Reps

variable (hP : IsSelector G P)
include hP

theorem exists_rep (B : Finset V) (x : V) : ∃ r ∈ reps P o B, P B r x := by
  obtain ⟨r, hr, hmin⟩ := (cls (P B) x).exists_min_image o.pos ⟨x, mem_cls.2 ((hP.equiv B).refl x)⟩
  rw [mem_cls] at hr
  refine ⟨r, mem_filter.2 ⟨mem_univ _, fun y hy => hmin y (mem_cls.2 ?_)⟩,
    (hP.equiv B).symm _ _ hr⟩
  exact (hP.equiv B).trans _ _ _ hr hy

theorem rep_unique {B : Finset V} {r r' : V} (hr : r ∈ reps P o B) (hr' : r' ∈ reps P o B)
    (h : P B r r') : r = r' := by
  have h1 := (mem_filter.1 hr).2 r' h
  have h2 := (mem_filter.1 hr').2 r ((hP.equiv B).symm _ _ h)
  exact o.inj (le_antisymm h1 h2)

/-- Representatives persist when the parameter set grows. -/
theorem reps_mono {B B' : Finset V} (hBB' : B ⊆ B') : reps P o B ⊆ reps P o B' := by
  intro x hx
  exact mem_filter.2 ⟨mem_univ _, fun y hy => (mem_filter.1 hx).2 y (hP.anti hBB' x y hy)⟩

/-- The number of parts meeting `Y`, counted by representatives. -/
theorem numCls_eq_reps (B Y : Finset V) :
    numCls (P B) Y = ((reps P o B).filter fun r => ∃ y ∈ Y, P B r y).card := by
  unfold numCls
  symm
  refine card_bij (fun r _ => cls (P B) r) (fun r hr => ?_) (fun r hr r' hr' h => ?_)
    (fun c hc => ?_)
  · obtain ⟨-, y, hy, hry⟩ := mem_filter.1 hr
    exact mem_image.2 ⟨y, hy, ((cls_eq_iff (hP.equiv B)).2 hry).symm⟩
  · exact rep_unique hP (mem_filter.1 hr).1 (mem_filter.1 hr').1
      ((cls_eq_iff (hP.equiv B)).1 h)
  · obtain ⟨y, hy, rfl⟩ := mem_image.1 hc
    obtain ⟨r, hr, hry⟩ := exists_rep hP B y
    exact ⟨r, mem_filter.2 ⟨hr, y, hy, hry⟩, (cls_eq_iff (hP.equiv B)).2 hry⟩

theorem card_reps (B : Finset V) : (reps P o B).card = numCls (P B) univ := by
  rw [numCls_eq_reps hP]
  congr 1; ext r; simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h, r, (hP.equiv B).refl r⟩, fun h => h.1⟩

theorem ham_eq_numCls (B : Finset V) (u v : V) :
    ham G P o B u v = numCls (P B) (sdiff G u v) := (numCls_eq_reps hP B _).symm

/-- A vertex of `B` crosses no part of `𝒫(G, B)`. -/
theorem not_crosses_of_mem {B : Finset V} {w : V} (hw : w ∈ B) (r : V) :
    ¬ Crosses G w (cls (P B) r) := by
  rintro ⟨hwr, hc, ha⟩
  by_cases hadj : G.Adj w r
  · refine hc fun z hz hzw => ?_
    have hrz : tpRel G B 0 r z := hP.resp B r z (mem_cls.1 hz)
    have hrw : r ≠ w := fun h => hwr (h ▸ mem_cls.2 ((hP.equiv B).refl r))
    have := adj_iff_of_tpRel hrz hw
    rw [G.adj_comm, ← this, G.adj_comm]; exact hadj
  · refine ha fun z hz hzw hwz => hadj ?_
    have hrz : tpRel G B 0 r z := hP.resp B r z (mem_cls.1 hz)
    have := adj_iff_of_tpRel hrz hw
    rw [G.adj_comm, this, G.adj_comm]; exact hwz

/-- Adding a vertex `w` to the parameter set splits every part crossed by
`w`, so the number of parts grows by at least the number of crossed
parts. -/
theorem card_reps_insert (B : Finset V) (w : V) :
    (reps P o B).card + crossCnt G P o B w ≤ (reps P o (insert w B)).card := by
  set B' := insert w B
  have hBB' : B ⊆ B' := subset_insert _ _
  -- every representative over `B'` maps to the representative of its part over `B`
  have hrepB : ∀ x, ∃ r ∈ reps P o B, P B r x := exists_rep hP B
  choose f hf hfx using hrepB
  -- the fibre of a representative `r` over `B` contains at least one
  -- representative over `B'`, and two if `w` crosses its part
  have hfib : ∀ r ∈ reps P o B, (if Crosses G w (cls (P B) r) then 2 else 1) ≤
      ((reps P o B').filter fun x => f x = r).card := by
    intro r hr
    have hfr : ∀ x, P B r x → f x = r := fun x hx =>
      (rep_unique hP (hf x) hr ((hP.equiv B).trans _ _ _ (hfx x) ((hP.equiv B).symm _ _ hx)))
    split_ifs with hcr
    · obtain ⟨hwr, hc, ha⟩ := hcr
      simp only [IsComplete, not_forall] at hc
      simp only [IsAnticomplete, not_forall, not_not] at ha
      obtain ⟨z1, hz1, hz1w, hz1a⟩ := hc
      obtain ⟨z2, hz2, hz2w, hz2a⟩ := ha
      obtain ⟨x1, hx1, hx1z⟩ := exists_rep hP B' z1
      obtain ⟨x2, hx2, hx2z⟩ := exists_rep hP B' z2
      have hne : x1 ≠ x2 := by
        rintro rfl
        have : P B' z1 z2 := (hP.equiv B').trans _ _ _ ((hP.equiv B').symm _ _ hx1z) hx2z
        have h := adj_iff_of_tpRel (hP.resp B' _ _ this) (mem_insert_self w B)
        rw [G.adj_comm z1, G.adj_comm z2] at h
        exact hz1a (h.2 hz2a)
      have h1 : f x1 = r := hfr x1 ((hP.equiv B).trans _ _ _ (mem_cls.1 hz1)
        ((hP.equiv B).symm _ _ (hP.anti hBB' _ _ hx1z)))
      have h2 : f x2 = r := hfr x2 ((hP.equiv B).trans _ _ _ (mem_cls.1 hz2)
        ((hP.equiv B).symm _ _ (hP.anti hBB' _ _ hx2z)))
      have : ({x1, x2} : Finset V) ⊆ (reps P o B').filter fun x => f x = r := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_filter.2 ⟨hx1, h1⟩
        · exact mem_filter.2 ⟨hx2, h2⟩
      exact (card_pair hne).symm.le.trans (card_le_card this)
    · obtain ⟨x, hx, hxr⟩ := exists_rep hP B' r
      refine card_pos.2 ⟨x, mem_filter.2 ⟨hx, hfr x ?_⟩⟩
      exact (hP.equiv B).symm _ _ (hP.anti hBB' _ _ hxr)
  have hsum := card_eq_sum_card_fiberwise (s := reps P o B') (t := reps P o B) (f := f)
    (fun x _ => hf x)
  rw [hsum]
  calc (reps P o B).card + crossCnt G P o B w
      = ∑ r ∈ reps P o B, (if Crosses G w (cls (P B) r) then 2 else 1) := by
        unfold crossCnt
        rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
        have := card_filter_add_card_filter_not
          (s := reps P o B) (fun r => Crosses G w (cls (P B) r))
        omega
    _ ≤ ∑ r ∈ reps P o B, ((reps P o B').filter fun x => f x = r).card := sum_le_sum hfib

/-- The parts meeting `Δ[u,v]`: at most two contain `u` or `v`, the
crossed ones are counted by `crossCnt`, and every other one has its
representative in `Δ[u,v] ∖ {u, v}`. -/
theorem ham_le (B : Finset V) (u v : V) :
    ham G P o B u v ≤ 2 + crossCnt G P o B u + crossCnt G P o B v +
      ((reps P o B).filter fun r => r ∈ sdiff G u v ∧ r ≠ u ∧ r ≠ v).card := by
  unfold ham crossCnt
  set R := reps P o B
  have hsub : (R.filter fun r => ∃ y ∈ sdiff G u v, P B r y) ⊆
      (R.filter fun r => P B r u) ∪ (R.filter fun r => P B r v) ∪
        (R.filter fun r => Crosses G u (cls (P B) r)) ∪
        (R.filter fun r => Crosses G v (cls (P B) r)) ∪
        (R.filter fun r => r ∈ sdiff G u v ∧ r ≠ u ∧ r ≠ v) := by
    intro r hr
    obtain ⟨hrR, y, hy, hry⟩ := mem_filter.1 hr
    simp only [mem_union, mem_filter, hrR, true_and]
    by_cases hru : P B r u; · tauto
    by_cases hrv : P B r v; · tauto
    by_cases hcu : Crosses G u (cls (P B) r); · tauto
    by_cases hcv : Crosses G v (cls (P B) r); · tauto
    right
    have hu : u ∉ cls (P B) r := fun h => hru (mem_cls.1 h)
    have hv : v ∉ cls (P B) r := fun h => hrv (mem_cls.1 h)
    have hyu : y ≠ u := fun h => hru (h ▸ hry)
    have hyv : y ≠ v := fun h => hrv (h ▸ hry)
    have hru' : r ≠ u := fun h => hru (h ▸ (hP.equiv B).refl r)
    have hrv' : r ≠ v := fun h => hrv (h ▸ (hP.equiv B).refl r)
    have huv : u ≠ v := ((mem_sdiff G).1 hy).1
    have hyd := (mem_sdiff_of_ne G huv hyu hyv).1 hy
    refine ⟨(mem_sdiff_of_ne G huv hru' hrv').2 ?_, hru', hrv'⟩
    have hyc : y ∈ cls (P B) r := mem_cls.2 hry
    have hrc : r ∈ cls (P B) r := mem_cls.2 ((hP.equiv B).refl r)
    simp only [Crosses, hu, hv, not_false_eq_true, true_and,
      not_and, not_not] at hcu hcv
    -- `u` and `v` are homogeneous to the part of `r`
    have hU : (G.Adj u y ↔ G.Adj u r) := by
      by_cases hc : IsComplete G u (cls (P B) r)
      · exact ⟨fun _ => hc r hrc hru', fun _ => hc y hyc hyu⟩
      · have ha := hcu hc
        exact ⟨fun h => absurd h (ha y hyc hyu), fun h => absurd h (ha r hrc hru')⟩
    have hV : (G.Adj v y ↔ G.Adj v r) := by
      by_cases hc : IsComplete G v (cls (P B) r)
      · exact ⟨fun _ => hc r hrc hrv', fun _ => hc y hyc hyv⟩
      · have ha := hcv hc
        exact ⟨fun h => absurd h (ha y hyc hyv), fun h => absurd h (ha r hrc hrv')⟩
    rw [← hU, ← hV]; exact hyd
  have hle1 : (R.filter fun r => P B r u).card ≤ 1 :=
    card_le_one.2 fun a ha b hb => rep_unique hP (mem_filter.1 ha).1 (mem_filter.1 hb).1
      ((hP.equiv B).trans _ _ _ (mem_filter.1 ha).2 ((hP.equiv B).symm _ _ (mem_filter.1 hb).2))
  have hle2 : (R.filter fun r => P B r v).card ≤ 1 :=
    card_le_one.2 fun a ha b hb => rep_unique hP (mem_filter.1 ha).1 (mem_filter.1 hb).1
      ((hP.equiv B).trans _ _ _ (mem_filter.1 ha).2 ((hP.equiv B).symm _ _ (mem_filter.1 hb).2))
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (card_union_le _ _) _) _).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (card_union_le _ _) _) _) _).trans ?_
  omega

end Reps

/-! ### The steps of the procedure -/

section Steps

variable {A : Finset V} {q κ : ℕ}

/-- The procedure only adds vertices. A run can therefore stop as soon as
`q |S| > |A|`, since the output would fail the size test as well. -/
theorem subset_pdRun (f : ℕ) (S : Finset V) : S ⊆ pdRun G P o A q κ f S := by
  induction f generalizing S with
  | zero => exact le_rfl
  | succ f ih =>
    unfold pdRun
    cases pdStep G P o A q κ S with
    | none => exact le_rfl
    | some w => exact (subset_insert w S).trans (ih _)

theorem pdStep_spec {S : Finset V} {w : V} (h : pdStep G P o A q κ S = some w) :
    Rule1 G P o A q κ S w ∨ ((∀ x, ¬ Rule1 G P o A q κ S x) ∧ Rule2 G P o A q κ S w) ∨
      ((∀ x, ¬ Rule1 G P o A q κ S x) ∧ (∀ x, ¬ Rule2 G P o A q κ S x) ∧
        Rule3 P o A q κ S w) := by
  unfold pdStep at h
  have hall : ∀ (p : V → Bool) x, List.find? p ((univ : Finset V).sort (· ≤ ·)) = none →
      p x = false := fun p x hp => by
    rw [List.find?_eq_none] at hp
    simpa using hp x (by simp)
  cases h1 : List.find? (fun w => decide (Rule1 G P o A q κ S w)) ((univ : Finset V).sort (· ≤ ·))
    with
  | some w1 =>
    rw [h1] at h
    simp only [Option.orElse_eq_orElse, Option.orElse_some, Option.some.injEq] at h
    subst h
    left; simpa using List.find?_some h1
  | none =>
    rw [h1] at h
    have n1 : ∀ x, ¬ Rule1 G P o A q κ S x := fun x => by simpa using hall _ x h1
    cases h2 : List.find? (fun w => decide (Rule2 G P o A q κ S w))
        ((univ : Finset V).sort (· ≤ ·)) with
    | some w2 =>
      rw [h2] at h
      simp only [Option.orElse_eq_orElse, Option.orElse_none, Option.orElse_some,
        Option.some.injEq] at h
      subst h
      right; left; exact ⟨n1, by simpa using List.find?_some h2⟩
    | none =>
      rw [h2] at h
      have n2 : ∀ x, ¬ Rule2 G P o A q κ S x := fun x => by simpa using hall _ x h2
      simp only [Option.orElse_eq_orElse, Option.orElse_none] at h
      right; right; exact ⟨n1, n2, by simpa using List.find?_some h⟩

theorem pdStep_none {S : Finset V} (h : pdStep G P o A q κ S = none) (x : V) :
    ¬ Rule1 G P o A q κ S x ∧ ¬ Rule2 G P o A q κ S x ∧ ¬ Rule3 P o A q κ S x := by
  unfold pdStep at h
  have key : ∀ (p : V → Bool), List.find? p ((univ : Finset V).sort (· ≤ ·)) = none →
      p x = false := fun p hp => by
    rw [List.find?_eq_none] at hp
    simpa using hp x (by simp)
  cases h1 : List.find? (fun w => decide (Rule1 G P o A q κ S w)) ((univ : Finset V).sort (· ≤ ·))
  · rw [h1] at h
    cases h2 : List.find? (fun w => decide (Rule2 G P o A q κ S w))
        ((univ : Finset V).sort (· ≤ ·))
    · rw [h2] at h
      simp only [Option.orElse_eq_orElse, Option.orElse_none] at h
      exact ⟨by simpa using key _ h1, by simpa using key _ h2, by simpa using key _ h⟩
    · rw [h2] at h
      simp only [Option.orElse_eq_orElse, Option.orElse_none, Option.orElse_some] at h
      exact absurd h (by simp)
  · rw [h1] at h
    simp only [Option.orElse_eq_orElse, Option.orElse_some] at h
    exact absurd h (by simp)

variable (hP : IsSelector G P)
include hP

/-- A vertex chosen by a rule is not yet in `S`. -/
theorem pdStep_not_mem (hκ : 1 ≤ κ) {S : Finset V} {w : V} (h : pdStep G P o A q κ S = some w) :
    w ∉ S := by
  intro hw
  rcases pdStep_spec h with h1 | ⟨-, h2⟩ | ⟨-, -, h3⟩
  · unfold Rule1 crossCnt at h1
    have : ((reps P o (A ∪ S)).filter fun r => Crosses G w (cls (P (A ∪ S)) r)) = ∅ :=
      filter_false_of_mem fun r _ => not_crosses_of_mem hP (mem_union_right A hw) r
    rw [this, card_empty] at h1; omega
  · have := h2 w hw
    rw [ham_eq_numCls hP, sdiff_self] at this
    simp [numCls] at this
  · have := h3 w hw
    unfold betw at this
    have h0 : ((reps P o (A ∪ S)).filter fun r => (o.pos w < o.pos r ∧ o.pos r < o.pos w) ∨
        (o.pos w < o.pos r ∧ o.pos r < o.pos w)) = ∅ :=
      filter_false_of_mem fun r _ h => by omega
    rw [h0, card_empty] at this
    have : 1 ≤ 2 * (3 * (q + 1)) * κ := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega

theorem pdRun_spec (hκ : 1 ≤ κ) (f : ℕ) (S : Finset V) (hf : Fintype.card V < S.card + f) :
    pdStep G P o A q κ (pdRun G P o A q κ f S) = none := by
  induction f generalizing S with
  | zero => exact absurd (card_le_univ S) (by omega)
  | succ f ih =>
    unfold pdRun
    cases h : pdStep G P o A q κ S with
    | none => exact h
    | some w =>
      exact ih _ (by rw [card_insert_of_notMem (pdStep_not_mem hP hκ h)]; omega)

/-- The output of the procedure admits no rule. -/
theorem predamp_final (hκ : 1 ≤ κ) (x : V) :
    ¬ Rule1 G P o A q κ (predamp G P o A q κ) x ∧ ¬ Rule2 G P o A q κ (predamp G P o A q κ) x ∧
      ¬ Rule3 P o A q κ (predamp G P o A q κ) x :=
  pdStep_none (pdRun_spec hP hκ _ ∅ (by simp)) x

end Steps

/-! ### The invariant of the procedure -/

section Invariant

variable {A : Finset V} {q κ : ℕ}

/-- The invariant: `S` splits into the vertices added by each rule, with
the properties used in the size bound. -/
def PdInv (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V → V → V → Bool) (o : VOrder V)
    (A : Finset V) (q κ : ℕ) (S : Finset V) : Prop :=
  ∃ S1 S2 S3 : Finset V, S ⊆ S1 ∪ S2 ∪ S3 ∧ S2 ⊆ S ∧ S3 ⊆ S ∧
    3 * (q + 1) * κ * S1.card ≤ (reps P o (A ∪ S)).card ∧
    (∀ u ∈ S2, ∀ v ∈ S2, u ≠ v →
      3 * (q + 1) * κ * κ < (sdiff G u v ∩ reps P o (A ∪ S)).card) ∧
    (∀ u ∈ S3, ∀ v ∈ S3, u ≠ v → 2 * (3 * (q + 1)) * κ ≤ betw P o (A ∪ S) u v)

theorem betw_comm (B : Finset V) (w s : V) : betw P o B w s = betw P o B s w := by
  unfold betw; congr 1; ext r; simp only [mem_filter]; tauto

variable (hP : IsSelector G P)
include hP

theorem betw_mono {B B' : Finset V} (h : B ⊆ B') (w s : V) :
    betw P o B w s ≤ betw P o B' w s := by
  unfold betw; exact card_le_card (filter_subset_filter _ (reps_mono hP h))

theorem pdInv_empty : PdInv G P o A q κ ∅ :=
  ⟨∅, ∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem pdInv_step (hκ : 1 ≤ κ) {S : Finset V} (hS : PdInv G P o A q κ S) {w : V}
    (h : pdStep G P o A q κ S = some w) : PdInv G P o A q κ (insert w S) := by
  obtain ⟨S1, S2, S3, hsub, hS2, hS3, h1, h2, h3⟩ := hS
  have hwS : w ∉ S := pdStep_not_mem hP hκ h
  have hB : A ∪ S ⊆ A ∪ insert w S := union_subset_union le_rfl (subset_insert _ _)
  have hB' : A ∪ insert w S = insert w (A ∪ S) := by ext; simp only [mem_union, mem_insert]; tauto
  have hrepsmono := reps_mono (o := o) hP hB
  have hcard_mono : (reps P o (A ∪ S)).card ≤ (reps P o (A ∪ insert w S)).card :=
    card_le_card hrepsmono
  have h2' : ∀ u ∈ S2, ∀ v ∈ S2, u ≠ v →
      3 * (q + 1) * κ * κ < (sdiff G u v ∩ reps P o (A ∪ insert w S)).card :=
    fun u hu v hv huv => (h2 u hu v hv huv).trans_le
      (card_le_card (inter_subset_inter le_rfl hrepsmono))
  have h3' : ∀ u ∈ S3, ∀ v ∈ S3, u ≠ v →
      2 * (3 * (q + 1)) * κ ≤ betw P o (A ∪ insert w S) u v :=
    fun u hu v hv huv => (h3 u hu v hv huv).trans (betw_mono hP hB u v)
  have hsub' : ∀ T1 T2 T3 : Finset V, S1 ⊆ T1 → S2 ⊆ T2 → S3 ⊆ T3 →
      w ∈ T1 ∪ T2 ∪ T3 → insert w S ⊆ T1 ∪ T2 ∪ T3 := by
    intro T1 T2 T3 e1 e2 e3 hw x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact hw
    · exact union_subset_union (union_subset_union e1 e2) e3 (hsub hx)
  rcases pdStep_spec h with r1 | ⟨n1, r2⟩ | ⟨-, -, r3⟩
  · -- rule 1: the number of parts grows by more than `q' κ`
    refine ⟨insert w S1, S2, S3, hsub' _ _ _ (subset_insert _ _) le_rfl le_rfl (by simp),
      hS2.trans (subset_insert _ _), hS3.trans (subset_insert _ _), ?_, h2', h3'⟩
    have hgrow := card_reps_insert (o := o) hP (A ∪ S) w
    rw [← hB'] at hgrow
    unfold Rule1 at r1
    calc 3 * (q + 1) * κ * (insert w S1).card ≤ 3 * (q + 1) * κ * (S1.card + 1) :=
          Nat.mul_le_mul_left _ (card_insert_le _ _)
      _ = 3 * (q + 1) * κ * S1.card + 3 * (q + 1) * κ := by ring
      _ ≤ _ := by omega
  · -- rule 2: the new vertex is far from all earlier ones
    have key : ∀ v ∈ S, w ≠ v →
        3 * (q + 1) * κ * κ < (sdiff G w v ∩ reps P o (A ∪ insert w S)).card := by
      intro v hv hwv
      have hfar := r2 v hv
      have hle := ham_le (o := o) hP (A ∪ S) w v
      have hcw : crossCnt G P o (A ∪ S) w ≤ 3 * (q + 1) * κ := not_lt.1 (n1 w)
      have hcv : crossCnt G P o (A ∪ S) v ≤ 3 * (q + 1) * κ := not_lt.1 (n1 v)
      have hZ : ((reps P o (A ∪ S)).filter fun r => r ∈ sdiff G w v ∧ r ≠ w ∧ r ≠ v).card ≤
          (sdiff G w v ∩ reps P o (A ∪ insert w S)).card := by
        refine card_le_card fun r hr => ?_
        obtain ⟨hrR, hrd, -⟩ := mem_filter.1 hr
        exact mem_inter.2 ⟨hrd, hrepsmono hrR⟩
      have hκ2 : 3 * (q + 1) * κ * κ + 2 + 2 * (3 * (q + 1) * κ) ≤
          5 * (3 * (q + 1)) * κ * κ := by
        have : 3 * (q + 1) * κ ≤ 3 * (q + 1) * κ * κ := Nat.le_mul_of_pos_right _ hκ
        have : 3 ≤ 3 * (q + 1) * κ * κ := by
          calc 3 ≤ 3 * (q + 1) * 1 * 1 := by omega
            _ ≤ 3 * (q + 1) * κ * κ :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ hκ) hκ
        nlinarith
      omega
    refine ⟨S1, insert w S2, S3, hsub' _ _ _ le_rfl (subset_insert _ _) le_rfl (by simp),
      insert_subset_insert _ hS2, hS3.trans (subset_insert _ _), h1.trans hcard_mono, ?_, h3'⟩
    intro u hu v hv huv
    rw [mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd rfl huv
    · exact key v (hS2 hv) huv
    · rw [sdiff_comm]; exact key u (hS2 hu) (Ne.symm huv)
    · exact h2' u hu v hv huv
  · -- rule 3: the new vertex is far from all earlier ones in the ordering
    have key : ∀ v ∈ S, 2 * (3 * (q + 1)) * κ ≤ betw P o (A ∪ insert w S) w v :=
      fun v hv => (r3 v hv).trans (betw_mono hP hB w v)
    refine ⟨S1, S2, insert w S3, hsub' _ _ _ le_rfl le_rfl (subset_insert _ _) (by simp),
      hS2.trans (subset_insert _ _), insert_subset_insert _ hS3, h1.trans hcard_mono, h2', ?_⟩
    intro u hu v hv huv
    rw [mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd rfl huv
    · exact key v (hS3 hv)
    · rw [betw_comm]; exact key u (hS3 hu)
    · exact h3' u hu v hv huv

theorem pdInv_run (hκ : 1 ≤ κ) (f : ℕ) {S : Finset V} (hS : PdInv G P o A q κ S) :
    PdInv G P o A q κ (pdRun G P o A q κ f S) := by
  induction f generalizing S with
  | zero => exact hS
  | succ f ih =>
    unfold pdRun
    cases h : pdStep G P o A q κ S with
    | none => exact hS
    | some w => exact ih (pdInv_step hP hκ hS h)

theorem pdInv_predamp (hκ : 1 ≤ κ) : PdInv G P o A q κ (predamp G P o A q κ) :=
  pdInv_run hP hκ _ (pdInv_empty hP)

end Invariant

/-! ### Assertion (A1): the size bound -/

section Size

variable {A : Finset V} {q κ : ℕ}

/-- Points pairwise separated by `ζ` representatives in the ordering:
`ζ (|T| - 1)` representatives lie before the last point. -/
theorem card_mul_le_of_betw {B : Finset V} {ζ : ℕ} :
    ∀ T : Finset V, (∀ u ∈ T, ∀ v ∈ T, u ≠ v → ζ ≤ betw P o B u v) →
      ∀ m ∈ T, (∀ t ∈ T, o.pos t ≤ o.pos m) →
        ζ * (T.card - 1) ≤ ((reps P o B).filter fun r => o.pos r < o.pos m).card := by
  intro T
  induction T using Finset.induction_on_max_value (f := o.pos) with
  | empty => intro _ m hm; simp at hm
  | insert a T haT hmax ih =>
    intro hsep m hm hmm
    have hma : m = a := by
      rw [mem_insert] at hm
      rcases hm with rfl | hm
      · rfl
      · exact o.inj (le_antisymm (hmax m hm) (hmm a (mem_insert_self _ _)))
    subst hma
    rw [card_insert_of_notMem haT]
    rcases T.eq_empty_or_nonempty with rfl | hT
    · simp
    obtain ⟨m', hm', hm'max⟩ := T.exists_max_image o.pos hT
    have hm'a : m' ≠ m := fun h => haT (h ▸ hm')
    have hlt : o.pos m' < o.pos m := lt_of_le_of_ne (hmax m' hm') (fun h => hm'a (o.inj h))
    have ih' := ih (fun u hu v hv huv => hsep u (mem_insert_of_mem hu) v (mem_insert_of_mem hv) huv)
      m' hm' hm'max
    have hb := hsep m' (mem_insert_of_mem hm') m (mem_insert_self _ _) hm'a
    unfold betw at hb
    have hdisj : Disjoint ((reps P o B).filter fun r => o.pos r < o.pos m')
        ((reps P o B).filter fun r => (o.pos m' < o.pos r ∧ o.pos r < o.pos m) ∨
          (o.pos m < o.pos r ∧ o.pos r < o.pos m')) := by
      rw [disjoint_filter]; intro r _ h1 h2; omega
    have hsub : ((reps P o B).filter fun r => o.pos r < o.pos m') ∪
        ((reps P o B).filter fun r => (o.pos m' < o.pos r ∧ o.pos r < o.pos m) ∨
          (o.pos m < o.pos r ∧ o.pos r < o.pos m')) ⊆
        (reps P o B).filter fun r => o.pos r < o.pos m := by
      intro r hr
      simp only [mem_union, mem_filter] at hr ⊢
      rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, by omega⟩
      · exact ⟨h1, by omega⟩
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj] at this
    have hT1 : 1 ≤ T.card := card_pos.2 hT
    calc ζ * T.card = ζ * (T.card - 1) + ζ := by
          obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 := ⟨T.card - 1, by omega⟩
          rw [hk]; simp; ring
      _ ≤ _ := by omega

variable (hP : IsSelector G P)
include hP

/-- **Assertion (A1).** If `κ ≥ 1` bounds the growth ratio of `𝒫` on `G`
and the packing ratio of `G`, and `|A| ≥ 6(q+1)`, then `q |S| ≤ |A|`. -/
theorem predamp_card (hκ : 1 ≤ κ)
    (hγ : ∀ B : Finset V, B.Nonempty → numCls (P B) univ ≤ κ * B.card)
    (hβ : IsPackingBound G κ) (hA : 6 * (q + 1) ≤ A.card) :
    q * (predamp G P o A q κ).card ≤ A.card := by
  set S := predamp G P o A q κ
  obtain ⟨S1, S2, S3, hsub, -, -, h1, h2, h3⟩ := pdInv_predamp (o := o) (A := A) (q := q) hP hκ
  set B := A ∪ S
  set R := reps P o B
  have hBne : B.Nonempty := by
    have : A.Nonempty := card_pos.1 (by omega)
    exact this.mono subset_union_left
  have hR : R.card ≤ κ * B.card := by rw [card_reps hP]; exact hγ B hBne
  have hAB : A.card ≤ B.card := card_le_card subset_union_left
  have hBS : B.card ≤ A.card + S.card := card_union_le _ _
  set q' := 3 * (q + 1)
  -- rule 1
  have e1 : q' * S1.card ≤ B.card := by
    have : κ * (q' * S1.card) ≤ κ * B.card := by
      calc κ * (q' * S1.card) = q' * κ * S1.card := by ring
        _ ≤ R.card := h1
        _ ≤ κ * B.card := hR
    exact Nat.le_of_mul_le_mul_left this hκ
  -- rule 2
  have e2 : q' * S2.card ≤ B.card := by
    rcases Nat.lt_or_ge S2.card 2 with hs | hs
    · calc q' * S2.card ≤ q' * 1 := Nat.mul_le_mul_left _ (by omega)
        _ ≤ B.card := by omega
    have hpack := hβ R S2 (q' * κ * κ + 1) hs fun u hu v hv huv => by
      have := h2 u hu v hv huv; omega
    have : κ * κ * (q' * S2.card) ≤ κ * κ * B.card := by
      have hS2 : S2.card * (q' * κ * κ) ≤ κ * R.card := by
        calc S2.card * (q' * κ * κ) ≤ S2.card * (q' * κ * κ + 1) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ κ * R.card := hpack
      calc κ * κ * (q' * S2.card) = S2.card * (q' * κ * κ) := by ring
        _ ≤ κ * R.card := hS2
        _ ≤ κ * (κ * B.card) := Nat.mul_le_mul_left _ hR
        _ = κ * κ * B.card := by ring
    exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos hκ hκ)
  -- rule 3
  have e3 : q' * S3.card ≤ B.card := by
    rcases S3.eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    obtain ⟨m, hm, hmax⟩ := S3.exists_max_image o.pos hne
    have hb := card_mul_le_of_betw (P := P) (o := o) (B := B) S3 h3 m hm hmax
    have hb' : (2 * q' * κ) * (S3.card - 1) ≤ κ * B.card :=
      hb.trans ((card_le_card (filter_subset _ _)).trans hR)
    have : κ * (2 * q' * (S3.card - 1)) ≤ κ * B.card := by
      calc κ * (2 * q' * (S3.card - 1)) = (2 * q' * κ) * (S3.card - 1) := by ring
        _ ≤ κ * B.card := hb'
    have h3' := Nat.le_of_mul_le_mul_left this hκ
    have : 1 ≤ S3.card := card_pos.2 hne
    have hq'S : 2 * q' * (S3.card - 1) + 2 * q' = 2 * (q' * S3.card) := by
      obtain ⟨k, hk⟩ : ∃ k, S3.card = k + 1 := ⟨S3.card - 1, by omega⟩
      rw [hk]; simp; ring
    omega
  have hS : S.card ≤ S1.card + S2.card + S3.card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have : q' * S.card ≤ 3 * B.card := by
    calc q' * S.card ≤ q' * (S1.card + S2.card + S3.card) := Nat.mul_le_mul_left _ hS
      _ = q' * S1.card + q' * S2.card + q' * S3.card := by ring
      _ ≤ 3 * B.card := by omega
  have : 3 * (q + 1) * S.card ≤ 3 * (A.card + S.card) :=
    this.trans (Nat.mul_le_mul_left _ hBS)
  nlinarith

/-- **Assertion (A2).** Every vertex has a representative in `S` at
Hamming distance at most `5 q' κ²`. -/
theorem predamp_near (hκ : 1 ≤ κ) (u : V) :
    ∃ s ∈ predamp G P o A q κ,
      ham G P o (A ∪ predamp G P o A q κ) u s ≤ 5 * (3 * (q + 1)) * κ * κ := by
  have := (predamp_final (o := o) (A := A) (q := q) hP hκ u).2.1
  unfold Rule2 at this
  push Not at this
  exact this

end Size

/-! ### Assertion (A3): the alternation argument -/

section Alternation

/-- `α` bounds the alternation of the ordering `o`. -/
def IsAltBound (G : SimpleGraph V) [DecidableRel G.Adj] (o : VOrder V) (α : ℕ) : Prop :=
  ∀ x, (univ.filter fun a => ∃ b, o.pos b = o.pos a + 1 ∧ x ∈ sdiff G a b).card ≤ α

/-- The `k`-th element of a finite set in the ordering. -/
theorem exists_rank (T : Finset V) {k : ℕ} (hk : k < T.card) :
    ∃ w ∈ T, (T.filter fun z => o.pos z < o.pos w).card = k := by
  set f := fun w => (T.filter fun z => o.pos z < o.pos w).card
  have hmaps : ∀ w ∈ T, f w ∈ range T.card := by
    intro w hw
    refine mem_range.2 (card_lt_card ⟨filter_subset _ _, fun h => ?_⟩)
    have := mem_filter.1 (h hw); omega
  have hinj : Set.InjOn f T := by
    intro w hw w' hw' hff
    by_contra hne
    have key : ∀ a ∈ T, ∀ b ∈ T, o.pos a < o.pos b → f a < f b := by
      intro a ha b hb hab
      refine card_lt_card ⟨fun z hz => ?_, fun h => ?_⟩
      · rw [mem_filter] at hz ⊢; exact ⟨hz.1, by omega⟩
      · have := mem_filter.1 (h (mem_filter.2 ⟨ha, hab⟩)); omega
    rcases lt_or_gt_of_ne (fun h => hne (o.inj h)) with h | h
    · have := key w hw w' hw' h; rw [hff] at this; exact lt_irrefl _ this
    · have := key w' hw' w hw h; rw [hff] at this; exact lt_irrefl _ this
  have hsurj := surj_on_of_inj_on_of_card_le (s := T) (t := range T.card)
    (fun w _ => f w) hmaps (fun a b ha hb h => hinj ha hb h) (by simp)
  obtain ⟨w, hw, hwk⟩ := hsurj k (mem_range.2 hk)
  exact ⟨w, hw, hwk.symm⟩

theorem card_above (T : Finset V) {w : V} (hw : w ∈ T) :
    (T.filter fun z => o.pos w < o.pos z).card + (T.filter fun z => o.pos z < o.pos w).card + 1 =
      T.card := by
  have h1 := card_filter_add_card_filter_not (s := T) (fun z => o.pos w < o.pos z)
  have h2 := card_filter_add_card_filter_not (s := T.filter fun z => ¬ o.pos w < o.pos z)
    (fun z => o.pos z < o.pos w)
  have h3 : (T.filter fun z => ¬ o.pos w < o.pos z).filter (fun z => o.pos z < o.pos w) =
      T.filter fun z => o.pos z < o.pos w := by
    ext z; simp only [mem_filter]; constructor
    · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨h, by omega⟩, h'⟩
  have h4 : (T.filter fun z => ¬ o.pos w < o.pos z).filter (fun z => ¬ o.pos z < o.pos w) = {w} := by
    ext z; simp only [mem_filter, mem_singleton]; constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact o.inj (by omega)
    · rintro rfl; exact ⟨⟨hw, by omega⟩, by omega⟩
  rw [h3, h4, card_singleton] at h2
  omega

/-- Along a stretch of the ordering without boundary pairs for `x`,
adjacency to `x` is constant and `x` does not occur, unless the stretch
is a single vertex. -/
theorem segment {x : V} :
    ∀ (d : ℕ) (y y' : V), o.pos y' = o.pos y + d →
      (∀ a, o.pos y ≤ o.pos a → o.pos a < o.pos y' → ∀ b, o.pos b = o.pos a + 1 →
        x ∉ sdiff G a b) →
      (y = y' ∨ (y ≠ x ∧ y' ≠ x)) ∧ (G.Adj x y ↔ G.Adj x y') := by
  intro d
  induction d with
  | zero => intro y y' h _; obtain rfl := o.inj (by omega); exact ⟨Or.inl rfl, Iff.rfl⟩
  | succ d ih =>
    intro y y' h hseg
    obtain ⟨a, ha⟩ := o.dense y' (o.pos y + d) (by omega)
    obtain ⟨h1, h2⟩ := ih y a ha fun a' h1 h2 b hb => hseg a' h1 (by omega) b hb
    have hx := hseg a (by omega) (by omega) y' (by omega)
    have hay' : a ≠ y' := fun h' => by rw [h'] at ha; omega
    rw [mem_sdiff] at hx
    push Not at hx
    obtain ⟨hxa, hxy', hadj⟩ := hx hay'
    refine ⟨Or.inr ⟨?_, Ne.symm hxy'⟩, h2.trans ?_⟩
    · rcases h1 with rfl | ⟨h, -⟩
      · exact Ne.symm hxa
      · exact h
    · rw [G.adj_comm x a, G.adj_comm x y']; exact hadj

variable {A : Finset V} {q κ : ℕ} (hP : IsSelector G P)
include hP

/-- **Assertion (A3).** Two vertices with the same atomic type over the
output are at Hamming distance at most `(4α+3) ζ + 2`. -/
theorem predamp_same_type (hκ : 1 ≤ κ) {α : ℕ} (hα : IsAltBound G o α) {u v : V}
    (huv : tpRel G (predamp G P o A q κ) 0 u v) :
    ham G P o (A ∪ predamp G P o A q κ) u v ≤ (4 * α + 3) * (2 * (3 * (q + 1)) * κ) + 2 := by
  set S := predamp G P o A q κ
  set ζ := 2 * (3 * (q + 1)) * κ
  set B := A ∪ S
  set R := reps P o B
  by_cases hue : u = v
  · subst hue; rw [ham_eq_numCls hP, sdiff_self]; simp [numCls]
  have huS : u ∉ S := fun h => hue (eq_of_tpRel_of_mem huv h)
  have hvS : v ∉ S := fun h =>
    hue (eq_of_tpRel_of_mem ((tpRel_isEquiv S 0).symm _ _ huv) h).symm
  -- no vertex of `S` lies in `Δ[u,v]`
  have hSd : ∀ s ∈ S, s ∉ sdiff G u v := by
    intro s hs hsd
    have hsu : s ≠ u := fun h => huS (h ▸ hs)
    have hsv : s ≠ v := fun h => hvS (h ▸ hs)
    rw [mem_sdiff_of_ne G hue hsu hsv] at hsd
    exact hsd (adj_iff_of_tpRel huv hs)
  have hfin := predamp_final (o := o) (A := A) (q := q) hP hκ
  by_contra hbig
  push Not at hbig
  set Z := R.filter fun r => r ∈ sdiff G u v ∧ r ≠ u ∧ r ≠ v
  have hle : ham G P o B u v ≤ 2 + crossCnt G P o B u + crossCnt G P o B v + Z.card :=
    ham_le (o := o) hP B u v
  have hcu : crossCnt G P o B u ≤ 3 * (q + 1) * κ := not_lt.1 (hfin u).1
  have hcv : crossCnt G P o B v ≤ 3 * (q + 1) * κ := not_lt.1 (hfin v).1
  have hZ : (2 * α + 1) * (2 * ζ) < Z.card := by
    have hζ : 2 * (3 * (q + 1) * κ) = ζ := by simp only [ζ]; ring
    have e1 : (2 * α + 1) * (2 * ζ) + ζ = (4 * α + 3) * ζ := by ring
    omega
  -- boundary pairs for `u` or `v`
  set Bd := univ.filter fun a => ∃ b, o.pos b = o.pos a + 1 ∧ (u ∈ sdiff G a b ∨ v ∈ sdiff G a b)
  have hBd : Bd.card ≤ 2 * α := by
    have : Bd ⊆ (univ.filter fun a => ∃ b, o.pos b = o.pos a + 1 ∧ u ∈ sdiff G a b) ∪
        (univ.filter fun a => ∃ b, o.pos b = o.pos a + 1 ∧ v ∈ sdiff G a b) := by
      intro a ha
      obtain ⟨b, hb, hb'⟩ := (mem_filter.1 ha).2
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases hb' with h | h
      · exact Or.inl ⟨b, hb, h⟩
      · exact Or.inr ⟨b, hb, h⟩
    have := (card_le_card this).trans (card_union_le _ _)
    have := hα u; have := hα v; omega
  set chunk := fun z => (Bd.filter fun a => o.pos a < o.pos z).card
  have hchunk : ∀ z ∈ Z, chunk z ∈ range (2 * α + 1) := fun z _ =>
    mem_range.2 (Nat.lt_succ_of_le ((card_le_card (filter_subset _ _)).trans hBd))
  obtain ⟨c0, -, hc0⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hchunk
    (by rw [card_range]; exact hZ)
  set Zc := Z.filter fun z => chunk z = c0
  -- no boundary between two vertices of the same chunk
  have hnob : ∀ y y', chunk y = chunk y' → o.pos y ≤ o.pos y' →
      ∀ a, o.pos y ≤ o.pos a → o.pos a < o.pos y' → a ∉ Bd := by
    intro y y' hyy' hle' a h1 h2 ha
    have hsub : (Bd.filter fun a' => o.pos a' < o.pos y) ⊆ (Bd.filter fun a' => o.pos a' < o.pos y') :=
      fun a' h' => by rw [mem_filter] at h' ⊢; exact ⟨h'.1, by omega⟩
    have hss : (Bd.filter fun a' => o.pos a' < o.pos y) ⊂ (Bd.filter fun a' => o.pos a' < o.pos y') :=
      ⟨hsub, fun h => by have := mem_filter.1 (h (mem_filter.2 ⟨ha, h2⟩)); omega⟩
    have := card_lt_card hss
    simp only [chunk] at hyy'; omega
  have hseg : ∀ y y', chunk y = chunk y' → o.pos y ≤ o.pos y' →
      ((y = y' ∨ (y ≠ u ∧ y' ≠ u)) ∧ (G.Adj u y ↔ G.Adj u y')) ∧
      ((y = y' ∨ (y ≠ v ∧ y' ≠ v)) ∧ (G.Adj v y ↔ G.Adj v y')) := by
    intro y y' hc hle'
    have nb := hnob y y' hc hle'
    refine ⟨segment (G := G) (o := o) (o.pos y' - o.pos y) y y' (by omega) fun a h1 h2 b hb hu => ?_,
      segment (G := G) (o := o) (o.pos y' - o.pos y) y y' (by omega) fun a h1 h2 b hb hv => ?_⟩
    · exact nb a h1 h2 (mem_filter.2 ⟨mem_univ _, b, hb, Or.inl hu⟩)
    · exact nb a h1 h2 (mem_filter.2 ⟨mem_univ _, b, hb, Or.inr hv⟩)
  -- a vertex in the stretch of a point of `Zc` lies in `Δ[u,v]`
  have hin : ∀ z ∈ Zc, ∀ y, chunk y = c0 → y ∈ sdiff G u v := by
    intro z hz y hy
    obtain ⟨hzZ, hzc⟩ := mem_filter.1 hz
    obtain ⟨-, hzd, hzu, hzv⟩ := mem_filter.1 hzZ
    rw [mem_sdiff_of_ne G hue hzu hzv] at hzd
    rcases le_total (o.pos z) (o.pos y) with h | h
    · obtain ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩ := hseg z y (hzc.trans hy.symm) h
      have hyu : y ≠ u := by rcases hu1 with rfl | ⟨-, h⟩; exact hzu; exact h
      have hyv : y ≠ v := by rcases hv1 with rfl | ⟨-, h⟩; exact hzv; exact h
      rw [mem_sdiff_of_ne G hue hyu hyv, ← hu2, ← hv2]; exact hzd
    · obtain ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩ := hseg y z (hy.trans hzc.symm) h
      have hyu : y ≠ u := by rcases hu1 with rfl | ⟨h, -⟩; exact hzu; exact h
      have hyv : y ≠ v := by rcases hv1 with rfl | ⟨h, -⟩; exact hzv; exact h
      rw [mem_sdiff_of_ne G hue hyu hyv, hu2, hv2]; exact hzd
  -- the median point of `Zc`
  obtain ⟨w, hw, hwk⟩ := exists_rank (o := o) Zc (k := ζ) (by omega)
  have habove := card_above (o := o) Zc hw
  have hwc : chunk w = c0 := (mem_filter.1 hw).2
  apply (hfin w).2.2
  intro s hs
  have hsd := hSd s hs
  have hsw : o.pos s ≠ o.pos w := fun h => hsd (by
    rw [o.inj h]; exact hin w hw w hwc)
  unfold betw
  rcases lt_or_gt_of_ne hsw with hlt | hgt
  · -- `s` comes before `w`: the `ζ` points of `Zc` before `w` lie after `s`
    refine le_trans (le_of_eq hwk.symm) (card_le_card fun z hz => ?_)
    obtain ⟨hzZc, hzw⟩ := mem_filter.1 hz
    obtain ⟨hzZ, hzc⟩ := mem_filter.1 hzZc
    refine mem_filter.2 ⟨(mem_filter.1 hzZ).1, Or.inr ⟨?_, hzw⟩⟩
    by_contra hzs; push Not at hzs
    -- `s` lies in the stretch from `z` to `w`
    have hsc : chunk s = c0 := by
      have hsub1 : (Bd.filter fun a => o.pos a < o.pos z) ⊆ (Bd.filter fun a => o.pos a < o.pos s) :=
        fun a h' => by rw [mem_filter] at h' ⊢; exact ⟨h'.1, by omega⟩
      have hsub2 : (Bd.filter fun a => o.pos a < o.pos s) ⊆ (Bd.filter fun a => o.pos a < o.pos w) :=
        fun a h' => by rw [mem_filter] at h' ⊢; exact ⟨h'.1, by omega⟩
      have := card_le_card hsub1; have := card_le_card hsub2
      simp only [chunk] at hzc hwc ⊢; omega
    exact hsd (hin w hw s hsc)
  · -- `s` comes after `w`
    have hge : ζ ≤ (Zc.filter fun z => o.pos w < o.pos z).card := by
      have : ζ + ζ < Zc.card := by omega
      omega
    refine hge.trans (card_le_card fun z hz => ?_)
    obtain ⟨hzZc, hzw⟩ := mem_filter.1 hz
    obtain ⟨hzZ, hzc⟩ := mem_filter.1 hzZc
    refine mem_filter.2 ⟨(mem_filter.1 hzZ).1, Or.inl ⟨hzw, ?_⟩⟩
    by_contra hzs; push Not at hzs
    rcases eq_or_lt_of_le hzs with heq | hlt'
    · exact hsd (by rw [o.inj heq]; exact hin w hw z hzc)
    have hsc : chunk s = c0 := by
      have hsub1 : (Bd.filter fun a => o.pos a < o.pos w) ⊆ (Bd.filter fun a => o.pos a < o.pos s) :=
        fun a h' => by rw [mem_filter] at h' ⊢; exact ⟨h'.1, by omega⟩
      have hsub2 : (Bd.filter fun a => o.pos a < o.pos s) ⊆ (Bd.filter fun a => o.pos a < o.pos z) :=
        fun a h' => by rw [mem_filter] at h' ⊢; exact ⟨h'.1, by omega⟩
      have := card_le_card hsub1; have := card_le_card hsub2
      simp only [chunk] at hzc hwc ⊢; omega
    exact hsd (hin w hw s hsc)

end Alternation

end Lax185574Proofs.Chain
