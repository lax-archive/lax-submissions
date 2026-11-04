import Lax185574Proofs.Chain.Sampling

/-!
Vertex orderings with low alternation, after Welzl and Bonnet, Duron,
Sylvester and Zamaraev (`thm:alternation-general` of the companion paper,
with the algorithm of its appendix `app:welzl`).

The greedy procedure keeps a set of active vertices and a weight `w(x)`
for every vertex. In each step it picks two active vertices `u > v` that
minimize the total weight `ξ(u,v)` of the vertices `x` whose closed
neighborhood contains exactly one of them, records the step `(u,v)`,
deactivates `u` and doubles the weight of every such `x`. The steps form a
spanning tree. The ordering is obtained from the last active vertex by
inserting `u` right after `v`, for the steps from the last to the first.

Every vertex `x` crosses at most `2K(x)` consecutive pairs of the
ordering, where `K(x)` is the number of steps it crosses, and
`w(x) = 2^{K(x)}`. If the atomic types of `G` grow with ratio `γ`, the
weighted sampling lemma gives a pair with `m ξ ≤ s W` among `m` active
vertices, where `W` is the total weight and `s = 4γ(log₂ n + 1)`. The
potential `W m^s` never increases, so the final total weight is at most
`n^{s+1}` and the alternation is at most `2(s+1)(log₂ n + 1) + 2`.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]

section Defs

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `x` crosses the pair `u v`: its closed neighborhood contains exactly
one of `u` and `v`. -/
def CrossesPair (x u v : V) : Prop := ¬ ((x = u ∨ G.Adj x u) ↔ (x = v ∨ G.Adj x v))

instance (x u v : V) : Decidable (CrossesPair G x u v) := by
  unfold CrossesPair; infer_instance

/-- The weight `ξ(u,v)` of the vertices crossing `u v`. -/
def xi (w : V → ℕ) (u v : V) : ℕ := ∑ x ∈ univ.filter (CrossesPair G · u v), w x

/-- The state of the greedy procedure: active vertices, weights, and the
steps `(u, v)` taken so far, the most recent first. -/
structure WState (V : Type u) where
  active : Finset V
  w : V → ℕ
  steps : List (V × V)

/-- The candidate pairs `(u, v)` with `v < u`, both active, in
lexicographic order. -/
def candPairs (A : Finset V) : List (V × V) :=
  ((univ : Finset V).sort (· ≤ ·)).flatMap fun u =>
    ((univ : Finset V).sort (· ≤ ·)).filterMap fun v =>
      if v < u ∧ u ∈ A ∧ v ∈ A then some (u, v) else none

/-- One greedy step: pick a candidate pair of minimum weight (the first
one in lexicographic order), deactivate `u`, and double the weights of
the vertices crossing the pair. -/
def welzlStep (st : WState V) : WState V :=
  match (candPairs st.active).argmin (fun p => xi G st.w p.1 p.2) with
  | none => st
  | some p =>
    { active := st.active.erase p.1
      w := fun x => if CrossesPair G x p.1 p.2 then 2 * st.w x else st.w x
      steps := p :: st.steps }

/-- Iterate the greedy step. -/
def welzlRun : ℕ → WState V → WState V
  | 0, st => st
  | f + 1, st => welzlRun f (welzlStep G st)

/-- The final state of the greedy procedure, started with all vertices
active and all weights one. -/
def welzlTree : WState V :=
  welzlRun G (Fintype.card V) ⟨univ, fun _ => 1, []⟩

/-- Insert `u` right after the first occurrence of `v`. -/
def insertAfter (v u : V) : List V → List V
  | [] => [u]
  | a :: l => if a = v then a :: u :: l else a :: insertAfter v u l

/-- The Welzl ordering of `G`, as a list of all vertices. -/
def welzlOrder : List V :=
  (welzlTree G).steps.foldl (fun l p => insertAfter p.2 p.1 l)
    ((welzlTree G).active.sort (· ≤ ·))

/-- The number of consecutive pairs of `l` crossed by `x`. -/
def crossCount (x : V) : List V → ℕ
  | a :: b :: l => (if CrossesPair G x a b then 1 else 0) + crossCount x (b :: l)
  | _ => 0

/-- The number of consecutive pairs `a b` of `l` with `x ∈ Δ[a,b]`. -/
def altCount (x : V) : List V → ℕ
  | a :: b :: l => (if x ∈ sdiff G a b then 1 else 0) + altCount x (b :: l)
  | _ => 0

/-- The alternation of the ordering `l`. -/
def alternation (l : List V) : ℕ := univ.sup fun x => altCount G x l

end Defs

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Crossing and alternation of lists -/

theorem crossesPair_comm {x u v : V} : CrossesPair G x u v ↔ CrossesPair G x v u := by
  unfold CrossesPair; constructor <;> intro h h' <;> exact h h'.symm

theorem crossesPair_triangle {x a b c : V} (h : CrossesPair G x a c) :
    CrossesPair G x a b ∨ CrossesPair G x b c := by
  unfold CrossesPair at *; by_contra h'; push Not at h'; exact h (h'.1.trans h'.2)

theorem insertAfter_cons_head (v u b : V) (r : List V) :
    ∃ r', insertAfter v u (b :: r) = b :: r' := by
  unfold insertAfter; split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem mem_insertAfter {v u x : V} {l : List V} :
    x ∈ insertAfter v u l ↔ x = u ∨ x ∈ l := by
  induction l with
  | nil => simp [insertAfter]
  | cons a l ih =>
    unfold insertAfter; split_ifs <;> simp [ih] <;> tauto

theorem nodup_insertAfter {v u : V} {l : List V} (hl : l.Nodup) (hu : u ∉ l) :
    (insertAfter v u l).Nodup := by
  induction l with
  | nil => simp [insertAfter]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.mem_cons, not_or] at hu
    unfold insertAfter; split_ifs
    · simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨Ne.symm hu.1, hl.1⟩, hu.2, hl.2⟩
    · rw [List.nodup_cons, mem_insertAfter]
      exact ⟨by rintro (h | h); exact hu.1 h.symm; exact hl.1 h, ih hl.2 hu.2⟩

theorem crossCount_insertAfter (x : V) {v u : V} {l : List V} (hv : v ∈ l) :
    crossCount G x (insertAfter v u l) ≤
      crossCount G x l + 2 * (if CrossesPair G x u v then 1 else 0) := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    by_cases hav : a = v
    · subst hav
      rw [show insertAfter a u (a :: l) = a :: u :: l by simp [insertAfter]]
      cases l with
      | nil =>
        simp only [crossCount]; split_ifs <;> simp_all [crossesPair_comm]
      | cons b r =>
        simp only [crossCount]
        have htri : CrossesPair G x u b → CrossesPair G x u a ∨ CrossesPair G x a b :=
          crossesPair_triangle
        have hc : CrossesPair G x a u ↔ CrossesPair G x u a := crossesPair_comm
        by_cases h1 : CrossesPair G x u a <;> by_cases h2 : CrossesPair G x a b <;>
          by_cases h3 : CrossesPair G x u b <;> simp_all <;> omega
    · rw [show insertAfter v u (a :: l) = a :: insertAfter v u l by simp [insertAfter, hav]]
      have hv' : v ∈ l := by
        rcases List.mem_cons.1 hv with h | h
        · exact absurd h.symm hav
        · exact h
      cases l with
      | nil => simp at hv'
      | cons b r =>
        obtain ⟨r', hr'⟩ := insertAfter_cons_head v u b r
        have := ih hv'
        rw [hr'] at this ⊢
        simp only [crossCount] at this ⊢
        omega

theorem crossCount_le_one_length {x : V} {l : List V} (hl : l.length ≤ 1) :
    crossCount G x l = 0 := by
  match l, hl with
  | [], _ => rfl
  | [_], _ => rfl

/-- `x ∉ {a,b}` lies in `Δ[a,b]` exactly when it crosses `a b`. -/
theorem mem_sdiff_iff_crossesPair {x a b : V} (hab : a ≠ b) (ha : x ≠ a) (hb : x ≠ b) :
    x ∈ sdiff G a b ↔ CrossesPair G x a b := by
  rw [mem_sdiff_of_ne G hab ha hb]
  unfold CrossesPair
  simp only [ha, hb, false_or, G.adj_comm x]

theorem altCount_le (x : V) {l : List V} (hl : l.Nodup) :
    altCount G x l ≤ crossCount G x l +
      (if x ∈ l then (if l.head? = some x then 1 else 2) else 0) := by
  induction l with
  | nil => simp [altCount, crossCount]
  | cons a l ih =>
    cases l with
    | nil => simp [altCount]
    | cons b r =>
      rw [List.nodup_cons] at hl
      have ih := ih hl.2
      simp only [altCount, crossCount]
      have hab : a ≠ b := fun h => hl.1 (h ▸ List.mem_cons_self)
      by_cases hxa : x = a
      · subst hxa
        have : x ∉ b :: r := hl.1
        simp only [this, if_false, add_zero] at ih
        have h1 : (if x ∈ sdiff G x b then 1 else 0) ≤ 1 := by split_ifs <;> simp
        simp only [List.mem_cons_self, if_true, List.head?_cons]
        omega
      by_cases hxb : x = b
      · subst hxb
        simp only [List.mem_cons_self, if_true, List.head?_cons] at ih
        have h1 : (if x ∈ sdiff G a x then 1 else 0) ≤ 1 := by split_ifs <;> simp
        have : x ∈ a :: x :: r := by simp
        simp only [this, if_true, List.head?_cons, Option.some.injEq, Ne.symm hxa, if_false]
        omega
      · have hiff := mem_sdiff_iff_crossesPair (G := G) hab hxa hxb
        have hite : (if x ∈ sdiff G a b then 1 else 0) = (if CrossesPair G x a b then 1 else 0) := by
          by_cases h : CrossesPair G x a b <;> simp [h, hiff]
        rw [hite]
        have hmem : x ∈ a :: b :: r ↔ x ∈ r := by simp [hxa, hxb]
        have hmem' : x ∈ b :: r ↔ x ∈ r := by simp [hxb]
        simp only [hmem, hmem', List.head?_cons, Option.some.injEq, Ne.symm hxa,
          Ne.symm hxb, if_false] at ih ⊢
        split_ifs at ih ⊢ <;> omega

/-! ### Invariants of the greedy procedure -/

/-- The steps, most recent first, are consistent with the active set:
every step `(u, v)` has `u` inactive and `v` active right after it. -/
def ValidSteps : Finset V → List (V × V) → Prop
  | _, [] => True
  | A, p :: rest => p.1 ∉ A ∧ p.2 ∈ A ∧ ValidSteps (insert p.1 A) rest

/-- The number of steps crossed by `x`. -/
def stepCross (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (steps : List (V × V)) : ℕ :=
  steps.countP fun p => CrossesPair G x p.1 p.2

theorem stepCross_cons (x : V) (p : V × V) (steps : List (V × V)) :
    stepCross G x (p :: steps) = stepCross G x steps + (if CrossesPair G x p.1 p.2 then 1 else 0) := by
  unfold stepCross; rw [List.countP_cons]; simp

/-- Folding the insertions over valid steps. -/
theorem fold_spec : ∀ (steps : List (V × V)) (A : Finset V) (l : List V),
    ValidSteps A steps → l.Nodup → (∀ x, x ∈ l ↔ x ∈ A) →
    let l' := steps.foldl (fun l p => insertAfter p.2 p.1 l) l
    l'.Nodup ∧ (∀ x, x ∈ l' ↔ x ∈ A ∨ x ∈ steps.map Prod.fst) ∧
      ∀ x, crossCount G x l' ≤ crossCount G x l + 2 * stepCross G x steps
  | [], A, l, _, hl, hA => by simpa [stepCross] using ⟨hl, hA⟩
  | p :: rest, A, l, hv, hl, hA => by
    obtain ⟨hu, hvA, hrest⟩ := hv
    have hl' : (insertAfter p.2 p.1 l).Nodup := nodup_insertAfter hl (fun h => hu ((hA _).1 h))
    have hA' : ∀ x, x ∈ insertAfter p.2 p.1 l ↔ x ∈ insert p.1 A := by
      intro x; rw [mem_insertAfter, hA, mem_insert]
    obtain ⟨h1, h2, h3⟩ := fold_spec rest (insert p.1 A) _ hrest hl' hA'
    refine ⟨h1, fun x => ?_, fun x => ?_⟩
    · simp only [List.foldl_cons, List.map_cons, List.mem_cons] at h2 ⊢
      rw [h2, mem_insert]; tauto
    · simp only [List.foldl_cons]
      refine (h3 x).trans ?_
      have := crossCount_insertAfter (G := G) x (u := p.1) ((hA p.2).2 hvA)
      rw [stepCross_cons]
      split_ifs at this ⊢ <;> omega

theorem argmin_candPairs {A : Finset V} {w : V → ℕ} {p : V × V}
    (h : (candPairs A).argmin (fun p => xi G w p.1 p.2) = some p) :
    p.2 < p.1 ∧ p.1 ∈ A ∧ p.2 ∈ A ∧
      ∀ u ∈ A, ∀ v ∈ A, v < u → xi G w p.1 p.2 ≤ xi G w u v := by
  have hmem := List.argmin_mem h
  simp only [candPairs, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq] at hmem
  obtain ⟨u, -, v, -, ⟨hvu, hu, hv⟩, rfl⟩ := hmem
  refine ⟨hvu, hu, hv, fun u' hu' v' hv' hvu' => ?_⟩
  have : (u', v') ∈ candPairs A := by
    simp only [candPairs, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, Finset.mem_sort, mem_univ, true_and]
    exact ⟨u', v', ⟨hvu', hu', hv'⟩, rfl⟩
  exact List.le_of_mem_argmin this h

theorem argmin_candPairs_none {A : Finset V} {w : V → ℕ}
    (h : (candPairs A).argmin (fun p => xi G w p.1 p.2) = none) : A.card ≤ 1 := by
  rw [List.argmin_eq_none] at h
  by_contra hc
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (show 1 < A.card by omega)
  have : (max a b, min a b) ∈ candPairs A := by
    simp only [candPairs, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, Finset.mem_sort, mem_univ, true_and]
    refine ⟨max a b, min a b, ⟨?_, ?_, ?_⟩, rfl⟩
    · rcases lt_or_gt_of_ne hab with h | h
      · simp [max_eq_right h.le, min_eq_left h.le, h]
      · simp [max_eq_left h.le, min_eq_right h.le, h]
    · rcases le_total a b with h | h
      · simpa [max_eq_right h] using hb
      · simpa [max_eq_left h] using ha
    · rcases le_total a b with h | h
      · simpa [min_eq_left h] using ha
      · simpa [min_eq_right h] using hb
  rw [h] at this; simp at this

/-- The structural invariant of the greedy procedure. -/
structure WInv (st : WState V) : Prop where
  cover : ∀ x, x ∈ st.active ∨ x ∈ st.steps.map Prod.fst
  valid : ValidSteps st.active st.steps
  weight : ∀ x, st.w x = 2 ^ stepCross G x st.steps

theorem winv_step {st : WState V} (h : WInv (G := G) st) : WInv (G := G) (welzlStep G st) := by
  unfold welzlStep
  split
  · exact h
  · rename_i p hp
    obtain ⟨hvu, hu, hv, -⟩ := argmin_candPairs hp
    refine ⟨fun x => ?_, ?_, fun x => ?_⟩
    · rcases h.cover x with hx | hx
      · by_cases hxu : x = p.1
        · right; simp [hxu]
        · left; exact mem_erase.2 ⟨hxu, hx⟩
      · right; simp only [List.map_cons, List.mem_cons]; exact Or.inr hx
    · refine ⟨notMem_erase _ _, mem_erase.2 ⟨ne_of_lt hvu, hv⟩, ?_⟩
      rw [insert_erase hu]; exact h.valid
    · simp only [stepCross_cons, h.weight x]
      split_ifs <;> ring

theorem winv_run (f : ℕ) {st : WState V} (h : WInv (G := G) st) : WInv (G := G) (welzlRun G f st) := by
  induction f generalizing st with
  | zero => exact h
  | succ f ih => exact ih (winv_step h)

theorem active_card_run (f : ℕ) (st : WState V) :
    (welzlRun G f st).active.card ≤ max 1 (st.active.card - f) := by
  induction f generalizing st with
  | zero => simp [welzlRun]
  | succ f ih =>
    refine (ih (welzlStep G st)).trans ?_
    unfold welzlStep
    split
    · rename_i hnone
      have := argmin_candPairs_none hnone
      omega
    · rename_i p hp
      obtain ⟨-, hu, -, -⟩ := argmin_candPairs hp
      simp only [card_erase_of_mem hu]
      omega

theorem winv_init : WInv (G := G) ⟨univ, fun _ => 1, []⟩ :=
  ⟨fun x => Or.inl (mem_univ x), trivial, fun x => by simp [stepCross]⟩

theorem welzlTree_inv : WInv (G := G) (welzlTree G) := winv_run _ winv_init

theorem welzlTree_active_card : (welzlTree G).active.card ≤ 1 := by
  have := active_card_run (G := G) (Fintype.card V) ⟨univ, fun _ => 1, []⟩
  simp only [card_univ, Nat.sub_self] at this
  unfold welzlTree; omega

/-- The Welzl ordering lists every vertex exactly once, and every vertex
crosses at most twice as many of its consecutive pairs as steps. -/
theorem welzlOrder_spec :
    (welzlOrder G).Nodup ∧ (∀ x, x ∈ welzlOrder G) ∧
      ∀ x, crossCount G x (welzlOrder G) ≤ 2 * stepCross G x (welzlTree G).steps := by
  have hinv := welzlTree_inv (G := G)
  obtain ⟨h1, h2, h3⟩ := fold_spec (G := G) (welzlTree G).steps (welzlTree G).active
    ((welzlTree G).active.sort (· ≤ ·)) hinv.valid (sort_nodup _ _) (fun x => mem_sort _)
  refine ⟨h1, fun x => (h2 x).2 (hinv.cover x), fun x => (h3 x).trans ?_⟩
  rw [crossCount_le_one_length (by rw [length_sort]; exact welzlTree_active_card)]
  omega

theorem welzlOrder_nodup : (welzlOrder G).Nodup := welzlOrder_spec.1

theorem mem_welzlOrder (x : V) : x ∈ welzlOrder G := welzlOrder_spec.2.1 x

/-! ### The potential argument -/

/-- The crossing set of a pair lies in its closed symmetric difference. -/
theorem crossing_subset_sdiff {u v : V} (huv : u ≠ v) :
    univ.filter (CrossesPair G · u v) ⊆ sdiff G u v := by
  intro x hx
  rw [mem_filter] at hx
  by_cases hxu : x = u
  · subst hxu; exact self_mem_sdiff G huv
  by_cases hxv : x = v
  · subst hxv; rw [sdiff_comm]; exact self_mem_sdiff G (Ne.symm huv)
  exact (mem_sdiff_iff_crossesPair huv hxu hxv).2 hx.2

theorem xi_comm (w : V → ℕ) (u v : V) : xi G w u v = xi G w v u := by
  unfold xi; congr 1; ext x; simp [crossesPair_comm]

theorem xi_le_total (w : V → ℕ) (u v : V) : xi G w u v ≤ ∑ x, w x :=
  sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _

/-- **One greedy step is cheap.** Among `m ≥ 2` active vertices some pair
`v < u` has `m ξ(u,v) ≤ s W`, where `s = 4γ(log₂ n + 1)`. -/
theorem exists_cheap_pair {γ : ℕ}
    (hγ : ∀ Y : Finset V, Y.Nonempty → numCls (tpRel G Y 0) univ ≤ γ * Y.card)
    (w : V → ℕ) (hw : ∀ x, 1 ≤ w x) (A : Finset V) (hA : 2 ≤ A.card) :
    ∃ u ∈ A, ∃ v ∈ A, v < u ∧
      A.card * xi G w u v ≤ 4 * γ * (Nat.log 2 (Fintype.card V) + 1) * ∑ x, w x := by
  set L := 2 * (Nat.log 2 (Fintype.card V) + 1)
  set s := 4 * γ * (Nat.log 2 (Fintype.card V) + 1)
  set W := ∑ x, w x
  set m := A.card
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (show 1 < A.card by omega)
  have hpair : ∃ u ∈ A, ∃ v ∈ A, v < u := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨b, hb, a, ha, h⟩
    · exact ⟨a, ha, b, hb, h⟩
  by_contra hne
  push Not at hne
  -- all pairs are expensive
  have hall : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → s * W < m * xi G w u v := by
    intro u hu v hv huv
    rcases lt_or_gt_of_ne huv with h | h
    · rw [xi_comm]; exact hne v hv u hu h
    · exact hne u hu v hv h
  have hms : s < m := by
    obtain ⟨u, hu, v, hv, hvu⟩ := hpair
    have h1 := hall u hu v hv (ne_of_gt hvu)
    have h2 : m * xi G w u v ≤ m * W := Nat.mul_le_mul_left _ (xi_le_total w u v)
    by_contra hsm; push Not at hsm
    have : m * W ≤ s * W := Nat.mul_le_mul_right _ hsm
    omega
  have hWpos : 0 < W := by
    have : w a ≤ W := single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_univ a)
    have := hw a; omega
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · obtain ⟨u, hu, v, hv, hvu⟩ := hpair
      have := hall u hu v hv (ne_of_gt hvu)
      rw [h, zero_mul] at this
      have hγ1 : 1 ≤ γ := by
        have h := hγ {a} (singleton_nonempty a)
        have : 1 ≤ numCls (tpRel G {a} 0) univ :=
          card_pos.2 ⟨_, mem_image_of_mem _ (mem_univ a)⟩
        simp at h; omega
      simp only [s] at h; positivity
    · exact h
  have hk1 := Nat.div_add_mod (m + s - 1) s
  have hk2 := Nat.mod_lt (m + s - 1) hspos
  generalize hkdef : (m + s - 1) / s = k at hk1
  have hmk : m ≤ s * k := by omega
  have hk1' : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hmk; omega
    · exact h
  have hmain := card_le_of_separated (G := G) hγ w A (fun u v => univ.filter (CrossesPair G · u v))
    (fun u _ v _ huv => crossing_subset_sdiff huv) (δ := (s * W : ℝ) / m)
    (by have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
        positivity)
    (fun u hu v hv huv => by
      have := hall u hu v hv huv
      have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      rw [div_le_iff₀ hm]
      have : ((s * W : ℕ) : ℝ) < (m * xi G w u v : ℕ) := by exact_mod_cast this
      push_cast at this
      unfold xi at this; push_cast at this
      linarith)
    (k := k) (L := L) hk1' (by omega)
    (by
      have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have : ((m * W : ℕ) : ℝ) ≤ ((s * k) * W : ℕ) := by
        exact_mod_cast Nat.mul_le_mul_right _ hmk
      push_cast at this
      rw [mul_div_assoc', le_div_iff₀ hm]
      have hW : (W : ℝ) = ∑ x, (w x : ℝ) := by simp [W]
      rw [← hW]; nlinarith)
    ((Nat.mul_le_mul (card_le_univ A) (card_le_univ A)).trans_lt (sq_lt_two_pow _))
  -- `m ≤ γ k L` contradicts `s < m`
  have hsL : s = 2 * γ * L := by simp only [s, L]; ring
  have h2m : 2 * m ≤ s * k := by
    calc 2 * m ≤ 2 * (γ * (k * L)) := by omega
      _ = s * k := by rw [hsL]; ring
  omega

/-- Bernoulli: `(m - 1)^s (m + s) ≤ m^{s+1}` for `m ≥ 1`. -/
theorem pow_mul_add_le (m s : ℕ) (hm : 1 ≤ m) : (m - 1) ^ s * (m + s) ≤ m ^ (s + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction s with
  | zero => simp
  | succ s ih =>
    calc a ^ (s + 1) * (a + 1 + (s + 1)) = a * (a ^ s * (a + 1 + s)) + a ^ (s + 1) := by ring
      _ ≤ a * (a + 1) ^ (s + 1) + a ^ (s + 1) := by
          have := Nat.mul_le_mul_left a ih; omega
      _ ≤ a * (a + 1) ^ (s + 1) + (a + 1) ^ (s + 1) :=
          Nat.add_le_add_left (Nat.pow_le_pow_left (Nat.le_succ a) _) _
      _ = (a + 1) ^ (s + 1 + 1) := by ring

/-- The potential `W · m^s` of a state, with `m` active vertices. -/
theorem potential_step {γ : ℕ}
    (hγ : ∀ Y : Finset V, Y.Nonempty → numCls (tpRel G Y 0) univ ≤ γ * Y.card)
    {st : WState V} (hw : ∀ x, 1 ≤ st.w x) :
    let s := 4 * γ * (Nat.log 2 (Fintype.card V) + 1)
    (∀ x, 1 ≤ (welzlStep G st).w x) ∧
      (∑ x, (welzlStep G st).w x) * (welzlStep G st).active.card ^ s ≤
        (∑ x, st.w x) * st.active.card ^ s := by
  intro s
  unfold welzlStep
  split
  · exact ⟨hw, le_rfl⟩
  · rename_i p hp
    obtain ⟨hvu, hu, hv, hmin⟩ := argmin_candPairs hp
    refine ⟨fun x => by dsimp only; split_ifs <;> have := hw x <;> omega, ?_⟩
    dsimp only
    have hm2 : 2 ≤ st.active.card := by
      have : ({p.1, p.2} : Finset V) ⊆ st.active := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have h2 := card_le_card this
      rw [card_pair (ne_of_gt hvu)] at h2; exact h2
    obtain ⟨u, hu', v, hv', hvu', hcheap⟩ := exists_cheap_pair hγ st.w hw st.active hm2
    have hxi : st.active.card * xi G st.w p.1 p.2 ≤ s * ∑ x, st.w x :=
      (Nat.mul_le_mul_left _ (hmin u hu' v hv' hvu')).trans hcheap
    have hsum : (∑ x, if CrossesPair G x p.1 p.2 then 2 * st.w x else st.w x) =
        (∑ x, st.w x) + xi G st.w p.1 p.2 := by
      have hx : ∀ x, (if CrossesPair G x p.1 p.2 then 2 * st.w x else st.w x) =
          st.w x + (if CrossesPair G x p.1 p.2 then st.w x else 0) := by
        intro x; split_ifs <;> ring
      unfold xi
      rw [sum_congr rfl (fun x _ => hx x), sum_add_distrib, sum_filter]
    rw [hsum, card_erase_of_mem hu]
    set m := st.active.card
    set W := ∑ x, st.w x
    set ξ := xi G st.w p.1 p.2
    have hB := pow_mul_add_le m s (by omega)
    -- (W + ξ) (m-1)^s ≤ W m^s
    have h1 : (W + ξ) * m ≤ W * (m + s) := by nlinarith
    have hm1 : 0 < m := by omega
    have : (W + ξ) * (m - 1) ^ s * m ≤ W * m ^ s * m := by
      calc (W + ξ) * (m - 1) ^ s * m = ((W + ξ) * m) * (m - 1) ^ s := by ring
        _ ≤ (W * (m + s)) * (m - 1) ^ s := Nat.mul_le_mul_right _ h1
        _ = W * ((m - 1) ^ s * (m + s)) := by ring
        _ ≤ W * m ^ (s + 1) := Nat.mul_le_mul_left _ hB
        _ = W * m ^ s * m := by ring
    exact Nat.le_of_mul_le_mul_right this hm1

theorem potential_run {γ : ℕ}
    (hγ : ∀ Y : Finset V, Y.Nonempty → numCls (tpRel G Y 0) univ ≤ γ * Y.card)
    (f : ℕ) {st : WState V} (hw : ∀ x, 1 ≤ st.w x) :
    let s := 4 * γ * (Nat.log 2 (Fintype.card V) + 1)
    (∑ x, (welzlRun G f st).w x) * (welzlRun G f st).active.card ^ s ≤
      (∑ x, st.w x) * st.active.card ^ s := by
  intro s
  induction f generalizing st with
  | zero => exact le_rfl
  | succ f ih =>
    obtain ⟨hw', hstep⟩ := potential_step hγ (st := st) hw
    exact (ih hw').trans hstep

/-- **Alternation of the Welzl ordering.** If the atomic types of `G` grow
with ratio `γ`, every vertex lies in `Δ[a,b]` for at most
`2(s+1)(log₂ n + 1) + 2` consecutive pairs `a b` of the ordering, where
`s = 4γ(log₂ n + 1)`. -/
theorem alternation_welzlOrder_le {γ : ℕ}
    (hγ : ∀ Y : Finset V, Y.Nonempty → numCls (tpRel G Y 0) univ ≤ γ * Y.card) :
    alternation G (welzlOrder G) ≤
      2 * ((4 * γ * (Nat.log 2 (Fintype.card V) + 1) + 1) *
        (Nat.log 2 (Fintype.card V) + 1)) + 2 := by
  set n := Fintype.card V
  set s := 4 * γ * (Nat.log 2 n + 1)
  refine Finset.sup_le fun x _ => ?_
  have hn : 1 ≤ n := Fintype.card_pos_iff.2 ⟨x⟩
  -- the final weights
  have hpot := potential_run (G := G) hγ n (st := ⟨univ, fun _ => 1, []⟩) (fun _ => le_rfl)
  simp only [card_univ, sum_const, smul_eq_mul, mul_one] at hpot
  change (∑ y, (welzlTree G).w y) * (welzlTree G).active.card ^ s ≤ n * n ^ s at hpot
  have hact : 1 ≤ (welzlTree G).active.card := by
    rcases Nat.eq_zero_or_pos (welzlTree G).active.card with h | h
    · exfalso
      rw [card_eq_zero] at h
      have hcov := (welzlTree_inv (G := G)).cover
      -- with no active vertex, the steps would cover all vertices, but the
      -- first step's second vertex stays active
      have hv := (welzlTree_inv (G := G)).valid
      have hfold := fold_spec (G := G) (welzlTree G).steps (welzlTree G).active
        ((welzlTree G).active.sort (· ≤ ·)) hv (sort_nodup _ _) (fun x => mem_sort _)
      revert hv hcov hfold
      rw [h]
      intro hcov hv _
      cases hs : (welzlTree G).steps with
      | nil => have := hcov x; rw [hs] at this; simp at this
      | cons p rest => rw [hs] at hv; exact absurd hv.2.1 (notMem_empty _)
    · exact h
  have hW : (∑ y, (welzlTree G).w y) ≤ n * n ^ s :=
    (Nat.le_mul_of_pos_right _ (pow_pos hact s)).trans hpot
  have hwx : 2 ^ stepCross G x (welzlTree G).steps ≤ n ^ (s + 1) := by
    rw [← (welzlTree_inv (G := G)).weight x, pow_succ, Nat.mul_comm]
    exact (single_le_sum (f := (welzlTree G).w) (fun _ _ => Nat.zero_le _) (mem_univ x)).trans hW
  have hlog : n ^ (s + 1) < 2 ^ ((s + 1) * (Nat.log 2 n + 1)) := by
    rw [pow_mul']
    exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) n) (by omega)
  have hK : stepCross G x (welzlTree G).steps < (s + 1) * (Nat.log 2 n + 1) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt hwx hlog)
  have halt := altCount_le (G := G) x (welzlOrder_nodup (G := G))
  have hcross := (welzlOrder_spec (G := G)).2.2 x
  have : (if x ∈ welzlOrder G then (if (welzlOrder G).head? = some x then 1 else 2) else 0) ≤ 2 := by
    split_ifs <;> omega
  omega

end Lax185574Proofs.Chain
