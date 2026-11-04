import Lax185574Proofs.Conversions.MergeConstructionDefs

/-!
The run of the construction script of cl:from-merge-to-construction. The
partial graphs of the run are described by a coloring and a set of
resolved pairs: the edges are the resolved pairs that are edges of G,
and the non-edges the resolved pairs that are non-edges of G.
-/

namespace Lax185574Proofs.Conversions.MergeConstruction

open Lax185574.PartialGraphs Lax185574.ConstructionSequences Lax185574.SequenceEncoding
open Lax185574.MergeSequences Lax185574.Partitions Lax185574.GraphBalls

open Classical

noncomputable section

variable {n : ℕ} (G : SimpleGraph (Fin n)) (ms : List (Setoid (Fin n) × SimpleGraph (Fin n)))

/-! ### States -/

/-- The partial graph with coloring `c` whose resolved pairs are `R`,
resolved according to `G`. -/
def mk (c : Fin n → ℕ) (R : SimpleGraph (Fin n)) : PartialGraph (Fin n) where
  edge := R ⊓ G
  nonEdge := R ⊓ Gᶜ
  disjoint := (disjoint_compl_right (a := G)).mono inf_le_right inf_le_right
  color := c

theorem partialGraph_ext {V : Type*} {H H' : PartialGraph V} (h1 : H.edge = H'.edge)
    (h2 : H.nonEdge = H'.nonEdge) (h3 : H.color = H'.color) : H = H' := by
  cases H; cases H'; cases h1; cases h2; cases h3; rfl

theorem resolved_mk (c : Fin n → ℕ) (R : SimpleGraph (Fin n)) : (mk G c R).resolved = R := by
  ext x y
  simp only [PartialGraph.resolved, mk, SimpleGraph.sup_adj, SimpleGraph.inf_adj,
    SimpleGraph.compl_adj]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · intro h
    by_cases hg : G.Adj x y
    · exact Or.inl ⟨h, hg⟩
    · exact Or.inr ⟨h, h.ne, hg⟩

theorem merge_mk (c : Fin n → ℕ) (R : SimpleGraph (Fin n)) (P Q : ℕ) :
    merge (mk G c R) P Q = mk G (fun v => if c v = Q then P else c v) R := rfl

theorem between_mk (c : Fin n → ℕ) (R : SimpleGraph (Fin n)) (P Q : ℕ) :
    between (mk G c R) P Q = SimpleGraph.fromRel fun x y => c x = P ∧ c y = Q := rfl

theorem resolvePos_mk (c : Fin n → ℕ) (R : SimpleGraph (Fin n)) (P Q : ℕ)
    (h : ∀ x y, (between (mk G c R) P Q).Adj x y → ¬ R.Adj x y → G.Adj x y) :
    resolvePos (mk G c R) P Q = mk G c (R ⊔ between (mk G c R) P Q) := by
  refine partialGraph_ext ?_ ?_ rfl
  · ext x y
    simp only [resolvePos, mk, SimpleGraph.sup_adj, SimpleGraph.inf_adj, SimpleGraph.sdiff_adj,
      SimpleGraph.compl_adj]
    constructor
    · rintro (⟨hR, hG⟩ | ⟨hB, hN⟩)
      · exact ⟨Or.inl hR, hG⟩
      · by_cases hR : R.Adj x y
        · by_cases hG : G.Adj x y
          · exact ⟨Or.inl hR, hG⟩
          · exact absurd ⟨hR, hR.ne, hG⟩ hN
        · exact ⟨Or.inr hB, h x y hB hR⟩
    · rintro ⟨hR | hB, hG⟩
      · exact Or.inl ⟨hR, hG⟩
      · exact Or.inr ⟨hB, fun ⟨_, _, hG'⟩ => hG' hG⟩
  · ext x y
    simp only [resolvePos, mk, SimpleGraph.sup_adj, SimpleGraph.inf_adj, SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hR, hne, hG⟩
      exact ⟨Or.inl hR, hne, hG⟩
    · rintro ⟨hR | hB, hne, hG⟩
      · exact ⟨hR, hne, hG⟩
      · by_cases hR : R.Adj x y
        · exact ⟨hR, hne, hG⟩
        · exact absurd (h x y hB hR) hG

theorem resolveNeg_mk (c : Fin n → ℕ) (R : SimpleGraph (Fin n)) (P Q : ℕ)
    (h : ∀ x y, (between (mk G c R) P Q).Adj x y → ¬ R.Adj x y → ¬ G.Adj x y) :
    resolveNeg (mk G c R) P Q = mk G c (R ⊔ between (mk G c R) P Q) := by
  refine partialGraph_ext ?_ ?_ rfl
  · ext x y
    simp only [resolveNeg, mk, SimpleGraph.sup_adj, SimpleGraph.inf_adj]
    constructor
    · rintro ⟨hR, hG⟩
      exact ⟨Or.inl hR, hG⟩
    · rintro ⟨hR | hB, hG⟩
      · exact ⟨hR, hG⟩
      · by_cases hR : R.Adj x y
        · exact ⟨hR, hG⟩
        · exact absurd hG (h x y hB hR)
  · ext x y
    simp only [resolveNeg, mk, SimpleGraph.sup_adj, SimpleGraph.inf_adj, SimpleGraph.sdiff_adj,
      SimpleGraph.compl_adj]
    constructor
    · rintro (⟨hR, hN⟩ | ⟨hB, hE⟩)
      · exact ⟨Or.inl hR, hN⟩
      · by_cases hR : R.Adj x y
        · by_cases hG : G.Adj x y
          · exact absurd ⟨hR, hG⟩ hE
          · exact ⟨Or.inl hR, hR.ne, hG⟩
        · exact ⟨Or.inr hB, hB.ne, h x y hB hR⟩
    · rintro ⟨hR | hB, hne, hG⟩
      · exact Or.inl ⟨hR, hne, hG⟩
      · exact Or.inr ⟨hB, fun ⟨_, hG'⟩ => hG hG'⟩

/-! ### The merge sequence -/

variable {G ms}

theorem part_zero (hm : IsMergeSequence G ms) : part ms 0 = ⊥ := by
  obtain ⟨hne, hhead, -⟩ := hm
  have h0 : 0 < ms.length := List.length_pos_of_ne_nil hne
  simp only [part, h0, dite_true]
  rw [← hhead, List.head_eq_getElem]

theorem part_last (hm : IsMergeSequence G ms) {j : ℕ} (hj : ms.length ≤ j + 1) :
    part ms j = ⊤ := by
  obtain ⟨hne, -, hlast, -⟩ := hm
  unfold part
  split_ifs with h
  · have : j = ms.length - 1 := by omega
    subst this
    rw [← hlast, List.getLast_eq_getElem]
  · rfl

theorem part_succ_le (hm : IsMergeSequence G ms) (j : ℕ) : part ms j ≤ part ms (j + 1) := by
  obtain ⟨-, -, -, hmono, -⟩ := hm
  unfold part
  split_ifs with h1 h2
  · exact (hmono j h2).1
  · exact le_top
  · omega
  · exact le_rfl

theorem part_mono (hm : IsMergeSequence G ms) {i j : ℕ} (hij : i ≤ j) : part ms i ≤ part ms j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact ih.trans (part_succ_le hm j)

theorem rel_succ_le (hm : IsMergeSequence G ms) (j : ℕ) : rel ms j ≤ rel ms (j + 1) := by
  obtain ⟨-, -, -, hmono, -⟩ := hm
  unfold rel
  split_ifs with h1 h2
  · exact (hmono j h2).2
  · exact le_top
  · omega
  · exact le_rfl

theorem rel_mono (hm : IsMergeSequence G ms) {i j : ℕ} (hij : i ≤ j) : rel ms i ≤ rel ms j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact ih.trans (rel_succ_le hm j)

theorem homogeneous (hm : IsMergeSequence G ms) {j : ℕ} (hj : j < ms.length) :
    HomogeneousModulo G (part ms j) (rel ms j) := by
  obtain ⟨-, -, -, -, hhom⟩ := hm
  simp only [part, rel, hj, dite_true]
  exact hhom j hj

/-! ### Blocks and resolved pairs -/

variable (ms)

theorem rect_adj (j a b : ℕ) (x y : Fin n) :
    (rect ms j a b).Adj x y ↔
      x ≠ y ∧ ((col ms j x = a ∧ col ms j y = b) ∨ (col ms j y = a ∧ col ms j x = b)) := by
  simp [rect, SimpleGraph.fromRel_adj]

theorem block_adj (j : ℕ) (x y : Fin n) :
    (block ms j).Adj x y ↔
      x ≠ y ∧ ∀ a b, part ms j a x → part ms j b y → a ≠ b → (rel ms (j + 1)).Adj a b := by
  simp only [block, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, fun a b ha hb hab => (h b a hb ha hab.symm).symm⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

theorem resolvedAt_adj (j : ℕ) (x y : Fin n) :
    (resolvedAt ms j).Adj x y ↔ ∃ i < j, (block ms i).Adj x y := by
  simp only [resolvedAt, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨i, hi, h⟩ | ⟨i, hi, h⟩⟩
    · exact ⟨i, hi, h⟩
    · exact ⟨i, hi, h.symm⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨h.ne, Or.inl ⟨i, hi, h⟩⟩

theorem resolvedAt_zero : resolvedAt ms 0 = ⊥ := by
  ext x y
  simp [resolvedAt_adj]

theorem resolvedAt_succ (j : ℕ) : resolvedAt ms (j + 1) = resolvedAt ms j ⊔ block ms j := by
  ext x y
  simp only [resolvedAt_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨i, hi, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact Or.inl ⟨i, hi, h⟩
    · exact Or.inr h
  · rintro (⟨i, hi, h⟩ | h)
    · exact ⟨i, by omega, h⟩
    · exact ⟨j, by omega, h⟩

variable {ms}

theorem block_le_rel (j : ℕ) : block ms j ≤ rel ms (j + 1) := by
  intro x y h
  rw [block_adj] at h
  exact h.2 x y ((part ms j).refl x) ((part ms j).refl y) h.1

theorem resolvedAt_le_rel (hm : IsMergeSequence G ms) (j : ℕ) : resolvedAt ms j ≤ rel ms j := by
  intro x y h
  rw [resolvedAt_adj] at h
  obtain ⟨i, hi, h⟩ := h
  exact rel_mono hm (by omega) (block_le_rel i h)

/-- In the last stage the block contains all pairs. -/
theorem block_last {j : ℕ} (hj : ms.length ≤ j + 1) :
    block ms j = ⊤ := by
  ext x y
  rw [block_adj]
  simp only [SimpleGraph.top_adj]
  refine ⟨fun h => h.1, fun h => ⟨h, fun a b _ _ hab => ?_⟩⟩
  have : rel ms (j + 1) = ⊤ := by simp [rel]; omega
  rw [this]
  exact hab

/-- All pairs are resolved after the last stage. -/
theorem resolvedAt_length (hm : IsMergeSequence G ms) : resolvedAt ms ms.length = ⊤ := by
  have hne := hm.1
  have h0 : 0 < ms.length := List.length_pos_of_ne_nil hne
  ext x y
  simp only [SimpleGraph.top_adj, resolvedAt_adj]
  refine ⟨fun ⟨i, _, h⟩ => h.ne, fun h => ⟨ms.length - 1, by omega, ?_⟩⟩
  rw [block_last (by omega)]
  exact h

/-! ### Homogeneity of the unresolved pairs -/

/-- At the start of stage `j`, the unresolved pairs between two parts of
`𝒫_j` are all edges or all non-edges. -/
theorem homogeneous_unresolved (hm : IsMergeSequence G ms) :
    ∀ j < ms.length, ∀ a b c d : Fin n, part ms j a c → part ms j b d → a ≠ b → c ≠ d →
      ¬ (resolvedAt ms j).Adj a b → ¬ (resolvedAt ms j).Adj c d → (G.Adj a b ↔ G.Adj c d) := by
  intro j
  induction j with
  | zero =>
    intro _ a b c d hac hbd _ _ _ _
    rw [part_zero hm, Setoid.bot_def] at hac hbd
    rw [hac, hbd]
  | succ j ih =>
    intro hj a b c d hac hbd hab hcd hRab hRcd
    rw [resolvedAt_succ, SimpleGraph.sup_adj, not_or] at hRab hRcd
    -- a witness outside `R_{j+1}` in the finer rectangle
    have wit : ∀ a b : Fin n, a ≠ b → ¬ (block ms j).Adj a b →
        ∃ a' b', part ms j a' a ∧ part ms j b' b ∧ a' ≠ b' ∧ ¬ (rel ms (j + 1)).Adj a' b' := by
      intro a b hab hB
      rw [block_adj] at hB
      push Not at hB
      obtain ⟨a', b', ha', hb', hab', hR⟩ := hB hab
      exact ⟨a', b', ha', hb', hab', hR⟩
    obtain ⟨a', b', ha', hb', hab', hRa⟩ := wit a b hab hRab.2
    obtain ⟨c', d', hc', hd', hcd', hRc⟩ := wit c d hcd hRcd.2
    have hRs : ∀ x y, ¬ (rel ms (j + 1)).Adj x y → ¬ (resolvedAt ms j).Adj x y :=
      fun x y h h' => h (rel_succ_le hm j (resolvedAt_le_rel hm j h'))
    have e1 := ih (by omega) a b a' b' ((part ms j).symm ha') ((part ms j).symm hb') hab hab'
      hRab.1 (hRs a' b' hRa)
    have e2 := ih (by omega) c d c' d' ((part ms j).symm hc') ((part ms j).symm hd') hcd hcd'
      hRcd.1 (hRs c' d' hRc)
    rw [e1, e2]
    have hle := part_succ_le hm j
    have hca : part ms (j + 1) c' a' :=
      (part ms (j + 1)).trans (hle hc') ((part ms (j + 1)).trans ((part ms (j + 1)).symm hac)
        ((part ms (j + 1)).symm (hle ha')))
    have hdb : part ms (j + 1) d' b' :=
      (part ms (j + 1)).trans (hle hd') ((part ms (j + 1)).trans ((part ms (j + 1)).symm hbd)
        ((part ms (j + 1)).symm (hle hb')))
    rcases homogeneous hm hj a' b' with h | h
    · exact ⟨fun _ => h c' d' hca hdb hcd' hRc,
        fun _ => h a' b' ((part ms _).refl a') ((part ms _).refl b') hab' hRa⟩
    · exact ⟨fun h' => absurd h' (h a' b' ((part ms _).refl a') ((part ms _).refl b') hab' hRa),
        fun h' => absurd h' (h c' d' hca hdb hcd' hRc)⟩

/-! ### Rectangles -/

variable (ms)

theorem col_eq_iff (j : ℕ) (x y : Fin n) : col ms j x = col ms j y ↔ part ms j x y := by
  rw [col, col, Fin.val_inj, rep_eq_iff]

/-- Two pairs of one rectangle lie in the same parts, possibly swapped. -/
theorem rect_aligned (j a b : ℕ) {x y x' y' : Fin n} (h : (rect ms j a b).Adj x y)
    (h' : (rect ms j a b).Adj x' y') :
    (part ms j x x' ∧ part ms j y y') ∨ (part ms j x y' ∧ part ms j y x') := by
  rw [rect_adj] at h h'
  simp only [← col_eq_iff]
  omega

/-- The pairs resolved during a stage, as a graph. -/
def doneGraph (j : ℕ) (L : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => ∃ p ∈ L, (rect ms j p.1 p.2).Adj x y

theorem doneGraph_adj (j : ℕ) (L : List (Fin n × Fin n)) (x y : Fin n) :
    (doneGraph ms j L).Adj x y ↔ ∃ p ∈ L, (rect ms j p.1 p.2).Adj x y := by
  simp only [doneGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | ⟨p, hp, h⟩⟩
    · exact h
    · exact ⟨p, hp, h.symm⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨h.ne, Or.inl ⟨p, hp, h⟩⟩

theorem doneGraph_nil (j : ℕ) : doneGraph ms j [] = ⊥ := by
  ext x y; simp [doneGraph_adj]

theorem doneGraph_append (j : ℕ) (L : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    doneGraph ms j (L ++ [p]) = doneGraph ms j L ⊔ rect ms j p.1 p.2 := by
  ext x y
  simp only [doneGraph_adj, SimpleGraph.sup_adj, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨q, hq | rfl, h⟩
    · exact Or.inl ⟨q, hq, h⟩
    · exact Or.inr h
  · rintro (⟨q, hq, h⟩ | h)
    · exact ⟨q, Or.inl hq, h⟩
    · exact ⟨p, Or.inr rfl, h⟩

theorem mem_resolvePairs (j : ℕ) (p : Fin n × Fin n) :
    p ∈ resolvePairs ms j ↔ Resolves ms j p := by
  simp [resolvePairs]

theorem doneGraph_le_rel (j : ℕ) (L : List (Fin n × Fin n)) (hL : ∀ p ∈ L, Resolves ms j p) :
    doneGraph ms j L ≤ rel ms (j + 1) := by
  intro x y h
  rw [doneGraph_adj] at h
  obtain ⟨p, hp, h⟩ := h
  exact (hL p hp).2.2.2.1 h

/-- After the resolves of stage `j`, the resolved pairs are those
resolved at the start of stage `j + 1`. -/
theorem resolvedAt_sup_doneGraph (j : ℕ) :
    resolvedAt ms j ⊔ doneGraph ms j (resolvePairs ms j) = resolvedAt ms (j + 1) := by
  rw [resolvedAt_succ]
  ext x y
  simp only [SimpleGraph.sup_adj, doneGraph_adj, mem_resolvePairs]
  constructor
  · rintro (h | ⟨p, hp, h⟩)
    · exact Or.inl h
    · right
      rw [block_adj]
      refine ⟨h.ne, fun a b ha hb hab => hp.2.2.2.1 ?_⟩
      rw [rect_adj] at h ⊢
      rw [← col_eq_iff] at ha hb
      exact ⟨hab, by omega⟩
  · rintro (h | h)
    · exact Or.inl h
    by_cases hR : (resolvedAt ms j).Adj x y
    · exact Or.inl hR
    right
    have hrect : ∀ x' y' : Fin n, (rect ms j (col ms j x) (col ms j y)).Adj x' y' →
        (rel ms (j + 1)).Adj x' y' := by
      intro x' y' h'
      rw [block_adj] at h
      rw [rect_adj] at h'
      obtain ⟨hne, h1 | h1⟩ := h'
      · exact h.2 x' y' ((col_eq_iff ms j _ _).1 h1.1) ((col_eq_iff ms j _ _).1 h1.2) hne
      · exact (h.2 y' x' ((col_eq_iff ms j _ _).1 h1.1) ((col_eq_iff ms j _ _).1 h1.2)
          hne.symm).symm
    have hxy : (rect ms j (col ms j x) (col ms j y)).Adj x y := by
      rw [rect_adj]; exact ⟨h.ne, Or.inl ⟨rfl, rfl⟩⟩
    have hsymm : rect ms j (col ms j x) (col ms j y) = rect ms j (col ms j y) (col ms j x) := by
      ext u w; rw [rect_adj, rect_adj]; tauto
    let a := rep (part ms j) x
    let b := rep (part ms j) y
    have hres : ∀ p : Fin n × Fin n, p.1 ≤ p.2 →
        rect ms j p.1 p.2 = rect ms j (col ms j x) (col ms j y) →
        rep (part ms j) p.1 = p.1 → rep (part ms j) p.2 = p.2 → Resolves ms j p := by
      intro p hp hrp h1 h2
      refine ⟨hp, h1, h2, ?_, fun hle => hR ?_⟩
      · rw [hrp]; exact hrect
      · exact hle (hrp ▸ hxy)
    rcases le_total a b with hab | hab
    · exact ⟨(a, b), hres (a, b) hab rfl (rep_rep _ _) (rep_rep _ _), hxy⟩
    · exact ⟨(b, a), hres (b, a) hab hsymm.symm (rep_rep _ _) (rep_rep _ _), hsymm ▸ hxy⟩

/-! ### The steps of a stage -/

variable (G)

/-- The state during the resolves of stage `j`, after the rectangles
`L`. -/
def resolveState (j : ℕ) (L : List (Fin n × Fin n)) : PartialGraph (Fin n) :=
  mk G (col ms j) (resolvedAt ms j ⊔ doneGraph ms j L)

/-- The coloring during the merges of stage `j`, after the sources `D`. -/
def mergeCol (j : ℕ) (D : List (Fin n)) (x : Fin n) : ℕ :=
  if rep (part ms j) x ∈ D then col ms (j + 1) x else col ms j x

/-- The state during the merges of stage `j`, after the sources `D`. -/
def mergeState (j : ℕ) (D : List (Fin n)) : PartialGraph (Fin n) :=
  mk G (mergeCol ms j D) (resolvedAt ms (j + 1))

variable {G ms}

theorem apply_resolveStep (hm : IsMergeSequence G ms) {j : ℕ} (hj : j < ms.length)
    (L : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    apply (resolveState G ms j L) (resolveStep G ms j p) = resolveState G ms j (L ++ [p]) := by
  have hB : between (resolveState G ms j L) (p.1 : ℕ) (p.2 : ℕ) = rect ms j p.1 p.2 := rfl
  have hunres : ∀ x y, ¬ (resolvedAt ms j ⊔ doneGraph ms j L).Adj x y →
      ¬ (resolvedAt ms j).Adj x y := fun x y h h' => h (Or.inl h')
  unfold resolveStep resolveState
  split_ifs with hpos
  · change resolvePos _ _ _ = _
    rw [resolvePos_mk, between_mk]
    · change mk G (col ms j) (resolvedAt ms j ⊔ doneGraph ms j L ⊔ rect ms j p.1 p.2) = _
      rw [doneGraph_append, sup_assoc]
    · intro x y hxy hR
      rw [between_mk] at hxy
      change (rect ms j p.1 p.2).Adj x y at hxy
      obtain ⟨x', y', hxy', hR', hG'⟩ := hpos
      have hR0 := hunres x y hR
      rcases rect_aligned ms j _ _ hxy hxy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact (homogeneous_unresolved hm j hj x y x' y' h1 h2 hxy.ne hxy'.ne hR0 hR').2 hG'
      · refine (homogeneous_unresolved hm j hj x y y' x' h1 h2 hxy.ne hxy'.ne.symm hR0
          (fun h => hR' h.symm)).2 hG'.symm
  · change resolveNeg _ _ _ = _
    rw [resolveNeg_mk, between_mk]
    · change mk G (col ms j) (resolvedAt ms j ⊔ doneGraph ms j L ⊔ rect ms j p.1 p.2) = _
      rw [doneGraph_append, sup_assoc]
    · intro x y hxy hR hG
      rw [between_mk] at hxy
      exact hpos ⟨x, y, hxy, hunres x y hR, hG⟩

theorem mem_mergeSources (j : ℕ) (v : Fin n) : v ∈ mergeSources ms j ↔ IsSource ms j v := by
  simp [mergeSources]

theorem apply_mergeStep (hm : IsMergeSequence G ms) (j : ℕ) (D : List (Fin n)) {v : Fin n}
    (hv : IsSource ms j v) (hvD : v ∉ D) :
    apply (mergeState G ms j D) (mergeStep ms j v) = mergeState G ms j (D ++ [v]) := by
  have hle := part_succ_le hm j
  unfold mergeStep mergeState
  change merge _ _ _ = _
  rw [merge_mk]
  congr 1
  funext x
  simp only [mergeCol, List.mem_append, List.mem_singleton]
  by_cases hx : rep (part ms j) x ∈ D
  · have hne : col ms (j + 1) x ≠ (v : ℕ) := by
      intro h
      have h' : rep (part ms (j + 1)) x = v := Fin.ext h
      apply hv.2
      rw [← h', rep_rep]
    simp [hx, hne]
  · by_cases hxv : rep (part ms j) x = v
    · subst hxv
      have : (if rep (part ms j) x ∈ D then col ms (j + 1) x else col ms j x) =
          ((rep (part ms j) x : Fin n) : ℕ) := by rw [if_neg hx]; rfl
      simp only [this, if_true, or_true]
      rw [col, rep_rep_of_le hle]
    · have : col ms j x ≠ (v : ℕ) := fun h => hxv (Fin.ext h)
      simp [hx, hxv, this]

theorem mergeState_nil (j : ℕ) : mergeState G ms j [] = mk G (col ms j) (resolvedAt ms (j + 1)) := by
  unfold mergeState
  congr 1

theorem mergeState_all (hm : IsMergeSequence G ms) (j : ℕ) :
    mergeState G ms j (mergeSources ms j) = mk G (col ms (j + 1)) (resolvedAt ms (j + 1)) := by
  unfold mergeState
  congr 1
  funext x
  simp only [mergeCol, mem_mergeSources]
  split_ifs with h
  · rfl
  · have hr : rep (part ms (j + 1)) (rep (part ms j) x) = rep (part ms j) x := by
      by_contra hne
      exact h ⟨rep_rep _ _, hne⟩
    rw [col, col, ← rep_rep_of_le (part_succ_le hm j) x, hr]

/-! ### Chains along scans -/

theorem chain_scanl_of_states {α β : Type*} (f : α → β → α) (Rel : α → α → Prop)
    (L : List β) (st : ℕ → α)
    (h : ∀ (k : ℕ) (hk : k < L.length), f (st k) L[k] = st (k + 1) ∧ Rel (st k) (st (k + 1))) :
    L.foldl f (st 0) = st L.length ∧ (L.scanl f (st 0)).IsChain Rel := by
  induction L generalizing st with
  | nil => exact ⟨rfl, List.isChain_singleton _⟩
  | cons b L ih =>
    obtain ⟨h0, hr0⟩ := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨ih1, ih2⟩ := ih (fun k => st (k + 1)) (fun k hk => h (k + 1) (by simp; omega))
    refine ⟨by simp [List.foldl_cons, h0, ih1], ?_⟩
    rw [List.scanl_cons, h0]
    cases L with
    | nil => exact List.isChain_cons_cons.2 ⟨hr0, List.isChain_singleton _⟩
    | cons c L =>
      rw [List.scanl_cons] at ih2 ⊢
      exact List.isChain_cons_cons.2 ⟨hr0, ih2⟩

theorem chain_scanl_append {α β : Type*} (f : α → β → α) (Rel : α → α → Prop) (a : α)
    (l₁ l₂ : List β) (h₁ : (l₁.scanl f a).IsChain Rel)
    (h₂ : (l₂.scanl f (l₁.foldl f a)).IsChain Rel) :
    ((l₁ ++ l₂).scanl f a).IsChain Rel := by
  induction l₁ generalizing a with
  | nil => simpa using h₂
  | cons b l ih =>
    rw [List.scanl_cons] at h₁
    rw [List.cons_append, List.scanl_cons]
    have ih' := ih (f a b) (by
      cases l with
      | nil => exact List.isChain_singleton _
      | cons c l => rw [List.scanl_cons] at h₁ ⊢; exact (List.isChain_cons_cons.1 h₁).2) h₂
    have hr : Rel a (f a b) := by
      cases l with
      | nil => exact (List.isChain_cons_cons.1 h₁).1
      | cons c l => rw [List.scanl_cons] at h₁; exact (List.isChain_cons_cons.1 h₁).1
    cases h : l ++ l₂ with
    | nil => rw [h] at ih'; simp only [List.scanl_nil]; exact List.isChain_cons_cons.2 ⟨hr, List.isChain_singleton _⟩
    | cons c l' =>
      rw [h, List.scanl_cons] at ih'
      rw [List.scanl_cons]
      exact List.isChain_cons_cons.2 ⟨hr, ih'⟩

end

end Lax185574Proofs.Conversions.MergeConstruction
