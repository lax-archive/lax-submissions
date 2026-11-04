import Lax185574Proofs.Conversions.MergeConstructionFormulas
import Lax185574Proofs.Conversions.ColorMaps

/-!
The definability part of cl:from-merge-to-construction. Mark the stages
by `2m` colors, two for each stage, and the ball `B` by one more color.
Fix a step of stage `j` and a vertex `v`, and let `B` be the radius-`r`
ball of `v` in the next partial graph. Take as parameters the least
vertices of the parts of `𝒫_j` meeting `B`, at most `max(1, w_r)` of
them. Then on `B` the resolved pairs are defined by `Γ_j` together with
the rectangles resolved so far in the stage, and a color class by the
disjunction of `φ^j_≡(x, p)` over the parameters `p` of that color.
-/

namespace Lax185574Proofs.Conversions.MergeConstruction

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.PartialGraphs Lax185574.MergeSequences Lax185574.FirstOrderTypes
open Lax185574.BetterMergeSequences Lax185574.LocalDefinability Lax185574.Colorings
open Lax185574.GraphBalls Lax185574.Partitions
open Lax185574Proofs.DistanceFormulaRank Lax185574Proofs.FormulaRank
open Lax185574Proofs.Conversions.ColorMaps

open Classical

noncomputable section

variable {n : ℕ} {G : SimpleGraph (Fin n)} {ms : List (Setoid (Fin n) × SimpleGraph (Fin n))}

/-! ### Colors -/

variable (ms) in
/-- The color of the `k`-th predicate of stage `i`. -/
def stageColor (i : ℕ) (k : Fin 2) : Fin (2 * ms.length + 1) :=
  ⟨min (2 * i + k) (2 * ms.length), by omega⟩

variable (ms) in
/-- The color marking the ball. -/
def ballColor : Fin (2 * ms.length + 1) := ⟨2 * ms.length, by omega⟩

/-- The colors: the predicates of the stages, then the ball. -/
def allColors (C : ℕ → Fin 2 → Set (Fin n)) (B : Set (Fin n)) :
    Fin (2 * ms.length + 1) → Set (Fin n) :=
  fun c => if c.val < 2 * ms.length then C (c.val / 2) ⟨c.val % 2, Nat.mod_lt _ (by omega)⟩ else B

theorem allColors_stage (C : ℕ → Fin 2 → Set (Fin n)) (B : Set (Fin n)) {i : ℕ}
    (hi : i < ms.length) : allColors (ms := ms) C B ∘ stageColor ms i = C i := by
  funext k
  simp only [Function.comp_apply, allColors]
  have hk := k.isLt
  have hv : (stageColor ms i k : ℕ) = 2 * i + k := by
    simp only [stageColor]; omega
  split_ifs with h
  · congr 1
    · rw [hv]; omega
    · exact Fin.ext (by simp only [hv]; omega)
  · exfalso; omega

theorem allColors_ball (C : ℕ → Fin 2 → Set (Fin n)) (B : Set (Fin n)) :
    allColors (ms := ms) C B (ballColor ms) = B := by
  simp [allColors, ballColor]

/-! ### Atoms -/

/-- The language of graphs with the colors of all stages and the ball. -/
abbrev LK (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))) : Language :=
  withColors Language.graph (2 * ms.length + 1)

variable (ms) in
/-- `U_B(x)`. -/
def ballF : (LK ms).Formula (Fin 1) :=
  Relations.formula₁ (Sum.inr (ColorRel.color (ballColor ms))) (Term.var 0)

variable (ms) in
/-- `E(x, y)`. -/
def adjF : (LK ms).Formula (Fin 2) :=
  Relations.formula₂ (Sum.inl Language.adj) (Term.var 0) (Term.var 1)

theorem qr_ballF : quantifierRank (ballF ms) = 0 := rfl

theorem qr_adjF : quantifierRank (adjF ms) = 0 := rfl

theorem realize_ballF (C : ℕ → Fin 2 → Set (Fin n)) (B : Set (Fin n)) {β : Type} (s : β)
    (v : β → Fin n) :
    @Formula.Realize _ _ (expansion G (allColors (ms := ms) C B)) _
      ((ballF ms).relabel fun _ => s) v ↔ v s ∈ B := by
  rw [@Formula.realize_relabel]
  change v s ∈ allColors (ms := ms) C B (ballColor ms) ↔ _
  rw [allColors_ball]

theorem realize_adjF (C : ℕ → Fin 2 → Set (Fin n)) (B : Set (Fin n)) {β : Type} (s t : β)
    (v : β → Fin n) :
    @Formula.Realize _ _ (expansion G (allColors (ms := ms) C B)) _ (pairF (adjF ms) s t) v ↔
      G.Adj (v s) (v t) := by
  rw [@realize_pairF]
  rfl

/-! ### The defining formulas -/

section Core

variable (φeq φR : (withColors Language.graph 2).Formula (Fin 2)) (C : ℕ → Fin 2 → Set (Fin n))

variable (ms) in
/-- `φ^i_≡` over all colors. -/
def eqFK (i : ℕ) : (LK ms).Formula (Fin 2) := recolor (stageColor ms i) φeq

variable (ms) in
/-- `φ^i_R` over all colors. -/
def relFK (i : ℕ) : (LK ms).Formula (Fin 2) := recolor (stageColor ms i) φR

variable (ms) in
/-- The parameters: the least vertices of the parts of `𝒫_j` meeting `B`. -/
def params (j : ℕ) (B : Set (Fin n)) : Finset (Fin n) :=
  (Finset.univ.filter (· ∈ B)).image (rep (part ms j))

variable (hC : ∀ i < ms.length, ∀ x : Fin 2 → Fin n,
    (@Formula.Realize _ _ (expansion G (C i)) _ φeq x ↔ part ms i (x 0) (x 1)) ∧
    (@Formula.Realize _ _ (expansion G (C i)) _ φR x ↔ (rel ms i).Adj (x 0) (x 1)))

include hC in
theorem realize_eqFK (B : Set (Fin n)) {i : ℕ} (hi : i < ms.length) (x : Fin 2 → Fin n) :
    @Formula.Realize _ _ (expansion G (allColors (ms := ms) C B)) _ (eqFK ms φeq i) x ↔
      part ms i (x 0) (x 1) := by
  rw [eqFK, realize_recolor_formula, allColors_stage C B hi]
  exact (hC i hi x).1

include hC in
theorem realize_relFK (B : Set (Fin n)) {i : ℕ} (hi : i < ms.length) (x : Fin 2 → Fin n) :
    @Formula.Realize _ _ (expansion G (allColors (ms := ms) C B)) _ (relFK ms φR i) x ↔
      (rel ms i).Adj (x 0) (x 1) := by
  rw [relFK, realize_recolor_formula, allColors_stage C B hi]
  exact (hC i hi x).2

theorem mem_params {j : ℕ} {B : Set (Fin n)} {p : Fin n} :
    p ∈ params ms j B ↔ ∃ x ∈ B, rep (part ms j) x = p := by
  simp [params]

theorem rep_params {j : ℕ} {B : Set (Fin n)} {p : Fin n} (hp : p ∈ params ms j B) :
    rep (part ms j) p = p := by
  obtain ⟨x, -, rfl⟩ := mem_params.1 hp
  exact rep_rep _ _

include hC in
/-- **The core of the definability.** A partial graph of stage `j`,
restricted to a set `B`, is definable with the least vertices of the
parts of `𝒫_j` meeting `B` as parameters, by formulas of quantifier
rank at most `7`. -/
theorem definableIn_state (hφeq : quantifierRank φeq ≤ 5) (hφR : quantifierRank φR ≤ 5)
    {j : ℕ} (hj : j < ms.length) {c : Fin n → ℕ}
    (hc : ∀ x y, part ms j x y → c x = c y) {L : List (Fin n × Fin n)}
    (hL : ∀ p ∈ L, Resolves ms j p) (B : Set (Fin n)) :
    @DefinableIn (Fin n) (LK ms) (expansion G (allColors (ms := ms) C B)) 7
      (params ms j B : Set (Fin n)) (mk G c (resolvedAt ms j ⊔ doneGraph ms j L)) B := by
  let _ := expansion G (allColors (ms := ms) C B)
  have hEq := fun i hi x => realize_eqFK φeq φR C hC B (i := i) hi x
  have hRel := fun i hi x => realize_relFK φeq φR C hC B (i := i) hi x
  have hqe : ∀ i, quantifierRank (eqFK ms φeq i) ≤ 5 := fun i => by
    rw [eqFK, quantifierRank_recolor]; exact hφeq
  have hqr : ∀ i, quantifierRank (relFK ms φR i) ≤ 5 := fun i => by
    rw [relFK, quantifierRank_recolor]; exact hφR
  -- the resolved pairs
  let S' := ↥(params ms j B : Set (Fin n))
  let Q := {q : S' × S' // ((q.1 : Fin n), (q.2 : Fin n)) ∈ L}
  let RcurF : (LK ms).Formula (Fin 2 ⊕ S') :=
    pairF (GammaF (eqFK ms φeq) (relFK ms φR) j) (Sum.inl 0) (Sum.inl 1) ⊔
      BoundedFormula.iSup fun q : Q =>
        rectF (eqFK ms φeq) j (Sum.inl 0) (Sum.inl 1) (Sum.inr q.1.1) (Sum.inr q.1.2)
  have hqR : quantifierRank RcurF ≤ 7 := by
    simp only [RcurF, qr_sup, qr_pairF]
    exact max_le (qr_GammaF hqe hqr j) (qr_iSup_le _ _ fun q => (qr_rectF hqe j _ _ _ _).trans
      (by norm_num))
  have hR : ∀ x : Fin 2 → Fin n, x 0 ∈ B → x 1 ∈ B →
      (RcurF.Realize (Sum.elim x Subtype.val) ↔
        (resolvedAt ms j ⊔ doneGraph ms j L).Adj (x 0) (x 1)) := by
    intro x hx0 hx1
    simp only [RcurF, Formula.realize_sup, realize_pairF, SimpleGraph.sup_adj, Sum.elim_inl]
    refine or_congr ?_ ?_
    · rw [realize_GammaF hEq hRel hj]
      rfl
    · unfold Formula.Realize
      rw [BoundedFormula.realize_iSup, doneGraph_adj]
      constructor
      · rintro ⟨q, hq⟩
        have hq' := (realize_rectF hEq hj (Sum.inl 0) (Sum.inl 1) (Sum.inr q.1.1) (Sum.inr q.1.2)
          (Sum.elim x Subtype.val) (rep_params q.1.1.2) (rep_params q.1.2.2)).1 hq
        exact ⟨((q.1.1 : Fin n), (q.1.2 : Fin n)), q.2, hq'⟩
      · rintro ⟨p, hp, hpr⟩
        obtain ⟨-, ha, hb, -⟩ := hL p hp
        -- both parameters are least vertices of parts meeting `B`
        have hmem : ∀ a : Fin n, rep (part ms j) a = a →
            (col ms j (x 0) = a ∨ col ms j (x 1) = a) → a ∈ params ms j B := by
          intro a _ h
          rcases h with h | h
          · exact mem_params.2 ⟨x 0, hx0, Fin.ext h⟩
          · exact mem_params.2 ⟨x 1, hx1, Fin.ext h⟩
        have hpr' := hpr
        rw [rect_adj] at hpr'
        have h1 : p.1 ∈ params ms j B := hmem p.1 ha (by omega)
        have h2 : p.2 ∈ params ms j B := hmem p.2 hb (by omega)
        let a' : S' := ⟨p.1, h1⟩
        let b' : S' := ⟨p.2, h2⟩
        let v : Fin 2 ⊕ S' → Fin n := Sum.elim x (Subtype.val : S' → Fin n)
        have ha' : rep (part ms j) (v (Sum.inr a')) = v (Sum.inr a') := ha
        have hb' : rep (part ms j) (v (Sum.inr b')) = v (Sum.inr b') := hb
        have hpr2 : (rect ms j (v (Sum.inr a')) (v (Sum.inr b'))).Adj (v (Sum.inl 0))
            (v (Sum.inl 1)) := hpr
        refine ⟨⟨(a', b'), hp⟩, ?_⟩
        exact (realize_rectF hEq hj (Sum.inl 0) (Sum.inl 1) (Sum.inr a') (Sum.inr b') v ha' hb').2 hpr2
  have hU : ∀ {β : Type} (s : β) (v : β → Fin n),
      ((ballF ms).relabel fun _ => s).Realize v ↔ v s ∈ B :=
    fun s v => realize_ballF (G := G) C B s v
  have hqU : ∀ {β : Type} (s : β), quantifierRank ((ballF ms).relabel fun _ => s) = 0 :=
    fun s => by rw [quantifierRank_formula_relabel]; rfl
  intro k Rel
  cases Rel with
  | edge =>
    refine ⟨((ballF ms).relabel fun _ => Sum.inl 0) ⊓ ((ballF ms).relabel fun _ => Sum.inl 1) ⊓
      RcurF ⊓ pairF (adjF ms) (Sum.inl 0) (Sum.inl 1), ?_, fun x => ?_⟩
    · simp only [qr_inf, hqU, qr_pairF, qr_adjF]
      omega
    · simp only [Formula.realize_inf, hU, realize_adjF, Sum.elim_inl, Fin.forall_fin_two]
      change _ ↔ (x 0 ∈ B ∧ x 1 ∈ B) ∧ ((resolvedAt ms j ⊔ doneGraph ms j L) ⊓ G).Adj (x 0) (x 1)
      rw [SimpleGraph.inf_adj]
      constructor
      · rintro ⟨⟨⟨h0, h1⟩, hr⟩, hg⟩
        exact ⟨⟨h0, h1⟩, (hR x h0 h1).1 hr, hg⟩
      · rintro ⟨⟨h0, h1⟩, hr, hg⟩
        exact ⟨⟨⟨h0, h1⟩, (hR x h0 h1).2 hr⟩, hg⟩
  | nonEdge =>
    refine ⟨((ballF ms).relabel fun _ => Sum.inl 0) ⊓ ((ballF ms).relabel fun _ => Sum.inl 1) ⊓
      RcurF ⊓ ∼(pairF (adjF ms) (Sum.inl 0) (Sum.inl 1)), ?_, fun x => ?_⟩
    · simp only [qr_inf, hqU, qr_not, qr_pairF, qr_adjF]
      omega
    · simp only [Formula.realize_inf, Formula.realize_not, hU, realize_adjF, Sum.elim_inl,
        Fin.forall_fin_two]
      change _ ↔ (x 0 ∈ B ∧ x 1 ∈ B) ∧ ((resolvedAt ms j ⊔ doneGraph ms j L) ⊓ Gᶜ).Adj (x 0) (x 1)
      rw [SimpleGraph.inf_adj, SimpleGraph.compl_adj]
      constructor
      · rintro ⟨⟨⟨h0, h1⟩, hr⟩, hg⟩
        have hr' := (hR x h0 h1).1 hr
        exact ⟨⟨h0, h1⟩, hr', hr'.ne, hg⟩
      · rintro ⟨⟨h0, h1⟩, hr, -, hg⟩
        exact ⟨⟨⟨h0, h1⟩, (hR x h0 h1).2 hr⟩, hg⟩
  | color Y =>
    refine ⟨((ballF ms).relabel fun _ => Sum.inl 0) ⊓
      BoundedFormula.iSup fun p : {p : S' // c p = Y} =>
        pairF (eqFK ms φeq j) (Sum.inl 0) (Sum.inr p.1), ?_, fun x => ?_⟩
    · simp only [qr_inf, hqU]
      refine max_le (by omega) (qr_iSup_le _ _ fun p => ?_)
      rw [qr_pairF]
      exact le_trans (hqe j) (by norm_num)
    · rw [Formula.realize_inf, hU]
      unfold Formula.Realize
      rw [BoundedFormula.realize_iSup]
      simp only [Sum.elim_inl, Fin.forall_fin_one]
      change _ ↔ x 0 ∈ B ∧ c (x 0) = Y
      refine and_congr_right fun hx => ?_
      constructor
      · rintro ⟨⟨p, hp⟩, h⟩
        have h' := (realize_pairF _ _ _ _).1 h
        rw [hEq j hj] at h'
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl, Sum.elim_inr] at h'
        rw [hc _ _ h', hp]
      · intro h
        let p : S' := ⟨rep (part ms j) (x 0), mem_params.2 ⟨x 0, hx, rfl⟩⟩
        refine ⟨⟨p, ?_⟩, ?_⟩
        · rw [← h]
          exact hc _ _ (rep_rel _ _)
        · refine (realize_pairF _ _ _ _).2 ?_
          rw [hEq j hj]
          exact (part ms j).symm (rep_rel _ _)

end Core

/-! ### The number of parameters -/

theorem card_params_le (hm : IsMergeSequence G ms) {j : ℕ} (hj : j < ms.length) {r : ℕ}
    {v : Fin n} {B : Set (Fin n)} (hB : B ⊆ graphBall (rel ms (j + 1)) r {v}) :
    (params ms j B).card ≤ max 1 (mergeWidth r ms) := by
  by_cases h1 : j + 1 < ms.length
  · refine le_max_of_le_right (le_trans ?_ ((Lax185574Proofs.Conversions.BetterMerge.partCount_mono
      _ hB).trans (partCount_le_mergeWidth h1 r v)))
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (Quotient.mk (part ms j)) ?_ ?_ (Set.toFinite _)
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := mem_params.1 hp
      exact ⟨x, hx, Quotient.sound ((part ms j).symm (rep_rel _ _))⟩
    · intro p hp q hq h
      rw [← rep_params hp, ← rep_params hq]
      exact rep_eq_of_rel _ (Quotient.exact h)
  · refine le_max_of_le_left (Finset.card_le_one.2 fun p hp q hq => ?_)
    rw [← rep_params hp, ← rep_params hq]
    exact rep_eq_of_rel _ (by rw [part_last hm (by omega)]; trivial)

/-- **Local definability** of the construction sequence, given formulas
defining the stages of the merge sequence. -/
theorem isRadiusDefinable (hm : IsMergeSequence G ms) (r : ℕ)
    (hdef : ∃ φeq φR : (withColors Language.graph 2).Formula (Fin 2),
      quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧ StagesDefinable G ms φeq φR) :
    IsRadiusDefinable G (script G ms).run r (2 * ms.length + 1) (max 1 (mergeWidth r ms)) 7 := by
  obtain ⟨φeq, φR, hq1, hq2, hS⟩ := hdef
  choose C hC using hS
  let C' : ℕ → Fin 2 → Set (Fin n) := fun i => if h : i < ms.length then C i h else fun _ => ∅
  have hC' : ∀ i < ms.length, ∀ x : Fin 2 → Fin n,
      (@Formula.Realize _ _ (expansion G (C' i)) _ φeq x ↔ part ms i (x 0) (x 1)) ∧
      (@Formula.Realize _ _ (expansion G (C' i)) _ φR x ↔ (rel ms i).Adj (x 0) (x 1)) := by
    intro i hi x
    have e1 : C' i = C i hi := dif_pos hi
    have e2 : part ms i = ms[i].1 := dif_pos hi
    have e3 : rel ms i = ms[i].2 := dif_pos hi
    rw [e1, e2, e3]
    exact hC i hi x
  intro t ht v
  obtain ⟨j, hj, hg, hg'⟩ := List.isChain_iff_getElem.1 (chain_run hm) t ht
  obtain ⟨c, R, hH, hc, L, hL, rfl⟩ := hg
  obtain ⟨c', R', hH', hc', L', hL', rfl⟩ := hg'
  have hB : (script G ms).run[t + 1].ball r v ⊆ graphBall (rel ms (j + 1)) r {v} := by
    rw [hH']; exact ball_subset hm hL' r v
  refine ⟨allColors (ms := ms) C' ((script G ms).run[t + 1].ball r v),
    params ms j ((script G ms).run[t + 1].ball r v), card_params_le hm hj hB, ?_⟩
  rw [hH]
  exact definableIn_state φeq φR C' hC' hq1 hq2 hj hc hL _

end

end Lax185574Proofs.Conversions.MergeConstruction
