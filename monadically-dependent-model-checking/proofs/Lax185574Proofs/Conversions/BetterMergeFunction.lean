import Lax185574.BetterMergeSequences
import Lax185574.PairRelationDefinable
import Lax185574.PairRelationMonotone
import Lax185574.PairRelationBalls
import Lax185574.HomogeneousSplitting
import Lax185574.SplitBalls
import Lax185574.SplittingMonotone
import Lax185574Proofs.PairRelationDefinable
import Lax185574Proofs.Conversions.ColorMaps

/-!
The mathematical half of lem:better-mw (`BetterMergeSequences`): the
merge sequence of the proof, as an explicit function of the graph and
the chain, and all its properties apart from the running time.

Write the chain in reverse order as V(G) = S₁ ⊇ ⋯ ⊇ S_m = ∅, let 𝒫ᵢ be
the partition into atomic types over Sᵢ, Tᵢ the set of vertices that are
minimal in their part of 𝒫ᵢ, Rᵢ = R(G, 𝒫ᵢ) and 𝒬ᵢ = 𝒫ᵢ ∧ Tᵢ. The merge
sequence is (𝒬₁, R₁), …, (𝒬_m, R_m). The order on the vertices is the
order of `Fin n`.
-/

namespace Lax185574Proofs.Conversions.BetterMerge

open FirstOrder FirstOrder.Language Lax710763.Transductions
open Lax185574.Partitions Lax185574.Flips Lax185574.GraphBalls Lax185574.MergeSequences
open Lax185574.BetterMergeSequences Lax185574.Chains Lax185574.VCDimension
open Lax185574.PairRelation Lax185574.TypeSplitting Lax185574.SplittingMonotone
open Lax185574.Colorings Lax185574.FirstOrderTypes
open Lax185574Proofs.Conversions.ColorMaps

universe z

/-! ### The function -/

section Function

variable {n : ℕ}

/-- The stage of the merge sequence for the chain set `X`: the partition
`𝒫_X ∧ T` into atomic types over `X`, split along the vertices minimal
in their part, and the pair relation `R(G, 𝒫_X)`. -/
def stage (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : Setoid (Fin n) × SimpleGraph (Fin n) :=
  (split G (atomicTypes G (X : Set (Fin n))) (minimalVertices (atomicTypes G (X : Set (Fin n)))),
    pairRelation G (atomicTypes G (X : Set (Fin n))))

/-- **The merge sequence of lem:better-mw.** The stages of the chain
sets, in reverse order. -/
def mergeSeq (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) :
    List (Setoid (Fin n) × SimpleGraph (Fin n)) :=
  S.reverse.map (stage G)

end Function

/-! ### Partitions -/

section Partitions

variable {V : Type z}

theorem split_le (G : SimpleGraph V) (P : Setoid V) (T : Set V) : split G P T ≤ P := by
  intro u v h
  change (Quotient.mk P u, _) = (Quotient.mk P v, _) at h
  exact Quotient.exact (Prod.mk.inj h).1

theorem atomicTypes_univ (G : SimpleGraph V) : atomicTypes G Set.univ = ⊥ := by
  refine le_antisymm (fun u v h => ?_) bot_le
  change (Set.univ ∩ {u}, _) = (Set.univ ∩ {v}, _) at h
  have h1 := (Prod.mk.inj h).1
  simp only [Set.univ_inter, Set.singleton_eq_singleton_iff] at h1
  rw [Setoid.bot_def]
  exact h1

theorem atomicTypes_empty (G : SimpleGraph V) : atomicTypes G ∅ = ⊤ := by
  refine le_antisymm le_top (fun u v _ => ?_)
  change ((∅ : Set V) ∩ {u}, (∅ : Set V) ∩ G.neighborSet u) = (∅ ∩ {v}, ∅ ∩ G.neighborSet v)
  simp

theorem atomicTypes_anti (G : SimpleGraph V) {X Y : Set V} (h : X ⊆ Y) :
    atomicTypes G Y ≤ atomicTypes G X := by
  intro u v huv
  change (Y ∩ {u}, Y ∩ G.neighborSet u) = (Y ∩ {v}, Y ∩ G.neighborSet v) at huv
  change (X ∩ {u}, X ∩ G.neighborSet u) = (X ∩ {v}, X ∩ G.neighborSet v)
  obtain ⟨h1, h2⟩ := Prod.mk.inj huv
  have e1 : X ∩ {u} = X ∩ (Y ∩ {u}) := by rw [← Set.inter_assoc, Set.inter_eq_left.2 h]
  have e2 : X ∩ {v} = X ∩ (Y ∩ {v}) := by rw [← Set.inter_assoc, Set.inter_eq_left.2 h]
  have e3 : X ∩ G.neighborSet u = X ∩ (Y ∩ G.neighborSet u) := by
    rw [← Set.inter_assoc, Set.inter_eq_left.2 h]
  have e4 : X ∩ G.neighborSet v = X ∩ (Y ∩ G.neighborSet v) := by
    rw [← Set.inter_assoc, Set.inter_eq_left.2 h]
  rw [e1, e2, e3, e4, h1, h2]

theorem split_bot (G : SimpleGraph V) (T : Set V) : split G ⊥ T = ⊥ :=
  le_antisymm (split_le G ⊥ T) bot_le

theorem split_top (G : SimpleGraph V) (T : Set V) : split G ⊤ T = ⊤ := by
  refine le_antisymm le_top (fun u v _ => ?_)
  change (Quotient.mk (⊤ : Setoid V) u, {t | t ∈ T ∧ ¬ (⊤ : Setoid V) t u} ∩ G.neighborSet u) =
    (Quotient.mk (⊤ : Setoid V) v, {t | t ∈ T ∧ ¬ (⊤ : Setoid V) t v} ∩ G.neighborSet v)
  refine Prod.ext (Quotient.sound trivial) ?_
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  have : (⊤ : Setoid V) t u := trivial
  have : (⊤ : Setoid V) t v := trivial
  tauto

/-- The vertices minimal in their part form a transversal. -/
theorem isTransversal_minimalVertices {n : ℕ} (P : Setoid (Fin n)) :
    IsTransversal P (minimalVertices P) := by
  classical
  intro v
  let s : Finset (Fin n) := Finset.univ.filter fun u => P u v
  have hs : s.Nonempty := ⟨v, by simp [s]⟩
  refine ⟨s.min' hs, ⟨fun u hu => ?_, ?_⟩, ?_⟩
  · have hm := Finset.min'_mem s hs
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact Finset.min'_le s u (by simp [s, P.trans hu hm])
  · have hm := Finset.min'_mem s hs
    simpa [s] using hm
  · rintro t ⟨ht, htv⟩
    have hm := Finset.min'_mem s hs
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    refine le_antisymm ?_ (Finset.min'_le s t (by simp [s, htv]))
    exact ht _ (P.trans hm (P.symm htv))

/-- Being in the same part of `𝒫 ∧ T`: the same part of `𝒫`, and the
same neighbors in `T` outside this part. -/
theorem split_iff (G : SimpleGraph V) (P : Setoid V) (T : Set V) (x y : V) :
    split G P T x y ↔ P x y ∧ ∀ z, z ∈ T → ¬ P z x → (G.Adj x z ↔ G.Adj y z) := by
  change (Quotient.mk P x, {t | t ∈ T ∧ ¬ P t x} ∩ G.neighborSet x) =
    (Quotient.mk P y, {t | t ∈ T ∧ ¬ P t y} ∩ G.neighborSet y) ↔ _
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hxy : P x y := Quotient.exact h1
    refine ⟨hxy, fun z hz hzx => ?_⟩
    have hzy : ¬ P z y := fun h => hzx (P.trans h (P.symm hxy))
    have := Set.ext_iff.mp h2 z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SimpleGraph.mem_neighborSet] at this
    exact ⟨fun h => (this.mp ⟨⟨hz, hzx⟩, h⟩).2, fun h => (this.mpr ⟨⟨hz, hzy⟩, h⟩).2⟩
  · rintro ⟨hxy, h⟩
    refine Prod.ext (Quotient.sound hxy) ?_
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, SimpleGraph.mem_neighborSet]
    have hiff : P z x ↔ P z y := ⟨fun h => P.trans h hxy, fun h => P.trans h (P.symm hxy)⟩
    constructor
    · rintro ⟨⟨hz, hzx⟩, ha⟩
      exact ⟨⟨hz, hiff.not.mp hzx⟩, (h z hz hzx).mp ha⟩
    · rintro ⟨⟨hz, hzy⟩, ha⟩
      exact ⟨⟨hz, hiff.not.mpr hzy⟩, (h z hz (hiff.not.mpr hzy)).mpr ha⟩

theorem partCount_mono [Finite V] (P : Setoid V) {X Y : Set V} (h : X ⊆ Y) :
    partCount P X ≤ partCount P Y :=
  Set.ncard_le_ncard (Set.image_mono h) (Set.toFinite _)

theorem partCount_le_card {n : ℕ} (P : Setoid (Fin n)) (X : Set (Fin n)) : partCount P X ≤ n :=
  (Set.ncard_image_le (Set.toFinite _)).trans ((Set.ncard_le_card _).trans (by simp))

end Partitions

/-! ### The merge sequence -/

section MergeSequence

variable {n : ℕ}

theorem getElem_mergeSeq (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) (t : ℕ)
    (ht : t < (mergeSeq n G S).length) :
    (mergeSeq n G S)[t] = stage G (S[S.length - 1 - t]'(by
      simp only [mergeSeq, List.length_map, List.length_reverse] at ht; omega)) := by
  simp [mergeSeq, List.getElem_reverse]

theorem length_mergeSeq (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) :
    (mergeSeq n G S).length = S.length := by
  simp [mergeSeq]

/-- The chain sets grow along the chain. -/
theorem chain_mono {S : List (Finset (Fin n))} (hS : IsChain S) {i j : ℕ} (hij : i ≤ j)
    (hj : j < S.length) : S[i] ⊆ S[j] := by
  obtain ⟨-, -, -, hstep⟩ := hS
  induction j, hij using Nat.le_induction with
  | base => exact subset_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hstep j hj)

/-- **The merge sequence of lem:better-mw is a merge sequence** (from
`HomogeneousSplitting`, `PairRelationMonotone` and `SplittingMonotone`). -/
theorem isMergeSequence_mergeSeq (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n)))
    (hS : IsChain S) : IsMergeSequence G (mergeSeq n G S) := by
  have hS' := hS
  obtain ⟨hne, hhead, hlast, -⟩ := hS'
  have hne' : mergeSeq n G S ≠ [] := by simpa [mergeSeq] using hne
  refine ⟨hne', ?_, ?_, ?_, ?_⟩
  · simp only [mergeSeq, List.head_map, List.head_reverse, stage, hlast, Finset.coe_univ,
      atomicTypes_univ, split_bot]
  · simp only [mergeSeq, List.getLast_map, List.getLast_reverse, stage, hhead, Finset.coe_empty,
      atomicTypes_empty, split_top]
  · intro t ht
    have hlen := length_mergeSeq G S
    have hP : ∀ (t : ℕ) (ht : t + 1 < S.length),
        atomicTypes G (S[S.length - 1 - t] : Set (Fin n)) ≤
          atomicTypes G (S[S.length - 1 - (t + 1)] : Set (Fin n)) := fun t ht =>
      atomicTypes_anti G (by exact_mod_cast chain_mono hS (by omega) (by omega))
    rw [getElem_mergeSeq, getElem_mergeSeq]
    refine ⟨?_, Lax185574.PairRelationMonotone.pairRelation_mono G _ _ (hP t (by omega))⟩
    let Ps : List (Setoid (Fin n)) :=
      S.reverse.map (fun X : Finset (Fin n) => atomicTypes G (↑X : Set (Fin n)))
    have hPs : ∀ (t : ℕ) (ht : t < Ps.length),
        Ps[t] = atomicTypes G (S[S.length - 1 - t]'(by simp [Ps] at ht; omega) : Set (Fin n)) := by
      intro t ht
      simp [Ps, List.getElem_reverse]
    have hlenPs : Ps.length = S.length := by simp [Ps]
    have := split_minimalVertices_mono G Ps (fun t ht => by
      rw [hPs, hPs]; exact hP t (by omega)) t (by omega)
    rw [hPs, hPs] at this
    exact this
  · intro t ht
    rw [getElem_mergeSeq]
    exact Lax185574.HomogeneousSplitting.homogeneousModulo_split G _ _
      (isTransversal_minimalVertices _)

/-- The chain width bounds the number of parts of the finer partition in
a flip ball of the coarser one. -/
theorem partCount_le_chainWidth (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) (r t : ℕ)
    (ht : t + 1 < S.length) (v : Fin n) :
    partCount (atomicTypes G (S[t + 1] : Set (Fin n)))
      (flipBall G (atomicTypes G (S[t] : Set (Fin n))) r v) ≤ chainWidth G r S := by
  refine le_csSup ⟨n, ?_⟩ ⟨t, ht, v, rfl⟩
  rintro K ⟨t, ht, w, rfl⟩
  exact partCount_le_card _ _

/-- **The width bound of lem:better-mw** (from `SplitBalls` and
`PairRelationBalls`). -/
theorem mergeWidth_mergeSeq_le (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n)))
    (hS : IsChain S) (r : ℕ) :
    mergeWidth r (mergeSeq n G S) ≤
      chainWidth G (5 * r + 1) S * neighborhoodComplexity G (chainWidth G (5 * r + 1) S) := by
  apply csSup_le'
  rintro K ⟨t, ht, v, rfl⟩
  have hlen := length_mergeSeq G S
  rw [getElem_mergeSeq, getElem_mergeSeq]
  simp only [stage]
  obtain ⟨i, hi⟩ : ∃ i, S.length - 1 - (t + 1) = i := ⟨_, rfl⟩
  have hi1 : S.length - 1 - t = i + 1 := by omega
  have hiS : i + 1 < S.length := by omega
  simp only [hi, hi1]
  have hPQ : atomicTypes G (S[i + 1] : Set (Fin n)) ≤ atomicTypes G (S[i] : Set (Fin n)) :=
    atomicTypes_anti G (by exact_mod_cast chain_mono hS (Nat.le_succ i) hiS)
  refine (partCount_mono _ (Lax185574.PairRelationBalls.graphBall_pairRelation_subset G _ r v)).trans ?_
  exact Lax185574.SplitBalls.partCount_split_le G _ _ _ (5 * r) _ hPQ
    (isTransversal_minimalVertices _) (fun w => partCount_le_chainWidth G S (5 * r + 1) i hiS w) v

end MergeSequence

/-! ### Definability of the stages -/

section Formulas

open Lax185574Proofs.PairRelationDefinable (theta theta_iff qr_theta)
open Lax185574Proofs.DistanceFormulaRank

/-- The language of graphs with two colors. -/
abbrev L2 : Language := withColors Language.graph 2

/-- The adjacency atom of `L2`. -/
def adj2 {β : Type} {m : ℕ} (t s : L2.Term (β ⊕ Fin m)) : L2.BoundedFormula β m :=
  Relations.boundedFormula₂ (Sum.inl Language.adj : L2.Relations 2) t s

/-- The atom of the second color of `L2`, marking `T`. -/
def colT {β : Type} {m : ℕ} (t : L2.Term (β ⊕ Fin m)) : L2.BoundedFormula β m :=
  Relations.boundedFormula₁ (Sum.inr (ColorRel.color 1) : L2.Relations 1) t

/-- `θ_S` with the first color of `L2` marking `S`. -/
def theta2 {β : Type} (a b : β) : L2.Formula β := recolor (fun _ : Fin 1 => (0 : Fin 2)) (theta a b)

/-- The body of the quantifier of `φ_≡`, with free variables `x, y, z`:
if `z ∈ T` lies outside the part of `x`, then `x` and `y` agree on `z`. -/
def eqBody : L2.Formula (Fin 3) :=
  (colT (Term.var (Sum.inl 2)) ⊓ ∼(theta2 2 0)) ⟹
    (adj2 (Term.var (Sum.inl 0)) (Term.var (Sum.inl 2))).iff
      (adj2 (Term.var (Sum.inl 1)) (Term.var (Sum.inl 2)))

/-- The variable map sending `z` to the bound variable. -/
def zVar : Fin 3 → Fin 2 ⊕ Fin 1 := ![Sum.inl 0, Sum.inl 1, Sum.inr 0]

/-- **`φ_≡(x, y)`**, of quantifier rank `2`: `x` and `y` lie in the same
part of `𝒫_S`, and agree on the vertices of `T` outside this part. -/
def phiEq : L2.Formula (Fin 2) :=
  theta2 0 1 ⊓ BoundedFormula.all (BoundedFormula.relabel zVar eqBody)

theorem qr_phiEq : quantifierRank phiEq ≤ 2 := by
  have h1 : quantifierRank (theta2 (0 : Fin 2) 1) ≤ 1 := by
    rw [theta2, quantifierRank_recolor]; exact qr_theta _ _
  have h2 : quantifierRank (theta2 (2 : Fin 3) 0) ≤ 1 := by
    rw [theta2, quantifierRank_recolor]; exact qr_theta _ _
  simp only [phiEq, qr_inf, quantifierRank, qr_relabel, eqBody, BoundedFormula.iff]
  simp [quantifierRank, adj2, colT, Relations.boundedFormula₁, Relations.boundedFormula₂,
    Relations.boundedFormula]
  omega

variable {V : Type z} (G : SimpleGraph V) (S T : Set V)

theorem theta2_iff {β : Type} (a b : β) (v : β → V) :
    @Formula.Realize _ V (expansion G ![S, T]) _ (theta2 a b) v ↔
      atomicTypes G S (v a) (v b) := by
  rw [theta2, realize_recolor_formula]
  have : (![S, T] ∘ fun _ : Fin 1 => (0 : Fin 2)) = fun _ => S := by funext; rfl
  rw [this]
  exact theta_iff G S a b v

theorem phiEq_iff (x : Fin 2 → V) :
    @Formula.Realize _ V (expansion G ![S, T]) _ phiEq x ↔
      split G (atomicTypes G S) T (x 0) (x 1) := by
  let _ := expansion G ![S, T]
  rw [split_iff]
  simp only [phiEq, Formula.Realize, BoundedFormula.realize_inf, BoundedFormula.realize_all]
  refine and_congr (theta2_iff G S T 0 1 x) (forall_congr' fun z => ?_)
  rw [BoundedFormula.realize_relabel]
  have hv : (Sum.elim x (Fin.snoc (default : Fin 0 → V) z ∘ Fin.castAdd 0) ∘ zVar) = ![x 0, x 1, z] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  have hθ := theta2_iff G S T (2 : Fin 3) 0 ![x 0, x 1, z]
  unfold Formula.Realize at hθ
  simp only [eqBody, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, BoundedFormula.realize_iff]
  have hθ' : BoundedFormula.Realize (theta2 (2 : Fin 3) 0) ![x 0, x 1, z]
      (Fin.snoc (default : Fin 0 → V) z ∘ Fin.natAdd 1) ↔ atomicTypes G S z (x 0) := by
    rw [show (Fin.snoc (default : Fin 0 → V) z ∘ Fin.natAdd 1 : Fin 0 → V) = default from
      Subsingleton.elim _ _]
    exact hθ
  rw [hθ']
  change (z ∈ T ∧ ¬ atomicTypes G S z (x 0) → (G.Adj (x 0) z ↔ G.Adj (x 1) z)) ↔ _
  constructor
  · intro h hz hzx; exact h ⟨hz, hzx⟩
  · rintro h ⟨hz, hzx⟩; exact h hz hzx

/-- **Definability of the stages** (from `PairRelationDefinable`). Two
fixed formulas of quantifier rank at most `5` define the stages of the
merge sequence, with the first color marking the chain set and the
second the vertices minimal in their part. -/
theorem exists_formulas_stagesDefinable :
    ∃ (φeq φR : L2.Formula (Fin 2)), quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))),
        StagesDefinable G (mergeSeq n G S) φeq φR := by
  obtain ⟨φ, hφq, hφ⟩ := Lax185574.PairRelationDefinable.exists_formula_pairRelation.{0}
  refine ⟨phiEq, recolor (fun _ : Fin 1 => (0 : Fin 2)) φ, qr_phiEq.trans (by norm_num),
    by rw [quantifierRank_recolor]; exact hφq, fun n G S t ht => ?_⟩
  rw [getElem_mergeSeq]
  let X : Set (Fin n) := (S[S.length - 1 - t]'(by
    simp only [mergeSeq, List.length_map, List.length_reverse] at ht; omega) : Set (Fin n))
  refine ⟨![X, minimalVertices (atomicTypes G X)], fun x => ⟨phiEq_iff G _ _ x, ?_⟩⟩
  rw [realize_recolor_formula]
  have : (![X, minimalVertices (atomicTypes G X)] ∘ fun _ : Fin 1 => (0 : Fin 2)) = fun _ => X := by
    funext; rfl
  rw [this]
  exact hφ G X x

end Formulas

/-- **The properties of the merge sequence of lem:better-mw**, apart from
definability: it is a merge sequence of the same length as the chain,
and its radius-`r` width is at most `k · π_G(k)` for the radius-`(5r+1)`
width `k` of the chain. -/
theorem mergeSeq_properties (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n)))
    (hS : IsChain S) :
    IsMergeSequence G (mergeSeq n G S) ∧ (mergeSeq n G S).length = S.length ∧
      ∀ r : ℕ, 1 ≤ r →
        mergeWidth r (mergeSeq n G S) ≤
          chainWidth G (5 * r + 1) S * neighborhoodComplexity G (chainWidth G (5 * r + 1) S) :=
  ⟨isMergeSequence_mergeSeq G S hS, length_mergeSeq G S,
    fun r _ => mergeWidth_mergeSeq_le G S hS r⟩

/-- **The function lemma of lem:better-mw**, in the form of
`BetterMergeSequences.exists_mergeSequence_of_chain` without the program:
two fixed formulas of quantifier rank at most `5`, and the merge
sequence `mergeSeq` with all properties apart from the running time. -/
theorem exists_formulas_mergeSeq :
    ∃ (φeq φR : (withColors Language.graph 2).Formula (Fin 2)),
      quantifierRank φeq ≤ 5 ∧ quantifierRank φR ≤ 5 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        IsMergeSequence G (mergeSeq n G S) ∧ (mergeSeq n G S).length = S.length ∧
          StagesDefinable G (mergeSeq n G S) φeq φR ∧
          ∀ r : ℕ, 1 ≤ r →
            mergeWidth r (mergeSeq n G S) ≤
              chainWidth G (5 * r + 1) S *
                neighborhoodComplexity G (chainWidth G (5 * r + 1) S) := by
  obtain ⟨φeq, φR, h1, h2, h3⟩ := exists_formulas_stagesDefinable
  refine ⟨φeq, φR, h1, h2, fun n G S hS => ?_⟩
  obtain ⟨a, b, c⟩ := mergeSeq_properties n G S hS
  exact ⟨a, b, h3 n G S, c⟩

end Lax185574Proofs.Conversions.BetterMerge
