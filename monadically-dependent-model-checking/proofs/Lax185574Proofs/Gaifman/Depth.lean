import Lax185574Proofs.Gaifman.Normalization

/-!
The quantifier depth of local formulas in the normal form.

A local formula has primitive ball-restricted quantifiers. Its depth is the
nesting depth of these quantifiers. This module shows that the depth of
every local formula in the normal form of a formula of quantifier rank `q`
with `k` free variables is bounded in terms of `q`, `k` and the largest
arity `A` of the vocabulary, and not otherwise in terms of the vocabulary.
Every construction of the normalization nests quantifiers additively. It
inserts guards (distance formulas of radius at most the current radius,
whose quantifier rank is at most the radius plus `A`) below quantifiers,
and it takes Boolean combinations, which do not increase the depth.
-/

namespace Lax185574Proofs.Gaifman.Depth

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.FirstOrder
open Lax185574Proofs.Gaifman.Locality Lax185574Proofs.Gaifman.GaifmanNormalForm

/-- The nesting depth of the ball-restricted quantifiers of a local
formula. -/
def depth {σ : Vocabulary} {k r : ℕ} : {b : ℕ} → LocalFormula σ k r b → ℕ
  | _, .rel _ _ => 0
  | _, .eq _ _ => 0
  | _, .not φ => depth φ
  | _, .or φ ψ => max (depth φ) (depth ψ)
  | _, .ex φ => depth φ + 1

/-- Every relation symbol of `σ` has arity at most `A`. -/
def ArityLE (σ : Vocabulary) (A : ℕ) : Prop := ∀ R : σ.Relation, σ.arity R ≤ A

/-! ### Ordinary formulas -/

section formulas

open Lax185574Proofs.Gaifman.FormulaUtils

theorem qr_rename {σ : Vocabulary} : ∀ {k k' : ℕ} (f : Fin k → Fin k') (φ : Formula σ k),
    (Formula.rename f φ).quantifierRank = φ.quantifierRank
  | _, _, _, .rel _ _ => rfl
  | _, _, _, .eq _ _ => rfl
  | _, _, f, .not φ => by
    simp only [Formula.rename, Formula.quantifierRank]; exact qr_rename f φ
  | _, _, f, .or φ ψ => by
    simp only [Formula.rename, Formula.quantifierRank, qr_rename f φ, qr_rename f ψ]
  | _, _, f, .ex φ => by
    simp only [Formula.rename, Formula.quantifierRank, qr_rename _ φ]

theorem qr_conjunction {σ : Vocabulary} {k : ℕ} (φ ψ : Formula σ k) :
    (Formula.conjunction φ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := rfl

theorem qr_disjunctions_le {σ : Vocabulary} {k : ℕ} (f : Formula σ k) (D : ℕ)
    (hf : f.quantifierRank ≤ D) :
    ∀ (l : List (Formula σ k)), (∀ φ ∈ l, φ.quantifierRank ≤ D) →
      (Formula.disjunctions f l).quantifierRank ≤ D
  | [], _ => hf
  | φ :: l, h => by
    simp only [Formula.disjunctions, Formula.quantifierRank]
    exact max_le (h φ (by simp)) (qr_disjunctions_le f D hf l fun ψ hψ => h ψ (by simp [hψ]))

theorem qr_exN {σ : Vocabulary} : ∀ (n : ℕ) {k : ℕ} (φ : Formula σ (k + n)),
    (Formula.exN n φ).quantifierRank = φ.quantifierRank + n
  | 0, _, _ => rfl
  | n + 1, k, φ => by
    simp only [Formula.exN]
    rw [qr_exN n, Formula.quantifierRank]
    omega

theorem qr_adjacencyFormula {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) :
    (Lax185574Proofs.Gaifman.AdjacencyFormula.adjacencyFormula σ).quantifierRank ≤ A := by
  unfold Lax185574Proofs.Gaifman.AdjacencyFormula.adjacencyFormula
  rw [qr_conjunction]
  refine max_le (Nat.zero_le _) (qr_disjunctions_le _ A (Nat.zero_le _) _ ?_)
  intro φ hφ
  simp only [Lax185574Proofs.Gaifman.AdjacencyFormula.adjacencyCases, List.mem_flatMap,
    Finset.mem_toList, Finset.mem_univ, true_and] at hφ
  obtain ⟨R, i, j, hφ⟩ := hφ
  split_ifs at hφ with hij
  · simp at hφ
  · simp only [List.mem_singleton] at hφ
    subst hφ
    unfold Lax185574Proofs.Gaifman.AdjacencyFormula.relationWitness
    rw [qr_exN]
    simpa [qr_conjunction, Formula.quantifierRank] using hA R

theorem qr_distanceFormula {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) :
    ∀ d, (Lax185574Proofs.Gaifman.DistanceFormula.distanceFormula σ d).quantifierRank ≤ d + A
  | 0 => Nat.zero_le _
  | d + 1 => by
    simp only [Lax185574Proofs.Gaifman.DistanceFormula.distanceFormula,
      Formula.quantifierRank, qr_conjunction, qr_rename]
    have h1 := qr_distanceFormula hA d
    have h2 := qr_adjacencyFormula hA
    omega

end formulas

/-! ### Local formulas -/

section localFormulas

open Lax185574Proofs.Gaifman.NormalFormOps

theorem depth_conjunction {σ : Vocabulary} {k r b : ℕ} (φ ψ : LocalFormula σ k r b) :
    depth (LocalFormula.conjunction φ ψ) = max (depth φ) (depth ψ) := rfl

theorem depth_disjunctions_le {σ : Vocabulary} {k r b : ℕ} (f : LocalFormula σ k r b)
    (D : ℕ) (hf : depth f ≤ D) :
    ∀ (l : List (LocalFormula σ k r b)), (∀ φ ∈ l, depth φ ≤ D) →
      depth (LocalFormula.disjunctions f l) ≤ D
  | [], _ => hf
  | φ :: l, h => by
    simp only [LocalFormula.disjunctions, depth]
    exact max_le (h φ (by simp)) (depth_disjunctions_le f D hf l fun ψ hψ => h ψ (by simp [hψ]))

theorem depth_relativize {σ : Vocabulary} {k b : ℕ} (r : ℕ) :
    ∀ {n : ℕ} (f : Fin n → LocalTerm σ k b) (φ : Formula σ n),
      depth (Lax185574Proofs.Gaifman.Relativize.relativize (b := b) r f φ) = φ.quantifierRank
  | _, _, .rel _ _ => rfl
  | _, _, .eq _ _ => rfl
  | _, f, .not φ => by
    simp only [Lax185574Proofs.Gaifman.Relativize.relativize, depth, Formula.quantifierRank]
    exact depth_relativize r f φ
  | _, f, .or φ ψ => by
    simp only [Lax185574Proofs.Gaifman.Relativize.relativize, depth, Formula.quantifierRank,
      depth_relativize r f φ, depth_relativize r f ψ]
  | _, f, .ex φ => by
    simp only [Lax185574Proofs.Gaifman.Relativize.relativize, depth, Formula.quantifierRank,
      depth_relativize r _ φ]

theorem depth_localDistance {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k b : ℕ}
    (R d : ℕ) (l r : LocalTerm σ k b) :
    depth (Lax185574Proofs.Gaifman.LocalDistance.localDistance R d l r) ≤ d + A := by
  unfold Lax185574Proofs.Gaifman.LocalDistance.localDistance
  rw [depth_relativize]
  exact qr_distanceFormula hA d

open Lax185574Proofs.Gaifman.NeighborhoodFormula in
theorem depth_nearAnchors {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k b : ℕ}
    (R d : ℕ) (t : LocalTerm σ k b) : depth (nearAnchors R d t) ≤ d + A := by
  apply depth_disjunctions_le _ _ (Nat.zero_le _)
  intro φ hφ
  simp only [List.mem_ofFn] at hφ
  obtain ⟨i, rfl⟩ := hφ
  exact depth_localDistance hA R d _ _

open Lax185574Proofs.Gaifman.NeighborhoodFormula in
theorem depth_nearConstants {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k b : ℕ}
    (R d : ℕ) (t : LocalTerm σ k b) : depth (nearConstants R d t) ≤ d + A := by
  apply depth_disjunctions_le _ _ (Nat.zero_le _)
  intro φ hφ
  simp only [List.mem_ofFn] at hφ
  obtain ⟨i, rfl⟩ := hφ
  exact depth_localDistance hA R d _ _

open Lax185574Proofs.Gaifman.NeighborhoodFormula in
theorem depth_nearCenters {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k b : ℕ}
    (R d : ℕ) (t : LocalTerm σ k b) : depth (nearCenters R d t) ≤ d + A := by
  apply depth_disjunctions_le _ _ (Nat.zero_le _)
  intro φ hφ
  simp only [List.mem_append, List.mem_ofFn] at hφ
  rcases hφ with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> exact depth_localDistance hA R d _ _

open Lax185574Proofs.Gaifman.Recenter in
theorem depth_nearTerms {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {n k b : ℕ}
    (S d : ℕ) (anchors : Fin n → LocalTerm σ k b) (t : LocalTerm σ k b) :
    depth (nearTerms S d anchors t) ≤ d + A := by
  apply depth_disjunctions_le _ _ (Nat.zero_le _)
  intro φ hφ
  simp only [List.mem_append, List.mem_ofFn] at hφ
  rcases hφ with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> exact depth_localDistance hA S d _ _

open Lax185574Proofs.Gaifman.RadiusChange in
theorem depth_enlarge {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k r : ℕ} (R : ℕ) :
    ∀ {b : ℕ} (φ : LocalFormula σ k r b), depth (enlarge R φ) ≤ depth φ + (r + A)
  | _, .rel _ _ => Nat.zero_le _
  | _, .eq _ _ => Nat.zero_le _
  | _, .not φ => by
    simp only [enlarge, depth]; exact depth_enlarge hA R φ
  | _, .or φ ψ => by
    simp only [enlarge, depth]
    have h1 := depth_enlarge hA R φ
    have h2 := depth_enlarge hA R ψ
    omega
  | b, .ex φ => by
    simp only [enlarge, depth, depth_conjunction]
    have h1 := depth_enlarge hA R φ
    have h2 := depth_nearCenters hA (b := b + 1) (k := k) R r (.bound (Fin.last b))
    omega

open Lax185574Proofs.Gaifman.Recenter in
theorem depth_recenter {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k r : ℕ} (S : ℕ) :
    ∀ {b k' b' : ℕ} (anchors : Fin k → LocalTerm σ k' b') (bound : Fin b → LocalTerm σ k' b')
      (φ : LocalFormula σ k r b), depth (recenter S anchors bound φ) ≤ depth φ + (r + A)
  | _, _, _, _, _, .rel _ _ => Nat.zero_le _
  | _, _, _, _, _, .eq _ _ => Nat.zero_le _
  | _, _, _, anchors, bound, .not φ => by
    simp only [recenter, depth]; exact depth_recenter hA S anchors bound φ
  | _, _, _, anchors, bound, .or φ ψ => by
    simp only [recenter, depth]
    have h1 := depth_recenter hA S anchors bound φ
    have h2 := depth_recenter hA S anchors bound ψ
    omega
  | _, _, b', anchors, bound, .ex φ => by
    simp only [recenter, depth, depth_conjunction]
    have h1 := depth_recenter hA S (liftTerms anchors) (extendBoundTerms bound) φ
    have h2 := depth_nearTerms hA S r (liftTerms anchors) (.bound (Fin.last b'))
    omega

end localFormulas

/-! ### Tuples, separation and local elimination -/

section elimination

open Lax185574Proofs.Gaifman.NormalFormOps Lax185574Proofs.Gaifman.LocalTuples
open Lax185574Proofs.Gaifman.Separation Lax185574Proofs.Gaifman.LocalElimination
open Lax185574Proofs.Gaifman.NeighborhoodFormula Lax185574Proofs.Gaifman.RadiusChange
open Lax185574Proofs.Gaifman.Recenter Lax185574Proofs.Gaifman.LocalDistance

theorem depth_conjunctions_le {σ : Vocabulary} {k R b : ℕ} (t : LocalFormula σ k R b)
    (D : ℕ) (ht : depth t ≤ D) :
    ∀ (l : List (LocalFormula σ k R b)), (∀ φ ∈ l, depth φ ≤ D) →
      depth (conjunctions t l) ≤ D
  | [], _ => ht
  | φ :: l, h => by
    simp only [conjunctions, depth_conjunction]
    exact max_le (h φ (by simp)) (depth_conjunctions_le t D ht l fun ψ hψ => h ψ (by simp [hψ]))

theorem depth_closeExists {σ : Vocabulary} {k R : ℕ} :
    ∀ (n : ℕ) (φ : LocalFormula σ k R n), depth (closeExists n φ) = depth φ + n
  | 0, _ => rfl
  | n + 1, φ => by
    simp only [closeExists]
    rw [depth_closeExists n, depth]
    omega

theorem depth_negPairs {σ : Vocabulary} {k R a b : ℕ} (i : Fin k) (D : ℕ) :
    ∀ (ps : List (LocalFormula σ k R a × LocalFormula σ 1 R b)),
      (∀ p ∈ ps, depth p.1 ≤ D ∧ depth p.2 ≤ D) →
        ∀ q ∈ negPairs i ps, depth q.1 ≤ D ∧ depth q.2 ≤ D
  | [], _, q, hq => by
    simp only [negPairs, List.mem_singleton] at hq
    subst hq
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | p :: ps, h, q, hq => by
    simp only [negPairs, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hq
    obtain ⟨q', hq', hq⟩ := hq
    have h' := depth_negPairs i D ps (fun p hp => h p (by simp [hp])) q' hq'
    have hp := h p (by simp)
    rcases hq with rfl | rfl
    · simp only [depth_conjunction, depth]
      exact ⟨max_le hp.1 h'.1, h'.2⟩
    · simp only [depth_conjunction, depth]
      exact ⟨h'.1, max_le hp.2 h'.2⟩

theorem depth_separate {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k R : ℕ} (i0 : Fin k) :
    ∀ {B a b : ℕ} (side : Fin B → Fin a ⊕ Fin b) (φ : LocalFormula σ (k + 1) R B),
      ∀ p ∈ separate i0 side φ, depth p.1 ≤ depth φ + (R + A) ∧ depth p.2 ≤ depth φ + (R + A)
  | _, _, _, side, .rel Q args, p, hp => by
    simp only [separate] at hp
    split_ifs at hp <;> simp only [List.mem_singleton, List.not_mem_nil] at hp <;> subst hp <;>
      exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | _, _, _, side, .eq l r, p, hp => by
    simp only [separate] at hp
    split at hp <;> simp only [List.mem_singleton, List.not_mem_nil] at hp <;> subst hp <;>
      exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | _, _, _, side, .not φ, p, hp => by
    have ih := depth_separate hA i0 side φ
    exact depth_negPairs i0 _ _ ih p hp
  | _, _, _, side, .or φ ψ, p, hp => by
    simp only [separate, List.mem_append] at hp
    simp only [depth]
    rcases hp with hp | hp
    · have := depth_separate hA i0 side φ p hp
      omega
    · have := depth_separate hA i0 side ψ p hp
      omega
  | _, _, b, side, .ex φ, p, hp => by
    simp only [separate, List.mem_append, wrapLeft, wrapRight, List.mem_map] at hp
    simp only [depth]
    rcases hp with ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
    · have := depth_separate hA i0 (extendLeft side) φ p' hp'
      simp only [depth]
      omega
    · have := depth_separate hA i0 (extendRight side) φ p' hp'
      have hn := depth_nearAnchors hA (k := 1) (b := b + 1) R R (.bound (Fin.last b))
      simp only [depth, depth_conjunction]
      omega

theorem depth_nearPart {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k R : ℕ} (S T : ℕ)
    (ψ : LocalFormula σ (k + 1) R 0) :
    depth (nearPart S T ψ) ≤ depth ψ + 1 + T + R + A := by
  simp only [nearPart, depth, depth_conjunction]
  have h1 := depth_nearCenters hA (k := k) (b := 1) S T (.bound 0)
  have h2 := depth_recenter hA S (sourceAnchorTerms (σ := σ) (k := k)) Fin.elim0 ψ
  omega

theorem depth_farProperty {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {R : ℕ} (T : ℕ)
    (β : LocalFormula σ 1 R 0) : depth (farProperty T β) ≤ depth β + T + R + A := by
  simp only [farProperty, depth_conjunction, depth]
  have h1 := depth_enlarge hA T β
  have h2 := depth_nearConstants hA (k := 1) (b := 0) T T (.anchor 0)
  omega

theorem depth_nearScatterFormula {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k n T : ℕ}
    (i0 : Fin k) (S : ℕ) (γ : LocalFormula σ 1 T 0) :
    depth (nearScatterFormula (n := n) i0 S γ) ≤ depth γ + n + 2 * T + A := by
  unfold nearScatterFormula
  rw [depth_closeExists]
  have hbody : depth (nearScatterBody (n := n) i0 S γ) ≤ depth γ + 2 * T + A := by
    apply depth_conjunctions_le _ _ (Nat.zero_le _)
    intro φ hφ
    simp only [List.mem_append, List.mem_ofFn] at hφ
    rcases hφ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp only [scatterWitnessClause, depth_conjunction]
      have h1 := depth_nearAnchors hA (k := k) (b := n) S T (.bound i)
      have h2 := depth_recenter hA S (fun _ : Fin 1 => (LocalTerm.bound i : LocalTerm σ k n))
        Fin.elim0 γ
      omega
    · apply depth_conjunctions_le _ _ (Nat.zero_le _)
      intro ψ hψ
      simp only [List.mem_ofFn] at hψ
      obtain ⟨j, rfl⟩ := hψ
      unfold scatterPairClause
      split_ifs
      · exact Nat.zero_le _
      · simp only [depth]
        have := depth_localDistance hA (k := k) (b := n) S (2 * T) (.bound i) (.bound j)
        omega
  omega

theorem depth_annulusFormula {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) {k R : ℕ}
    (S T : ℕ) (β : LocalFormula σ 1 R 0) :
    depth (annulusFormula (k := k) S T β) ≤ depth β + 1 + 3 * T + R + A := by
  simp only [annulusFormula, depth, depth_conjunction]
  have h1 := depth_nearAnchors hA (k := k) (b := 1) S (3 * T) (.bound 0)
  have h2 := depth_nearAnchors hA (k := k) (b := 1) S T (.bound 0)
  have h3 := depth_recenter hA S (fun _ : Fin 1 => (LocalTerm.bound 0 : LocalTerm σ k 1))
    Fin.elim0 β
  have h4 := depth_nearConstants hA (k := k) (b := 1) S T (.bound 0)
  omega

end elimination

/-! ### Normal forms -/

/-- The depth of an atom of a normal form: the depth of the local formula,
or of the property of the basic local sentence. -/
def atomDepth {σ : Vocabulary} {k : ℕ} : NormalAtom σ k → ℕ
  | .local _ φ => depth φ
  | .basic _ β => depth β.property

/-- Every atom of `nf` has depth at most `D`. -/
def DepthBounded {σ : Vocabulary} {k : ℕ} (nf : NormalForm σ k) (D : ℕ) : Prop :=
  ∀ atom ∈ nf.body.atoms, atomDepth atom ≤ D

section normalForms

open Lax185574Proofs.Gaifman.NormalFormOps Lax185574Proofs.Gaifman.LocalElimination
open Lax185574Proofs.Gaifman.ExistentialNormalForm Lax185574Proofs.Gaifman.RadiusChange
open Lax185574Proofs.Gaifman.BooleanCombination

variable {σ : Vocabulary} {k : ℕ}

theorem depthBounded_mono {nf : NormalForm σ k} {D D' : ℕ} (h : DepthBounded nf D)
    (hD : D ≤ D') : DepthBounded nf D' := fun a ha => (h a ha).trans hD

theorem depthBounded_truth {D : ℕ} : DepthBounded (NormalForm.truth σ k) D := by
  intro atom h
  simp [NormalForm.truth, Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination.atoms] at h

theorem depthBounded_neg {nf : NormalForm σ k} {D : ℕ} (h : DepthBounded nf D) :
    DepthBounded (NormalForm.neg nf) D := fun atom ha => h atom ha

theorem depthBounded_conj {l r : NormalForm σ k} {D : ℕ} (hl : DepthBounded l D)
    (hr : DepthBounded r D) : DepthBounded (NormalForm.conj l r) D := by
  intro atom ha
  simp only [NormalForm.conj, Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_append] at ha
  exact ha.elim (hl atom) (hr atom)

theorem depthBounded_disj {l r : NormalForm σ k} {D : ℕ} (hl : DepthBounded l D)
    (hr : DepthBounded r D) : DepthBounded (NormalForm.disj l r) D := by
  intro atom ha
  simp only [NormalForm.disj, BooleanCombination.or,
    Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_append] at ha
  exact ha.elim (hl atom) (hr atom)

theorem depthBounded_ofLocal {r D : ℕ} (φ : LocalFormula σ k r 0) (h : depth φ ≤ D) :
    DepthBounded (NormalForm.ofLocal φ) D := by
  intro atom ha
  simp only [NormalForm.ofLocal,
    Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_singleton] at ha
  subst atom
  exact h

theorem depthBounded_ofBasic {r D : ℕ} (β : BasicLocalSentence σ r) (h : depth β.property ≤ D) :
    DepthBounded (NormalForm.ofBasic (k := k) β) D := by
  intro atom ha
  simp only [NormalForm.ofBasic,
    Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination.atoms,
    List.mem_singleton] at ha
  subst atom
  exact h

theorem depthBounded_disjunctionsNF {D : ℕ} :
    ∀ {nfs : List (NormalForm σ k)}, (∀ nf ∈ nfs, DepthBounded nf D) →
      DepthBounded (disjunctionsNF nfs) D
  | [], _ => depthBounded_neg depthBounded_truth
  | nf :: nfs, h => depthBounded_disj (h nf (by simp))
      (depthBounded_disjunctionsNF fun nf' hnf' => h nf' (by simp [hnf']))

variable {A : ℕ} (hA : ArityLE σ A)
include hA

theorem depthBounded_farCaseNormalForm {R T S : ℕ} (i0 : Fin k) (β : LocalFormula σ 1 R 0)
    (l : ℕ) : DepthBounded (farCaseNormalForm i0 T S β l)
      (depth β + l + 1 + R + 3 * T + 2 * A) := by
  have hγ := depth_farProperty hA T β
  have hn := depth_nearScatterFormula hA (n := l) i0 S (farProperty T β)
  have han := depth_annulusFormula hA (k := k) S T β
  apply depthBounded_conj
  · exact depthBounded_ofBasic _ (by simp only [scatterSentence]; omega)
  · apply depthBounded_conj
    · exact depthBounded_neg
        (depthBounded_ofBasic _ (by simp only [scatterSentence]; omega))
    · exact depthBounded_disj (depthBounded_neg (depthBounded_ofLocal _ (by omega)))
        (depthBounded_ofLocal _ (by omega))

theorem depthBounded_farWitnessNormalForm {R T S : ℕ} (i0 : Fin k)
    (β : LocalFormula σ 1 R 0) :
    DepthBounded (farWitnessNormalForm i0 T S β) (depth β + k + 1 + R + 3 * T + 2 * A) := by
  have hγ := depth_farProperty hA T β
  apply depthBounded_disj
  · exact depthBounded_ofBasic _ (by simp only [scatterSentence]; omega)
  · apply depthBounded_disjunctionsNF
    intro nf hnf
    simp only [List.mem_ofFn] at hnf
    obtain ⟨i, rfl⟩ := hnf
    exact depthBounded_mono (depthBounded_farCaseNormalForm hA i0 β (i.val + 1))
      (by have := i.2; omega)

theorem depthBounded_eliminateLocal {R T S : ℕ} (i0 : Fin k)
    (ψ : LocalFormula σ (k + 1) R 0) :
    DepthBounded (eliminateLocal i0 T S ψ) (depth ψ + k + 1 + 3 * R + 3 * T + 3 * A) := by
  apply depthBounded_disj
  · exact depthBounded_ofLocal _ (by have := depth_nearPart hA S T ψ; omega)
  · apply depthBounded_disjunctionsNF
    intro nf hnf
    simp only [List.mem_map] at hnf
    obtain ⟨p, hp, rfl⟩ := hnf
    have hsep := depth_separate hA i0 Fin.elim0 ψ p hp
    apply depthBounded_conj
    · exact depthBounded_ofLocal _ (by have := depth_enlarge hA S p.1; omega)
    · exact depthBounded_mono (depthBounded_farWitnessNormalForm hA i0 p.2) (by omega)

omit hA in
theorem depth_interp {k R : ℕ} (t : LocalFormula σ k R 0) (D : ℕ) (ht : depth t ≤ D) :
    ∀ (b : Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination (LocalFormula σ k R 0)),
      (∀ φ ∈ b.atoms, depth φ ≤ D) →
        depth (BooleanCombination.interp t LocalFormula.not LocalFormula.conjunction b) ≤ D
  | .atom a, h => h a (by simp [Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination.atoms])
  | .truth, _ => ht
  | .not b, h => by
    simp only [BooleanCombination.interp, depth]
    exact depth_interp t D ht b h
  | .and b c, h => by
    simp only [BooleanCombination.interp, depth_conjunction]
    exact max_le
      (depth_interp t D ht b fun φ hφ => h φ (by
        simp [Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination.atoms, hφ]))
      (depth_interp t D ht c fun φ hφ => h φ (by
        simp [Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination.atoms, hφ]))

theorem depth_combineLocal {R D : ℕ}
    (b : Lax185574Proofs.Gaifman.GaifmanNormalForm.BooleanCombination (LocalPiece σ (k + 1)))
    (h : ∀ p ∈ b.atoms, depth p.formula ≤ D ∧ p.radius ≤ R) :
    depth (combineLocal R b) ≤ D + R + A := by
  unfold combineLocal
  apply depth_interp _ _ (Nat.zero_le _)
  intro φ hφ
  simp only [BooleanCombination.atoms_map, List.mem_map] at hφ
  obtain ⟨p, hp, rfl⟩ := hφ
  have := depth_enlarge hA R p.formula
  have := h p hp
  omega

theorem depthBounded_eliminateNormalForm {R T S D : ℕ} (nf : NormalForm σ (k + 1))
    (hradii : nf.RadiiBounded R) (hdepth : DepthBounded nf D) :
    DepthBounded (eliminateNormalForm R T S nf) (D + k + 2 + 4 * R + 3 * T + 4 * A) := by
  intro atom hatom
  simp only [eliminateNormalForm, BooleanCombination.atoms_map, List.mem_map] at hatom
  obtain ⟨x, hx, rfl⟩ := hatom
  rcases x with d | b
  · obtain ⟨τ, -, hd⟩ := BooleanCombination.mem_atoms_pullOut_left.mp hx
    have hc : depth (combineLocal R (BooleanCombination.collapse τ (splitBody nf))) ≤
        D + R + A := by
      apply depth_combineLocal hA
      intro p hp
      have hmem := localPiece_of_mem_splitBody (BooleanCombination.mem_atoms_collapse.mp hp)
      exact ⟨hdepth _ hmem, hradii _ hmem⟩
    change d ∈ (eliminateCombinedLocal T S k _).body.atoms at hd
    cases k with
    | zero =>
      have := depthBounded_ofBasic (k := 0) (scatterSentence
        (combineLocal R (BooleanCombination.collapse τ (splitBody nf))) 1) hc d hd
      simp only [Sum.elim_inl, id]
      omega
    | succ k =>
      have := depthBounded_eliminateLocal hA (Fin.last k) (T := T) (S := S)
        (combineLocal R (BooleanCombination.collapse τ (splitBody nf))) d hd
      simp only [Sum.elim_inl, id]
      omega
  · have hb := BooleanCombination.mem_atoms_pullOut_right hx
    have := hdepth _ (basicPiece_of_mem_splitBody hb)
    simp only [Sum.elim_inr, basicAtom]
    simp only [atomDepth] at this ⊢
    omega

end normalForms

/-! ### The bound for the normal form -/

/-- The depth bound for the normal form of a formula of quantifier rank `q`
with `k` free variables over a vocabulary of arity at most `A`. -/
def depthBound (A q k : ℕ) : ℕ := q * (k + q + 2 + 6 * 7 ^ q + 4 * A)

theorem depthBound_mono (A k : ℕ) {q q' : ℕ} (h : q ≤ q') : depthBound A q k ≤ depthBound A q' k := by
  have : 7 ^ q ≤ 7 ^ q' := Nat.pow_le_pow_right (by omega) h
  exact Nat.mul_le_mul h (by omega)

theorem depthBound_step (A q k : ℕ) :
    depthBound A q (k + 1) + k + 2 + 6 * 7 ^ (q + 1) + 4 * A ≤ depthBound A (q + 1) k := by
  unfold depthBound
  have hX : 7 ^ q ≤ 7 ^ (q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : q * (k + 1 + q + 2 + 6 * 7 ^ q + 4 * A) ≤
      q * (k + q + 3 + 6 * 7 ^ (q + 1) + 4 * A) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (q + 1) * (k + (q + 1) + 2 + 6 * 7 ^ (q + 1) + 4 * A) =
      q * (k + q + 3 + 6 * 7 ^ (q + 1) + 4 * A) + (k + q + 3 + 6 * 7 ^ (q + 1) + 4 * A) := by
    ring
  omega

section normalize

open Lax185574Proofs.Gaifman.NormalFormOps
open Lax185574Proofs.Gaifman.Normalization (normalize_spec rankRadius splitRadius)

theorem depthBounded_normalize {σ : Vocabulary} {A : ℕ} (hA : ArityLE σ A) :
    ∀ {k : ℕ} (φ : Formula σ k), DepthBounded (Normalization.normalize φ) (depthBound A φ.quantifierRank k)
  | _, .rel R args => depthBounded_ofLocal _ (Nat.zero_le _)
  | _, .eq l r => depthBounded_ofLocal _ (Nat.zero_le _)
  | _, .not φ => depthBounded_neg (depthBounded_normalize hA φ)
  | _, .or φ ψ => by
    simp only [Normalization.normalize, Formula.quantifierRank]
    exact depthBounded_disj
      (depthBounded_mono (depthBounded_normalize hA φ) (depthBound_mono _ _ (le_max_left _ _)))
      (depthBounded_mono (depthBounded_normalize hA ψ) (depthBound_mono _ _ (le_max_right _ _)))
  | k, .ex φ => by
    simp only [Normalization.normalize, Formula.quantifierRank]
    refine depthBounded_mono (depthBounded_eliminateNormalForm hA (Normalization.normalize φ)
      (normalize_spec.{0} φ).1 (depthBounded_normalize hA φ)) ?_
    have hstep := depthBound_step A φ.quantifierRank k
    have hpos : 0 < 7 ^ φ.quantifierRank := Nat.pow_pos (by omega)
    have hpow : 7 ^ (φ.quantifierRank + 1) = 7 * 7 ^ φ.quantifierRank := by ring
    simp only [rankRadius, splitRadius]
    omega

end normalize

end Lax185574Proofs.Gaifman.Depth
