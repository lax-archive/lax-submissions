import Lax185574Proofs.Gaifman.LocalTuples
import Mathlib.Tactic

/-!
Elimination of one existential quantifier from a local formula.  The near case
remains local. The far case is converted, via the finite scatter lemma, into a
Boolean combination of local formulas and basic local sentences.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/LocalElimination.lean`.
-/

namespace Lax185574Proofs.Gaifman.LocalElimination

noncomputable section

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.GaifmanNormalForm
open Lax185574Proofs.Gaifman.Distance Lax185574Proofs.Gaifman.NormalFormOps
open Lax185574Proofs.Gaifman.NeighborhoodFormula Lax185574Proofs.Gaifman.RadiusChange
open Lax185574Proofs.Gaifman.Recenter Lax185574Proofs.Gaifman.Scatter
open Lax185574Proofs.Gaifman.Separation Lax185574Proofs.Gaifman.LocalTuples
open Lax185574Proofs.Gaifman.LocalDistance
open Lax185574Proofs.Gaifman.BooleanCombination

/-- The old `k+1` anchors represented in a context with the first `k` anchors
and one newly bound variable. -/
def sourceAnchorTerms {σ : Vocabulary} {k : ℕ} :
    Fin (k + 1) → LocalTerm σ k 1 :=
  Fin.lastCases (.bound 0) (fun i => .anchor i)

theorem eval_sourceAnchorTerms {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (y : M) :
    (fun i => (sourceAnchorTerms (σ := σ) i).eval A env (fun _ => y)) =
      Fin.snoc env y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [sourceAnchorTerms, LocalTerm.eval]
  · simp [sourceAnchorTerms, LocalTerm.eval]

/-- The near part of an existential local formula. -/
def nearPart {σ : Vocabulary} {k R : ℕ} (S T : ℕ)
    (ψ : LocalFormula σ (k + 1) R 0) : LocalFormula σ k S 0 :=
  .ex (LocalFormula.conjunction
    (nearCenters S T (.bound 0))
    (recenter S (sourceAnchorTerms (σ := σ)) Fin.elim0 ψ))

theorem sat_nearPart {σ : Vocabulary} {M : Type*} {k R S T : ℕ}
    (A : Structure σ M) (env : Fin k → M)
    (ψ : LocalFormula σ (k + 1) R 0)
    (hTS : T ≤ S) (hTRS : T + R ≤ S) :
    (nearPart S T ψ).Sat A env Fin.elim0 ↔
      ∃ y, inBallAround A T env y ∧
        ψ.Sat A (Fin.snoc env y) Fin.elim0 := by
  simp only [nearPart, LocalFormula.Sat, LocalFormula.sat_conjunction]
  constructor
  · rintro ⟨y, -, hy, hψ⟩
    have hy' : inBallAround A T env y := by
      have h := (sat_nearCenters A env (fun _ => y) (.bound 0) hTS).mp hy
      simpa [LocalTerm.eval] using h
    have hanchors : ∀ i, inBallAround A T env
        ((sourceAnchorTerms (σ := σ) i).eval A env (fun _ => y)) := by
      intro i
      induction i using Fin.lastCases with
      | last => simpa [sourceAnchorTerms, LocalTerm.eval] using hy'
      | cast i =>
          simpa [sourceAnchorTerms, LocalTerm.eval] using
            (anchor_inBallAround A env i)
    have hψ' := (sat_recenter A env (fun _ => y)
      (sourceAnchorTerms (σ := σ)) Fin.elim0 ψ hanchors hTRS).mp hψ
    rw [eval_sourceAnchorTerms A env y] at hψ'
    have hempty :
        (fun i => (Fin.elim0 i : LocalTerm σ k 1).eval A env (fun _ => y)) =
          (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    rw [hempty] at hψ'
    exact ⟨y, hy', hψ'⟩
  · rintro ⟨y, hy, hψ⟩
    have hyS := inBallAround_mono A hTS env hy
    have hanchors : ∀ i, inBallAround A T env
        ((sourceAnchorTerms (σ := σ) i).eval A env (fun _ => y)) := by
      intro i
      induction i using Fin.lastCases with
      | last => simpa [sourceAnchorTerms, LocalTerm.eval] using hy
      | cast i =>
          simpa [sourceAnchorTerms, LocalTerm.eval] using
            (anchor_inBallAround A env i)
    refine ⟨y, hyS, ?_, ?_⟩
    · apply (sat_nearCenters A env (fun _ => y) (.bound 0) hTS).mpr
      simpa [LocalTerm.eval] using hy
    · apply (sat_recenter A env (fun _ => y)
        (sourceAnchorTerms (σ := σ)) Fin.elim0 ψ hanchors hTRS).mpr
      rw [eval_sourceAnchorTerms A env y]
      have hempty :
          (fun i => (Fin.elim0 i : LocalTerm σ k 1).eval A env (fun _ => y)) =
            (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      rw [hempty]
      exact hψ

/-- The unary property used by the far scatter argument: the separated
right-hand formula holds and the point is far from every constant. -/
def farProperty {σ : Vocabulary} {R : ℕ} (T : ℕ)
    (β : LocalFormula σ 1 R 0) : LocalFormula σ 1 T 0 :=
  LocalFormula.conjunction (enlarge T β)
    (.not (nearConstants T T (.anchor 0)))

theorem sat_farProperty {σ : Vocabulary} {M : Type*} {R T : ℕ}
    (A : Structure σ M) (y : M) (β : LocalFormula σ 1 R 0)
    (hRT : R ≤ T) :
    (farProperty T β).Sat A (fun _ => y) Fin.elim0 ↔
      β.Sat A (fun _ => y) Fin.elim0 ∧
        ¬ ∃ c : σ.Constant, distanceAtMost A T (A.constant c) y := by
  rw [farProperty, LocalFormula.sat_conjunction,
    sat_enlarge A (fun _ => y) Fin.elim0 β hRT]
  apply and_congr_right
  intro _
  apply not_congr
  simpa [LocalTerm.eval] using
    (sat_nearConstants A (fun _ => y) Fin.elim0
      (.anchor 0) (le_refl T))

/-- One tuple entry is near the free anchors and satisfies the unary scatter
property. -/
def scatterWitnessClause {σ : Vocabulary} {k n T : ℕ} (S : ℕ)
    (γ : LocalFormula σ 1 T 0) (i : Fin n) :
    LocalFormula σ k S n :=
  LocalFormula.conjunction
    (nearAnchors S T (.bound i))
    (recenter S (fun _ : Fin 1 => .bound i) Fin.elim0 γ)

/-- The pairwise-separation clause for two tuple entries. -/
def scatterPairClause {σ : Vocabulary} {k n : ℕ} (i0 : Fin k)
    (S T : ℕ) (i j : Fin n) : LocalFormula σ k S n :=
  if i = j then RadiusChange.truth i0
  else .not (localDistance S (2 * T) (.bound i) (.bound j))

/-- The quantifier-free matrix describing a near scattered tuple. -/
def nearScatterBody {σ : Vocabulary} {k n T : ℕ} (i0 : Fin k)
    (S : ℕ) (γ : LocalFormula σ 1 T 0) : LocalFormula σ k S n :=
  LocalTuples.conjunctions (RadiusChange.truth i0)
    ((List.ofFn fun i : Fin n => scatterWitnessClause S γ i) ++
      (List.ofFn fun i : Fin n =>
        LocalTuples.conjunctions (RadiusChange.truth i0)
          (List.ofFn fun j : Fin n => scatterPairClause i0 S T i j)))

/-- A local formula saying that there is an `n`-point radius-`T` scatter of
`γ` near the free anchor tuple. -/
def nearScatterFormula {σ : Vocabulary} {k n T : ℕ} (i0 : Fin k)
    (S : ℕ) (γ : LocalFormula σ 1 T 0) : LocalFormula σ k S 0 :=
  LocalTuples.closeExists n (nearScatterBody i0 S γ)

theorem sat_scatterWitnessClause {σ : Vocabulary} {M : Type*}
    {k n S T : ℕ} (A : Structure σ M) (env : Fin k → M)
    (w : Fin n → M) (γ : LocalFormula σ 1 T 0) (i : Fin n)
    (hTS : T ≤ S) (h2TS : 2 * T ≤ S) :
    (scatterWitnessClause S γ i).Sat A env w ↔
      NearTuple A T env (w i) ∧
        γ.Sat A (fun _ => w i) Fin.elim0 := by
  rw [scatterWitnessClause, LocalFormula.sat_conjunction]
  constructor
  · rintro ⟨hnear, hγ⟩
    have hnear' := (sat_nearAnchors A env w (.bound i) hTS).mp hnear
    have hball : inBallAround A T env (w i) := Or.inl hnear'
    have hanchors : ∀ _ : Fin 1, inBallAround A T env
        ((.bound i : LocalTerm σ k n).eval A env w) := fun _ => hball
    have hγ' := (sat_recenter A env w
      (fun _ : Fin 1 => (.bound i : LocalTerm σ k n)) Fin.elim0 γ
      hanchors (by omega)).mp hγ
    have hempty :
        (fun z => (Fin.elim0 z : LocalTerm σ k n).eval A env w) =
          (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    rw [hempty] at hγ'
    simpa [LocalTerm.eval] using ⟨hnear', hγ'⟩
  · rintro ⟨hnear, hγ⟩
    have hball : inBallAround A T env (w i) := Or.inl hnear
    have hanchors : ∀ _ : Fin 1, inBallAround A T env
        ((.bound i : LocalTerm σ k n).eval A env w) := fun _ => hball
    constructor
    · apply (sat_nearAnchors A env w (.bound i) hTS).mpr
      simpa [LocalTerm.eval] using hnear
    · apply (sat_recenter A env w
        (fun _ : Fin 1 => (.bound i : LocalTerm σ k n)) Fin.elim0 γ
        hanchors (by omega)).mpr
      have hempty :
          (fun z => (Fin.elim0 z : LocalTerm σ k n).eval A env w) =
            (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      rw [hempty]
      simpa [LocalTerm.eval] using hγ

theorem sat_scatterPairClause {σ : Vocabulary} {M : Type*}
    {k n S T : ℕ} (A : Structure σ M) (env : Fin k → M)
    (w : Fin n → M) (i0 : Fin k) (i j : Fin n)
    (hi : NearTuple A T env (w i)) (h3TS : 3 * T ≤ S) :
    (scatterPairClause i0 S T i j).Sat A env w ↔
      i ≠ j → ¬ distanceAtMost A (2 * T) (w i) (w j) := by
  by_cases hij : i = j
  · subst j
    simp [scatterPairClause, RadiusChange.sat_truth]
  · simp only [scatterPairClause, if_neg hij, LocalFormula.Sat]
    have hball : inBallAround A T env (w i) := Or.inl hi
    have h := sat_localDistance A env w
      (.bound i : LocalTerm σ k n) (.bound j) hball (by omega : T + 2 * T ≤ S)
    simpa [LocalTerm.eval, hij] using not_congr h

theorem sat_nearScatterBody {σ : Vocabulary} {M : Type*}
    {k n S T : ℕ} (A : Structure σ M) (env : Fin k → M)
    (w : Fin n → M) (i0 : Fin k) (γ : LocalFormula σ 1 T 0)
    (hTS : T ≤ S) (h2TS : 2 * T ≤ S) (h3TS : 3 * T ≤ S) :
    (nearScatterBody i0 S γ).Sat A env w ↔
      IsScatter A T (fun y => γ.Sat A (fun _ => y) Fin.elim0) w ∧
        ∀ i, NearTuple A T env (w i) := by
  rw [nearScatterBody, LocalTuples.sat_conjunctions A env w
    (RadiusChange.truth i0) (RadiusChange.sat_truth A env w i0)]
  constructor
  · intro hall
    have hwit : ∀ i,
        (scatterWitnessClause S γ i).Sat A env w := by
      intro i
      apply hall
      simp only [List.mem_append, List.mem_ofFn]
      exact Or.inl ⟨i, rfl⟩
    have hwit' : ∀ i, NearTuple A T env (w i) ∧
        γ.Sat A (fun _ => w i) Fin.elim0 := by
      intro i
      exact (sat_scatterWitnessClause A env w γ i hTS h2TS).mp (hwit i)
    have hpairs : ∀ i j,
        (scatterPairClause i0 S T i j).Sat A env w := by
      intro i j
      have hi := hall
        (LocalTuples.conjunctions (RadiusChange.truth i0)
          (List.ofFn fun j : Fin n => scatterPairClause i0 S T i j))
        (by
          simp only [List.mem_append, List.mem_ofFn]
          exact Or.inr ⟨i, rfl⟩)
      exact (LocalTuples.sat_conjunctions A env w
        (RadiusChange.truth i0) (RadiusChange.sat_truth A env w i0)
        (List.ofFn fun j : Fin n => scatterPairClause i0 S T i j)).mp hi
        (scatterPairClause i0 S T i j) (by simp)
    refine ⟨⟨(fun i => (hwit' i).2), ?_⟩, fun i => (hwit' i).1⟩
    intro i j hij
    exact (sat_scatterPairClause A env w i0 i j (hwit' i).1 h3TS).mp
      (hpairs i j) hij
  · rintro ⟨hscatter, hnear⟩
    intro φ hφ
    simp only [List.mem_append, List.mem_ofFn] at hφ
    rcases hφ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · apply (sat_scatterWitnessClause A env w γ i hTS h2TS).mpr
      exact ⟨hnear i, hscatter.1 i⟩
    · apply (LocalTuples.sat_conjunctions A env w
        (RadiusChange.truth i0) (RadiusChange.sat_truth A env w i0)
        (List.ofFn fun j : Fin n => scatterPairClause i0 S T i j)).mpr
      intro clause hclause
      simp only [List.mem_ofFn] at hclause
      obtain ⟨j, rfl⟩ := hclause
      apply (sat_scatterPairClause A env w i0 i j (hnear i) h3TS).mpr
      exact hscatter.2 i j

theorem sat_nearScatterFormula {σ : Vocabulary} {M : Type*}
    {k n S T : ℕ} (A : Structure σ M) (env : Fin k → M)
    (i0 : Fin k) (γ : LocalFormula σ 1 T 0)
    (hTS : T ≤ S) (h2TS : 2 * T ≤ S) (h3TS : 3 * T ≤ S) :
    (nearScatterFormula (n := n) i0 S γ).Sat A env Fin.elim0 ↔
      HasNearScatter A T env
        (fun y => γ.Sat A (fun _ => y) Fin.elim0) n := by
  rw [nearScatterFormula, LocalTuples.sat_closeExists A env]
  constructor
  · rintro ⟨w, -, hbody⟩
    exact ⟨w, (sat_nearScatterBody A env w i0 γ hTS h2TS h3TS).mp hbody⟩
  · rintro ⟨w, hscatter, hnear⟩
    refine ⟨w, ?_, (sat_nearScatterBody A env w i0 γ
      hTS h2TS h3TS).mpr ⟨hscatter, hnear⟩⟩
    intro i
    exact inBallAround_mono A hTS env (Or.inl (hnear i))

/-- The local annulus alternative in the finite scatter argument. -/
def annulusFormula {σ : Vocabulary} {k R : ℕ} (S T : ℕ)
    (β : LocalFormula σ 1 R 0) : LocalFormula σ k S 0 :=
  .ex (LocalFormula.conjunction
    (nearAnchors S (3 * T) (.bound 0))
    (LocalFormula.conjunction
      (.not (nearAnchors S T (.bound 0)))
      (LocalFormula.conjunction
        (recenter S (fun _ : Fin 1 => .bound 0) Fin.elim0 β)
        (.not (nearConstants S T (.bound 0))))))

theorem sat_annulusFormula {σ : Vocabulary} {M : Type*}
    {k R S T : ℕ} (A : Structure σ M) (env : Fin k → M)
    (β : LocalFormula σ 1 R 0)
    (hRT : R ≤ T) (hTS : T ≤ S) (h3TS : 3 * T ≤ S)
    (h3TRS : 3 * T + R ≤ S) :
    (annulusFormula S T β).Sat A env Fin.elim0 ↔
      HasAnnulusWitness A T env
        (fun y => (farProperty T β).Sat A (fun _ => y) Fin.elim0) := by
  simp only [annulusFormula, LocalFormula.Sat,
    LocalFormula.sat_conjunction]
  constructor
  · rintro ⟨y, -, hnear3, hnnear, hβ, hnconst⟩
    have hnear3' : NearTuple A (3 * T) env y := by
      have h := (sat_nearAnchors A env (fun _ => y) (.bound 0) h3TS).mp hnear3
      simpa [LocalTerm.eval] using h
    have hnnear' : ¬ NearTuple A T env y := by
      intro h
      apply hnnear
      apply (sat_nearAnchors A env (fun _ => y) (.bound 0) hTS).mpr
      simpa [LocalTerm.eval] using h
    have hanchors : ∀ _ : Fin 1, inBallAround A (3 * T) env
        ((.bound 0 : LocalTerm σ k 1).eval A env (fun _ => y)) :=
      fun _ => Or.inl hnear3'
    have hβ' := (sat_recenter A env (fun _ => y)
      (fun _ : Fin 1 => (.bound 0 : LocalTerm σ k 1)) Fin.elim0 β
      hanchors h3TRS).mp hβ
    have hempty :
        (fun z => (Fin.elim0 z : LocalTerm σ k 1).eval A env (fun _ => y)) =
          (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    rw [hempty] at hβ'
    have hnconst' : ¬ ∃ c : σ.Constant,
        distanceAtMost A T (A.constant c) y := by
      intro h
      apply hnconst
      apply (sat_nearConstants A env (fun _ => y) (.bound 0) hTS).mpr
      simpa [LocalTerm.eval] using h
    exact ⟨y, hnear3', hnnear',
      (sat_farProperty A y β hRT).mpr ⟨by simpa [LocalTerm.eval] using hβ', hnconst'⟩⟩
  · rintro ⟨y, hnear3, hnnear, hγ⟩
    obtain ⟨hβ, hnconst⟩ := (sat_farProperty A y β hRT).mp hγ
    have hyS : inBallAround A S env y :=
      inBallAround_mono A h3TS env (Or.inl hnear3)
    refine ⟨y, hyS, ?_, ?_, ?_, ?_⟩
    · apply (sat_nearAnchors A env (fun _ => y) (.bound 0) h3TS).mpr
      simpa [LocalTerm.eval] using hnear3
    · intro h
      apply hnnear
      have h' := (sat_nearAnchors A env (fun _ => y) (.bound 0) hTS).mp h
      simpa [LocalTerm.eval] using h'
    · have hanchors : ∀ _ : Fin 1, inBallAround A (3 * T) env
          ((.bound 0 : LocalTerm σ k 1).eval A env (fun _ => y)) :=
        fun _ => Or.inl hnear3
      apply (sat_recenter A env (fun _ => y)
        (fun _ : Fin 1 => (.bound 0 : LocalTerm σ k 1)) Fin.elim0 β
        hanchors h3TRS).mpr
      have hempty :
          (fun z => (Fin.elim0 z : LocalTerm σ k 1).eval A env (fun _ => y)) =
            (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      rw [hempty]
      simpa [LocalTerm.eval] using hβ
    · intro h
      apply hnconst
      have h' := (sat_nearConstants A env (fun _ => y) (.bound 0) hTS).mp h
      simpa [LocalTerm.eval] using h'

/-- The basic local sentence asserting an `n`-point scatter of `γ`. -/
def scatterSentence {σ : Vocabulary} {T : ℕ}
    (γ : LocalFormula σ 1 T 0) (n : ℕ) : BasicLocalSentence σ T where
  witnessCount := n
  property := γ

/-- The same scatter assertion, viewed as a normal form in any free-variable
context. -/
def scatterNormalForm {σ : Vocabulary} {k T : ℕ}
    (γ : LocalFormula σ 1 T 0) (n : ℕ) : NormalForm σ k :=
  NormalForm.ofBasic (scatterSentence γ n)

theorem sat_scatterNormalForm {σ : Vocabulary} {M : Type*}
    {k T : ℕ} (A : Structure σ M) (env : Fin k → M)
    (γ : LocalFormula σ 1 T 0) (n : ℕ) :
    (scatterNormalForm (k := k) γ n).Sat A env ↔
      HasScatter A T (fun y => γ.Sat A (fun _ => y) Fin.elim0) n := by
  rfl

/-- False normal form, used as the empty finite disjunction. -/
def falseNormalForm (σ : Vocabulary) (k : ℕ) : NormalForm σ k :=
  NormalForm.neg (NormalForm.truth σ k)

/-- Finite disjunction of normal forms. -/
def disjunctionsNF {σ : Vocabulary} {k : ℕ} :
    List (NormalForm σ k) → NormalForm σ k
  | [] => falseNormalForm σ k
  | nf :: nfs => NormalForm.disj nf (disjunctionsNF nfs)

theorem sat_disjunctionsNF {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (nfs : List (NormalForm σ k)) :
    (disjunctionsNF nfs).Sat A env ↔ ∃ nf ∈ nfs, nf.Sat A env := by
  induction nfs with
  | nil => simp [disjunctionsNF, falseNormalForm]
  | cons nf nfs ih => simp [disjunctionsNF, ih]

theorem radiiBounded_disjunctionsNF {σ : Vocabulary} {k bound : ℕ}
    {nfs : List (NormalForm σ k)}
    (h : ∀ nf ∈ nfs, nf.RadiiBounded bound) :
    (disjunctionsNF nfs).RadiiBounded bound := by
  induction nfs with
  | nil =>
      exact NormalForm.radiiBounded_neg NormalForm.radiiBounded_truth
  | cons nf nfs ih =>
      apply NormalForm.radiiBounded_disj
      · exact h nf (by simp)
      · exact ih (fun nf hnf => h nf (by simp [hnf]))

theorem witnessesBounded_disjunctionsNF {σ : Vocabulary} {k bound : ℕ}
    {nfs : List (NormalForm σ k)}
    (h : ∀ nf ∈ nfs, nf.WitnessesBounded bound) :
    (disjunctionsNF nfs).WitnessesBounded bound := by
  induction nfs with
  | nil =>
      exact NormalForm.witnessesBounded_neg NormalForm.witnessesBounded_truth
  | cons nf nfs ih =>
      apply NormalForm.witnessesBounded_disj
      · exact h nf (by simp)
      · exact ih (fun nf hnf => h nf (by simp [hnf]))

/-- One bounded-scatter alternative in the semantic scatter lemma. -/
def farCaseNormalForm {σ : Vocabulary} {k R : ℕ} (i0 : Fin k)
    (T S : ℕ) (β : LocalFormula σ 1 R 0) (l : ℕ) : NormalForm σ k :=
  let γ := farProperty T β
  NormalForm.conj (scatterNormalForm γ l)
    (NormalForm.conj
      (NormalForm.neg (scatterNormalForm γ (l + 1)))
      (NormalForm.disj
        (NormalForm.neg
          (NormalForm.ofLocal (nearScatterFormula (n := l) i0 S γ)))
        (NormalForm.ofLocal (annulusFormula S T β))))

/-- The complete normal form for existence of a far witness satisfying `β`.
The first disjunct is a scatter of size `k+1`. The remaining finite disjunction
implements the bounded-scatter alternatives. -/
def farWitnessNormalForm {σ : Vocabulary} {k R : ℕ} (i0 : Fin k)
    (T S : ℕ) (β : LocalFormula σ 1 R 0) : NormalForm σ k :=
  let γ := farProperty T β
  NormalForm.disj (scatterNormalForm γ (k + 1))
    (disjunctionsNF (List.ofFn fun i : Fin k =>
      farCaseNormalForm i0 T S β (i.val + 1)))

theorem sat_farCaseNormalForm {σ : Vocabulary} {M : Type*}
    {k R S T : ℕ} (A : Structure σ M) (env : Fin k → M)
    (i0 : Fin k) (β : LocalFormula σ 1 R 0) (l : ℕ)
    (hRT : R ≤ T) (hTS : T ≤ S) (h2TS : 2 * T ≤ S)
    (h3TS : 3 * T ≤ S) (h3TRS : 3 * T + R ≤ S) :
    (farCaseNormalForm i0 T S β l).Sat A env ↔
      HasScatter A T
          (fun y => (farProperty T β).Sat A (fun _ => y) Fin.elim0) l ∧
        ¬ HasScatter A T
          (fun y => (farProperty T β).Sat A (fun _ => y) Fin.elim0) (l + 1) ∧
        (¬ HasNearScatter A T env
            (fun y => (farProperty T β).Sat A (fun _ => y) Fin.elim0) l ∨
          HasAnnulusWitness A T env
            (fun y => (farProperty T β).Sat A (fun _ => y) Fin.elim0)) := by
  simp only [farCaseNormalForm, NormalForm.sat_conj, NormalForm.sat_neg,
    NormalForm.sat_disj, NormalForm.sat_ofLocal]
  rw [sat_scatterNormalForm, sat_scatterNormalForm,
    sat_nearScatterFormula A env i0 (farProperty T β) hTS h2TS h3TS,
    sat_annulusFormula A env β hRT hTS h3TS h3TRS]

theorem radiiBounded_farCaseNormalForm {σ : Vocabulary}
    {k R T S : ℕ} (i0 : Fin k) (β : LocalFormula σ 1 R 0) (l : ℕ)
    (hTS : T ≤ S) :
    (farCaseNormalForm i0 T S β l).RadiiBounded S := by
  apply NormalForm.radiiBounded_conj
  · exact NormalForm.radiiBounded_ofBasic _ hTS
  · apply NormalForm.radiiBounded_conj
    · exact NormalForm.radiiBounded_neg
        (NormalForm.radiiBounded_ofBasic _ hTS)
    · apply NormalForm.radiiBounded_disj
      · exact NormalForm.radiiBounded_neg
          (NormalForm.radiiBounded_ofLocal _ (le_refl S))
      · exact NormalForm.radiiBounded_ofLocal _ (le_refl S)

theorem witnessesBounded_farCaseNormalForm {σ : Vocabulary}
    {k R T S bound : ℕ} (i0 : Fin k) (β : LocalFormula σ 1 R 0)
    (l : ℕ) (hl : l ≤ bound) (hnext : l + 1 ≤ bound) :
    (farCaseNormalForm i0 T S β l).WitnessesBounded bound := by
  apply NormalForm.witnessesBounded_conj
  · exact NormalForm.witnessesBounded_ofBasic _ hl
  · apply NormalForm.witnessesBounded_conj
    · exact NormalForm.witnessesBounded_neg
        (NormalForm.witnessesBounded_ofBasic _ hnext)
    · apply NormalForm.witnessesBounded_disj
      · exact NormalForm.witnessesBounded_neg
          (NormalForm.witnessesBounded_ofLocal _)
      · exact NormalForm.witnessesBounded_ofLocal _

theorem sat_farWitnessNormalForm {σ : Vocabulary} {M : Type*}
    {k R S T : ℕ} (A : Structure σ M) (env : Fin k → M)
    (i0 : Fin k) (β : LocalFormula σ 1 R 0)
    (hRT : R ≤ T) (hTS : T ≤ S) (h2TS : 2 * T ≤ S)
    (h3TS : 3 * T ≤ S) (h3TRS : 3 * T + R ≤ S) :
    (farWitnessNormalForm i0 T S β).Sat A env ↔
      HasFarWitness A T env
        (fun y => (farProperty T β).Sat A (fun _ => y) Fin.elim0) := by
  rw [farWitnessNormalForm, NormalForm.sat_disj,
    sat_scatterNormalForm, sat_disjunctionsNF,
    hasFarWitness_iff]
  apply or_congr_right
  constructor
  · rintro ⟨nf, hnf, hsat⟩
    simp only [List.mem_ofFn] at hnf
    obtain ⟨i, rfl⟩ := hnf
    refine ⟨i.val + 1, by omega, by omega, ?_⟩
    exact (sat_farCaseNormalForm A env i0 β (i.val + 1)
      hRT hTS h2TS h3TS h3TRS).mp hsat
  · rintro ⟨l, h1l, hlk, hcase⟩
    have hlt : l - 1 < k := by omega
    let i : Fin k := ⟨l - 1, hlt⟩
    refine ⟨farCaseNormalForm i0 T S β (i.val + 1), ?_, ?_⟩
    · simp only [List.mem_ofFn]
      exact ⟨i, rfl⟩
    · have hil : i.val + 1 = l := by simp [i]; omega
      rw [hil]
      exact (sat_farCaseNormalForm A env i0 β l
        hRT hTS h2TS h3TS h3TRS).mpr hcase

theorem radiiBounded_farWitnessNormalForm {σ : Vocabulary}
    {k R T S : ℕ} (i0 : Fin k) (β : LocalFormula σ 1 R 0)
    (hTS : T ≤ S) :
    (farWitnessNormalForm i0 T S β).RadiiBounded S := by
  apply NormalForm.radiiBounded_disj
  · exact NormalForm.radiiBounded_ofBasic _ hTS
  · apply radiiBounded_disjunctionsNF
    intro nf hnf
    simp only [List.mem_ofFn] at hnf
    obtain ⟨i, rfl⟩ := hnf
    exact radiiBounded_farCaseNormalForm i0 β (i.val + 1) hTS

theorem witnessesBounded_farWitnessNormalForm {σ : Vocabulary}
    {k R T S : ℕ} (i0 : Fin k) (β : LocalFormula σ 1 R 0) :
    (farWitnessNormalForm i0 T S β).WitnessesBounded (k + 1) := by
  apply NormalForm.witnessesBounded_disj
  · exact NormalForm.witnessesBounded_ofBasic _ (le_refl (k + 1))
  · apply witnessesBounded_disjunctionsNF
    intro nf hnf
    simp only [List.mem_ofFn] at hnf
    obtain ⟨i, rfl⟩ := hnf
    apply witnessesBounded_farCaseNormalForm i0 β (i.val + 1)
    · omega
    · omega

/-- Normal form contributed by one separated left/right pair. -/
def separatedPairNormalForm {σ : Vocabulary} {k R : ℕ} (i0 : Fin k)
    (T S : ℕ)
    (p : LocalFormula σ k R 0 × LocalFormula σ 1 R 0) :
    NormalForm σ k :=
  NormalForm.conj (NormalForm.ofLocal (enlarge S p.1))
    (farWitnessNormalForm i0 T S p.2)

theorem sat_separatedPairNormalForm {σ : Vocabulary} {M : Type*}
    {k R T S : ℕ} (A : Structure σ M) (env : Fin k → M)
    (i0 : Fin k)
    (p : LocalFormula σ k R 0 × LocalFormula σ 1 R 0)
    (hRS : R ≤ S) (hRT : R ≤ T) (hTS : T ≤ S)
    (h2TS : 2 * T ≤ S) (h3TS : 3 * T ≤ S)
    (h3TRS : 3 * T + R ≤ S) :
    (separatedPairNormalForm i0 T S p).Sat A env ↔
      p.1.Sat A env Fin.elim0 ∧
        HasFarWitness A T env
          (fun y => (farProperty T p.2).Sat A (fun _ => y) Fin.elim0) := by
  rw [separatedPairNormalForm, NormalForm.sat_conj,
    NormalForm.sat_ofLocal, sat_enlarge A env Fin.elim0 p.1 hRS,
    sat_farWitnessNormalForm A env i0 p.2 hRT hTS h2TS h3TS h3TRS]

theorem radiiBounded_separatedPairNormalForm {σ : Vocabulary}
    {k R T S : ℕ} (i0 : Fin k)
    (p : LocalFormula σ k R 0 × LocalFormula σ 1 R 0)
    (hTS : T ≤ S) :
    (separatedPairNormalForm i0 T S p).RadiiBounded S := by
  apply NormalForm.radiiBounded_conj
  · exact NormalForm.radiiBounded_ofLocal _ (le_refl S)
  · exact radiiBounded_farWitnessNormalForm i0 p.2 hTS

theorem witnessesBounded_separatedPairNormalForm {σ : Vocabulary}
    {k R T S : ℕ} (i0 : Fin k)
    (p : LocalFormula σ k R 0 × LocalFormula σ 1 R 0) :
    (separatedPairNormalForm i0 T S p).WitnessesBounded (k + 1) := by
  apply NormalForm.witnessesBounded_conj
  · exact NormalForm.witnessesBounded_ofLocal _
  · exact witnessesBounded_farWitnessNormalForm i0 p.2

/-- Eliminate the existential quantifier from one local formula around
`k+1` anchors, when `k` is nonempty. -/
def eliminateLocal {σ : Vocabulary} {k R : ℕ} (i0 : Fin k)
    (T S : ℕ) (ψ : LocalFormula σ (k + 1) R 0) : NormalForm σ k :=
  NormalForm.disj (NormalForm.ofLocal (nearPart S T ψ))
    (disjunctionsNF ((separateClosed i0 ψ).map fun p =>
      separatedPairNormalForm i0 T S p))

theorem sat_eliminateLocal {σ : Vocabulary} {M : Type*}
    {k R T S : ℕ} (A : Structure σ M) (env : Fin k → M)
    (i0 : Fin k) (ψ : LocalFormula σ (k + 1) R 0)
    (hT : T = 2 * R + 1)
    (hRS : R ≤ S) (hRT : R ≤ T) (hTS : T ≤ S)
    (hTRS : T + R ≤ S) (h2TS : 2 * T ≤ S)
    (h3TS : 3 * T ≤ S) (h3TRS : 3 * T + R ≤ S) :
    (eliminateLocal i0 T S ψ).Sat A env ↔
      ∃ y, ψ.Sat A (Fin.snoc env y) Fin.elim0 := by
  rw [eliminateLocal, NormalForm.sat_disj, NormalForm.sat_ofLocal,
    sat_nearPart A env ψ hTS hTRS, sat_disjunctionsNF]
  constructor
  · rintro (⟨y, hy, hψ⟩ | ⟨nf, hnf, hnfSat⟩)
    · exact ⟨y, hψ⟩
    · simp only [List.mem_map] at hnf
      obtain ⟨p, hp, rfl⟩ := hnf
      obtain ⟨hleft, y, hyNear, hγ⟩ :=
        (sat_separatedPairNormalForm A env i0 p hRS hRT hTS
          h2TS h3TS h3TRS).mp hnfSat
      obtain ⟨hright, hnconst⟩ := (sat_farProperty A y p.2 hRT).mp hγ
      have hyBall : ¬ inBallAround A T env y := by
        rintro (⟨i, hi⟩ | ⟨c, hc⟩)
        · exact hyNear ⟨i, hi⟩
        · exact hnconst ⟨c, hc⟩
      refine ⟨y, ?_⟩
      apply (sat_separateClosed A env y i0 ψ (hT ▸ hyBall)).mpr
      exact ⟨p, hp, hleft, hright⟩
  · rintro ⟨y, hψ⟩
    by_cases hy : inBallAround A T env y
    · exact Or.inl ⟨y, hy, hψ⟩
    · right
      have hsep := (sat_separateClosed A env y i0 ψ (hT ▸ hy)).mp hψ
      obtain ⟨p, hp, hleft, hright⟩ := hsep
      refine ⟨separatedPairNormalForm i0 T S p, ?_, ?_⟩
      · simp only [List.mem_map]
        exact ⟨p, hp, rfl⟩
      · apply (sat_separatedPairNormalForm A env i0 p hRS hRT hTS
          h2TS h3TS h3TRS).mpr
        refine ⟨hleft, y, ?_, ?_⟩
        · intro hnear
          apply hy
          rcases hnear with ⟨i, hi⟩
          exact Or.inl ⟨i, hi⟩
        · apply (sat_farProperty A y p.2 hRT).mpr
          refine ⟨hright, ?_⟩
          rintro ⟨c, hc⟩
          exact hy (Or.inr ⟨c, hc⟩)

theorem radiiBounded_eliminateLocal {σ : Vocabulary}
    {k R T S : ℕ} (i0 : Fin k)
    (ψ : LocalFormula σ (k + 1) R 0) (hTS : T ≤ S) :
    (eliminateLocal i0 T S ψ).RadiiBounded S := by
  apply NormalForm.radiiBounded_disj
  · exact NormalForm.radiiBounded_ofLocal _ (le_refl S)
  · apply radiiBounded_disjunctionsNF
    intro nf hnf
    simp only [List.mem_map] at hnf
    obtain ⟨p, -, rfl⟩ := hnf
    exact radiiBounded_separatedPairNormalForm i0 p hTS

theorem witnessesBounded_eliminateLocal {σ : Vocabulary}
    {k R T S : ℕ} (i0 : Fin k)
    (ψ : LocalFormula σ (k + 1) R 0) :
    (eliminateLocal i0 T S ψ).WitnessesBounded (k + 1) := by
  apply NormalForm.witnessesBounded_disj
  · exact NormalForm.witnessesBounded_ofLocal _
  · apply witnessesBounded_disjunctionsNF
    intro nf hnf
    simp only [List.mem_map] at hnf
    obtain ⟨p, -, rfl⟩ := hnf
    exact witnessesBounded_separatedPairNormalForm i0 p

end

end Lax185574Proofs.Gaifman.LocalElimination
