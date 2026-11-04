import Lax185574Proofs.Gaifman.LocalElimination

/-!
Elimination of one existential quantifier from an arbitrary Gaifman normal
form.  Basic local sentences are independent of the quantified variable, so a
finite truth-pattern split pulls them outside.  Each remaining Boolean
combination of local atoms is converted to one common-radius local formula and
handled by `LocalElimination`.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/ExistentialNormalForm.lean`.
-/

namespace Lax185574Proofs.Gaifman.ExistentialNormalForm

noncomputable section

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.GaifmanNormalForm
open Lax185574Proofs.Gaifman.NormalFormOps Lax185574Proofs.Gaifman.RadiusChange
open Lax185574Proofs.Gaifman.LocalElimination
open Lax185574Proofs.Gaifman.BooleanCombination
open Lax185574Proofs.Gaifman.Scatter

/-- A local normal-form atom with its radius exposed as data. -/
structure LocalPiece (σ : Vocabulary) (k : ℕ) where
  radius : ℕ
  formula : LocalFormula σ k radius 0

/-- A basic local sentence with its radius exposed as data. -/
structure BasicPiece (σ : Vocabulary) where
  radius : ℕ
  sentence : BasicLocalSentence σ radius

/-- Split a normal atom into its local and sentence alternatives. -/
def splitAtom {σ : Vocabulary} {k : ℕ} :
    NormalAtom σ k → LocalPiece σ k ⊕ BasicPiece σ
  | .local r φ => .inl ⟨r, φ⟩
  | .basic r β => .inr ⟨r, β⟩

/-- Reinsert a basic sentence into a possibly different free-variable
context. -/
def basicAtom {σ : Vocabulary} {k : ℕ} (b : BasicPiece σ) :
    NormalAtom σ k := .basic b.radius b.sentence

/-- Boolean body with local atoms and basic sentences explicitly separated. -/
def splitBody {σ : Vocabulary} {k : ℕ} (nf : NormalForm σ k) :
    BooleanCombination (LocalPiece σ k ⊕ BasicPiece σ) :=
  BooleanCombination.map splitAtom nf.body

theorem eval_splitBody {σ : Vocabulary} {M : Type*} {k : ℕ}
    (A : Structure σ M) (env : Fin k → M) (nf : NormalForm σ k) :
    (splitBody nf).eval (Sum.elim
      (fun p => p.formula.Sat A env Fin.elim0)
      (fun b => b.sentence.Sat A)) ↔ nf.Sat A env := by
  rw [splitBody, BooleanCombination.eval_map]
  apply BooleanCombination.eval_congr nf.body
  intro atom _
  cases atom <;> rfl

/-- Turn a Boolean combination of local atoms into one local formula at a
common radius. -/
def combineLocal {σ : Vocabulary} {k : ℕ} (R : ℕ)
    (b : BooleanCombination (LocalPiece σ (k + 1))) :
    LocalFormula σ (k + 1) R 0 :=
  BooleanCombination.interp (RadiusChange.truth (Fin.last k))
    LocalFormula.not LocalFormula.conjunction
    (BooleanCombination.map (fun p => enlarge R p.formula) b)

theorem sat_combineLocal {σ : Vocabulary} {M : Type*} {k R : ℕ}
    (A : Structure σ M) (env : Fin (k + 1) → M)
    (b : BooleanCombination (LocalPiece σ (k + 1)))
    (hr : ∀ p, p ∈ b.atoms → p.radius ≤ R) :
    (combineLocal R b).Sat A env Fin.elim0 ↔
      b.eval (fun p => p.formula.Sat A env Fin.elim0) := by
  rw [combineLocal]
  rw [BooleanCombination.eval_interp
    (value := fun φ : LocalFormula σ (k + 1) R 0 =>
      φ.Sat A env Fin.elim0)
    (truth := RadiusChange.truth (Fin.last k))
    (neg := LocalFormula.not) (conj := LocalFormula.conjunction)
    (RadiusChange.sat_truth A env Fin.elim0 (Fin.last k))
    (fun _ => Iff.rfl)
    (fun φ ψ => LocalFormula.sat_conjunction A env Fin.elim0 φ ψ)]
  rw [BooleanCombination.eval_map]
  apply BooleanCombination.eval_congr b
  intro p hp
  exact sat_enlarge A env Fin.elim0 p.formula (hr p hp)

/-- At zero remaining free variables, an existential local formula is already
a one-witness basic local sentence. -/
def eliminateClosedLocal {σ : Vocabulary} {R : ℕ}
    (ψ : LocalFormula σ 1 R 0) : NormalForm σ 0 :=
  scatterNormalForm ψ 1

theorem sat_eliminateClosedLocal {σ : Vocabulary} {M : Type*} {R : ℕ}
    (A : Structure σ M) (ψ : LocalFormula σ 1 R 0) :
    (eliminateClosedLocal ψ).Sat A Fin.elim0 ↔
      ∃ y, ψ.Sat A (fun _ => y) Fin.elim0 := by
  rw [eliminateClosedLocal, sat_scatterNormalForm]
  constructor
  · rintro ⟨w, hw, -⟩
    exact ⟨w 0, hw 0⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun _ => y, (fun _ => hy), ?_⟩
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

theorem radiiBounded_eliminateClosedLocal {σ : Vocabulary} {R S : ℕ}
    (ψ : LocalFormula σ 1 R 0) (hRS : R ≤ S) :
    (eliminateClosedLocal ψ).RadiiBounded S :=
  NormalForm.radiiBounded_ofBasic _ hRS

theorem witnessesBounded_eliminateClosedLocal {σ : Vocabulary} {R : ℕ}
    (ψ : LocalFormula σ 1 R 0) :
    (eliminateClosedLocal ψ).WitnessesBounded 1 :=
  NormalForm.witnessesBounded_ofBasic _ (le_refl 1)

/-- Dispatch local existential elimination according to whether any free
anchors remain. -/
def eliminateCombinedLocal {σ : Vocabulary} {R : ℕ} (T S : ℕ) :
    (k : ℕ) → LocalFormula σ (k + 1) R 0 → NormalForm σ k
  | 0, ψ => eliminateClosedLocal ψ
  | k + 1, ψ => eliminateLocal (Fin.last k) T S ψ

theorem sat_eliminateCombinedLocal {σ : Vocabulary} {M : Type*}
    {R T S : ℕ} (A : Structure σ M)
    (hT : T = 2 * R + 1)
    (hRS : R ≤ S) (hRT : R ≤ T) (hTS : T ≤ S)
    (hTRS : T + R ≤ S) (h2TS : 2 * T ≤ S)
    (h3TS : 3 * T ≤ S) (h3TRS : 3 * T + R ≤ S) :
    ∀ (k : ℕ) (env : Fin k → M) (ψ : LocalFormula σ (k + 1) R 0),
      (eliminateCombinedLocal T S k ψ).Sat A env ↔
        ∃ y, ψ.Sat A (Fin.snoc env y) Fin.elim0 := by
  intro k
  cases k with
  | zero =>
      intro env ψ
      have henv : env = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      subst env
      rw [eliminateCombinedLocal, sat_eliminateClosedLocal A ψ]
      apply exists_congr
      intro y
      have hsnoc : Fin.snoc (Fin.elim0 : Fin 0 → M) y = (fun _ => y) :=
        Fin.snoc_zero _ _
      rw [hsnoc]
  | succ k =>
      intro env ψ
      exact sat_eliminateLocal A env (Fin.last k) ψ hT hRS hRT hTS
        hTRS h2TS h3TS h3TRS

theorem radiiBounded_eliminateCombinedLocal {σ : Vocabulary}
    {R T S : ℕ} (hRS : R ≤ S) (hTS : T ≤ S) :
    ∀ (k : ℕ) (ψ : LocalFormula σ (k + 1) R 0),
      (eliminateCombinedLocal T S k ψ).RadiiBounded S := by
  intro k
  cases k with
  | zero => exact fun ψ => radiiBounded_eliminateClosedLocal ψ hRS
  | succ k => exact fun ψ => radiiBounded_eliminateLocal (Fin.last k) ψ hTS

theorem witnessesBounded_eliminateCombinedLocal {σ : Vocabulary}
    {R T S : ℕ} :
    ∀ (k : ℕ) (ψ : LocalFormula σ (k + 1) R 0),
      (eliminateCombinedLocal T S k ψ).WitnessesBounded (k + 1) := by
  intro k
  cases k with
  | zero => exact fun ψ => witnessesBounded_eliminateClosedLocal ψ
  | succ k => exact fun ψ => witnessesBounded_eliminateLocal (Fin.last k) ψ

theorem localPiece_of_mem_splitBody {σ : Vocabulary} {k : ℕ}
    {nf : NormalForm σ k} {p : LocalPiece σ k}
    (hp : Sum.inl p ∈ (splitBody nf).atoms) :
    NormalAtom.local p.radius p.formula ∈ nf.body.atoms := by
  simp only [splitBody, BooleanCombination.atoms_map, List.mem_map] at hp
  obtain ⟨atom, hatom, hsplit⟩ := hp
  rcases atom with ⟨r, φ⟩ | ⟨r, β⟩
  · simp only [splitAtom, Sum.inl.injEq] at hsplit
    cases hsplit
    exact hatom
  · simp [splitAtom] at hsplit

theorem basicPiece_of_mem_splitBody {σ : Vocabulary} {k : ℕ}
    {nf : NormalForm σ k} {b : BasicPiece σ}
    (hb : Sum.inr b ∈ (splitBody nf).atoms) :
    NormalAtom.basic b.radius b.sentence ∈ nf.body.atoms := by
  simp only [splitBody, BooleanCombination.atoms_map, List.mem_map] at hb
  obtain ⟨atom, hatom, hsplit⟩ := hb
  rcases atom with ⟨r, φ⟩ | ⟨r, β⟩
  · simp [splitAtom] at hsplit
  · simp only [splitAtom, Sum.inr.injEq] at hsplit
    cases hsplit
    exact hatom

/-- Replacement normal form for one truth assignment to the basic sentences
occurring in the body. -/
def assignmentReplacement {σ : Vocabulary} {k : ℕ} (R T S : ℕ)
    (nf : NormalForm σ (k + 1)) (τ : BasicPiece σ → Bool) :
    NormalForm σ k :=
  eliminateCombinedLocal T S k
    (combineLocal R (BooleanCombination.collapse τ (splitBody nf)))

/-- Eliminate one first-order existential from an arbitrary normal form. -/
def eliminateNormalForm {σ : Vocabulary} {k : ℕ} (R T S : ℕ)
    (nf : NormalForm σ (k + 1)) : NormalForm σ k :=
  ⟨BooleanCombination.map (Sum.elim id basicAtom)
    (BooleanCombination.pullOut (splitBody nf)
      (fun τ => (assignmentReplacement R T S nf τ).body))⟩

theorem sat_eliminateNormalForm {σ : Vocabulary} {M : Type*}
    {k R T S : ℕ} (A : Structure σ M) (env : Fin k → M)
    (nf : NormalForm σ (k + 1))
    (hradii : nf.RadiiBounded R)
    (hT : T = 2 * R + 1)
    (hRS : R ≤ S) (hRT : R ≤ T) (hTS : T ≤ S)
    (hTRS : T + R ≤ S) (h2TS : 2 * T ≤ S)
    (h3TS : 3 * T ≤ S) (h3TRS : 3 * T + R ≤ S) :
    (eliminateNormalForm R T S nf).Sat A env ↔
      ∃ y, nf.Sat A (Fin.snoc env y) := by
  let outValue : NormalAtom σ k → Prop := fun atom =>
    match atom with
    | .local _ φ => φ.Sat A env Fin.elim0
    | .basic _ β => β.Sat A
  let localValue : M → LocalPiece σ (k + 1) → Prop := fun y p =>
    p.formula.Sat A (Fin.snoc env y) Fin.elim0
  let basicValue : BasicPiece σ → Prop := fun b => b.sentence.Sat A
  change (BooleanCombination.map (Sum.elim id basicAtom)
    (BooleanCombination.pullOut (splitBody nf)
      (fun τ => (assignmentReplacement R T S nf τ).body))).eval outValue ↔ _
  rw [BooleanCombination.eval_map]
  have hmerge :
      (outValue ∘ Sum.elim id basicAtom) =
        Sum.elim outValue basicValue := by
    funext x
    cases x <;> rfl
  rw [hmerge]
  rw [← BooleanCombination.eval_pullOut (splitBody nf)
    (fun τ => (assignmentReplacement R T S nf τ).body)
    localValue basicValue outValue]
  · apply exists_congr
    intro y
    exact eval_splitBody A (Fin.snoc env y) nf
  · intro τ
    change (assignmentReplacement R T S nf τ).Sat A env ↔ _
    rw [assignmentReplacement,
      sat_eliminateCombinedLocal A hT hRS hRT hTS hTRS h2TS h3TS h3TRS]
    apply exists_congr
    intro y
    apply sat_combineLocal
    intro p hp
    apply hradii (NormalAtom.local p.radius p.formula)
    apply localPiece_of_mem_splitBody
    exact BooleanCombination.mem_atoms_collapse.mp hp

theorem radiiBounded_assignmentReplacement {σ : Vocabulary}
    {k R T S : ℕ} (nf : NormalForm σ (k + 1))
    (τ : BasicPiece σ → Bool) (hRS : R ≤ S) (hTS : T ≤ S) :
    (assignmentReplacement R T S nf τ).RadiiBounded S := by
  exact radiiBounded_eliminateCombinedLocal hRS hTS k
    (combineLocal R (BooleanCombination.collapse τ (splitBody nf)))

theorem witnessesBounded_assignmentReplacement {σ : Vocabulary}
    {k R T S : ℕ} (nf : NormalForm σ (k + 1))
    (τ : BasicPiece σ → Bool) :
    (assignmentReplacement R T S nf τ).WitnessesBounded (k + 1) := by
  exact witnessesBounded_eliminateCombinedLocal k
    (combineLocal R (BooleanCombination.collapse τ (splitBody nf)))

theorem radiiBounded_eliminateNormalForm {σ : Vocabulary}
    {k R T S : ℕ} (nf : NormalForm σ (k + 1))
    (hradii : nf.RadiiBounded R) (hRS : R ≤ S) (hTS : T ≤ S) :
    (eliminateNormalForm R T S nf).RadiiBounded S := by
  intro atom hatom
  simp only [eliminateNormalForm, BooleanCombination.atoms_map,
    List.mem_map] at hatom
  obtain ⟨x, hx, rfl⟩ := hatom
  rcases x with d | b
  · obtain ⟨τ, -, hd⟩ := BooleanCombination.mem_atoms_pullOut_left.mp hx
    exact radiiBounded_assignmentReplacement nf τ hRS hTS d hd
  · have hb := BooleanCombination.mem_atoms_pullOut_right hx
    exact le_trans
      (hradii (NormalAtom.basic b.radius b.sentence)
        (basicPiece_of_mem_splitBody hb)) hRS

theorem witnessesBounded_eliminateNormalForm {σ : Vocabulary}
    {k R T S bound : ℕ} (nf : NormalForm σ (k + 1))
    (hwitnesses : nf.WitnessesBounded bound) (hk : k + 1 ≤ bound) :
    (eliminateNormalForm R T S nf).WitnessesBounded bound := by
  intro r basic hatom
  simp only [eliminateNormalForm, BooleanCombination.atoms_map,
    List.mem_map] at hatom
  obtain ⟨x, hx, hxeq⟩ := hatom
  rcases x with d | b
  · have hd : d = NormalAtom.basic r basic := hxeq
    subst d
    obtain ⟨τ, -, hbasic⟩ := BooleanCombination.mem_atoms_pullOut_left.mp hx
    exact le_trans
      (witnessesBounded_assignmentReplacement nf τ r basic hbasic) hk
  · have hbEq : basicAtom b = NormalAtom.basic r basic := hxeq
    have hb := BooleanCombination.mem_atoms_pullOut_right hx
    cases b with
    | mk br bsentence =>
      simp only [basicAtom, NormalAtom.basic.injEq] at hbEq
      rcases hbEq with ⟨rfl, rfl⟩
      exact hwitnesses br bsentence (basicPiece_of_mem_splitBody hb)

end

end Lax185574Proofs.Gaifman.ExistentialNormalForm
