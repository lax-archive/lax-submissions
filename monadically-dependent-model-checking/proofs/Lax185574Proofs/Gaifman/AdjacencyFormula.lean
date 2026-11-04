import Lax185574Proofs.Gaifman.Relativize
import Lax185574Proofs.Gaifman.Distance

/-!
An explicit first-order definition of the Gaifman edge relation for the finite
vocabulary used by the submission.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/AdjacencyFormula.lean`.
-/

namespace Lax185574Proofs.Gaifman.AdjacencyFormula

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.FirstOrder
open Lax185574Proofs.Gaifman.Locality Lax185574Proofs.Gaifman.FormulaUtils
open Lax185574Proofs.Gaifman.Relativize Lax185574Proofs.Gaifman.Distance

/-- The tuple variable at position `i`, after the two endpoint variables. -/
def tupleVariable {σ : Vocabulary} {m : ℕ} (i : Fin m) : Term σ (2 + m) :=
  .var (Fin.natAdd 2 i)

/-- An endpoint variable embedded before `m` tuple variables. -/
def endpointVariable {σ : Vocabulary} {m : ℕ} (i : Fin 2) : Term σ (2 + m) :=
  .var (Fin.castAdd m i)

/-- A relation tuple witnessing that endpoint `0` occurs at position `i` and
endpoint `1` at position `j`. -/
def relationWitness {σ : Vocabulary} (R : σ.Relation)
    (i j : Fin (σ.arity R)) : Formula σ 2 :=
  Formula.exN (σ.arity R)
    (Formula.conjunction
      (.rel R (fun l => tupleVariable l))
      (Formula.conjunction
        (.eq (tupleVariable i) (endpointVariable 0))
        (.eq (tupleVariable j) (endpointVariable 1))))

/-- All relation/position choices that can witness a Gaifman edge. -/
noncomputable def adjacencyCases (σ : Vocabulary) : List (Formula σ 2) :=
  (Finset.univ : Finset σ.Relation).toList.flatMap fun R =>
    (Finset.univ : Finset (Fin (σ.arity R))).toList.flatMap fun i =>
      (Finset.univ : Finset (Fin (σ.arity R))).toList.flatMap fun j =>
        if i = j then [] else [relationWitness R i j]

/-- The explicit formula defining Gaifman adjacency. -/
noncomputable def adjacencyFormula (σ : Vocabulary) : Formula σ 2 :=
  Formula.conjunction
    (.not (.eq (.var 0) (.var 1)))
    (Formula.disjunctions (Formula.falsity (σ := σ) (0 : Fin 2))
      (adjacencyCases σ))

@[simp] theorem eval_tupleVariable {σ : Vocabulary} {M : Type*} {m : ℕ}
    (A : Structure σ M) (env : Fin 2 → M) (tuple : Fin m → M) (i : Fin m) :
    (tupleVariable (σ := σ) i).eval A (Formula.appendEnv env tuple) = tuple i := by
  simp only [tupleVariable, Term.eval, Formula.appendEnv]
  exact Fin.append_right env tuple i

@[simp] theorem eval_endpointVariable {σ : Vocabulary} {M : Type*} {m : ℕ}
    (A : Structure σ M) (env : Fin 2 → M) (tuple : Fin m → M) (i : Fin 2) :
    (endpointVariable (σ := σ) (m := m) i).eval A
      (Formula.appendEnv env tuple) = env i := by
  simp only [endpointVariable, Term.eval, Formula.appendEnv]
  exact Fin.append_left env tuple i

theorem sat_relationWitness {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (env : Fin 2 → M) (R : σ.Relation)
    (i j : Fin (σ.arity R)) :
    Formula.Sat A (relationWitness R i j) env ↔
      ∃ tuple : Fin (σ.arity R) → M,
        A.relation R tuple ∧ tuple i = env 0 ∧ tuple j = env 1 := by
  rw [relationWitness, Formula.sat_exN]
  apply exists_congr
  intro tuple
  simp only [Formula.sat_conjunction, Formula.Sat, eval_tupleVariable,
    eval_endpointVariable]

theorem satRestricted_relationWitness {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (D : M → Prop) (env : Fin 2 → M)
    (R : σ.Relation) (i j : Fin (σ.arity R)) :
    SatRestricted A D (relationWitness R i j) env ↔
      ∃ tuple : Fin (σ.arity R) → M,
        (∀ l, D (tuple l)) ∧ A.relation R tuple ∧
          tuple i = env 0 ∧ tuple j = env 1 := by
  rw [relationWitness, satRestricted_exN]
  apply exists_congr
  intro tuple
  simp only [satRestricted_conjunction, SatRestricted, eval_tupleVariable,
    eval_endpointVariable]

theorem mem_adjacencyCases_iff {σ : Vocabulary} (φ : Formula σ 2) :
    φ ∈ adjacencyCases σ ↔
      ∃ (R : σ.Relation) (i j : Fin (σ.arity R)),
        i ≠ j ∧ φ = relationWitness R i j := by
  simp [adjacencyCases]

/-- Correctness of the explicit adjacency formula. -/
theorem sat_adjacencyFormula {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (env : Fin 2 → M) :
    Formula.Sat A (adjacencyFormula σ) env ↔
      gaifmanAdjacent A (env 0) (env 1) := by
  rw [adjacencyFormula, Formula.sat_conjunction]
  simp only [Formula.Sat, not_false_eq_true]
  apply and_congr_right
  intro hne
  change env 0 ≠ env 1 at hne
  rw [Formula.sat_disjunctions]
  · constructor
    · rintro ⟨φ, hφ, hsφ⟩
      rw [mem_adjacencyCases_iff] at hφ
      rcases hφ with ⟨R, i, j, hij, rfl⟩
      rw [sat_relationWitness] at hsφ
      rcases hsφ with ⟨tuple, hR, hi, hj⟩
      exact ⟨R, tuple, hR, i, j, hij, hi, hj⟩
    · rintro ⟨R, tuple, hR, i, j, hij, hi, hj⟩
      refine ⟨relationWitness R i j, ?_, ?_⟩
      · rw [mem_adjacencyCases_iff]
        exact ⟨R, i, j, hij, rfl⟩
      · rw [sat_relationWitness]
        exact ⟨tuple, hR, hi, hj⟩
  · exact Formula.not_sat_falsity A env 0

/-- Restricted satisfaction still defines adjacency when every entry of a
witnessing tuple lies in the restriction domain. -/
theorem satRestricted_adjacencyFormula {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (D : M → Prop) (env : Fin 2 → M)
    (hclosed : ∀ (R : σ.Relation) (tuple : Fin (σ.arity R) → M)
      (i j : Fin (σ.arity R)), A.relation R tuple →
        tuple i = env 0 → tuple j = env 1 → i ≠ j → ∀ l, D (tuple l)) :
    SatRestricted A D (adjacencyFormula σ) env ↔
      gaifmanAdjacent A (env 0) (env 1) := by
  rw [adjacencyFormula, satRestricted_conjunction]
  simp only [SatRestricted]
  apply and_congr_right
  intro hne
  change env 0 ≠ env 1 at hne
  rw [satRestricted_disjunctions]
  · constructor
    · rintro ⟨φ, hφ, hsφ⟩
      rw [mem_adjacencyCases_iff] at hφ
      rcases hφ with ⟨R, i, j, hij, rfl⟩
      rw [satRestricted_relationWitness] at hsφ
      rcases hsφ with ⟨tuple, _, hR, hi, hj⟩
      exact ⟨R, tuple, hR, i, j, hij, hi, hj⟩
    · rintro ⟨R, tuple, hR, i, j, hij, hi, hj⟩
      refine ⟨relationWitness R i j, ?_, ?_⟩
      · rw [mem_adjacencyCases_iff]
        exact ⟨R, i, j, hij, rfl⟩
      · rw [satRestricted_relationWitness]
        exact ⟨tuple, hclosed R tuple i j hR hi hj hij, hR, hi, hj⟩
  · simp [Formula.falsity, Formula.truth, SatRestricted]

end Lax185574Proofs.Gaifman.AdjacencyFormula
