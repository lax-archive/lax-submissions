import Lax185574Proofs.Gaifman.AdjacencyFormula
import Mathlib.Tactic

/-!
First-order formulas for bounded Gaifman distance, built from the explicit
adjacency formula.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/DistanceFormula.lean`.
-/

namespace Lax185574Proofs.Gaifman.DistanceFormula

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.FirstOrder
open Lax185574Proofs.Gaifman.Locality Lax185574Proofs.Gaifman.FormulaUtils
open Lax185574Proofs.Gaifman.AdjacencyFormula
open Lax185574Proofs.Gaifman.Relativize Lax185574Proofs.Gaifman.Distance

/-- Rename two endpoints to the old left endpoint and a new last variable. -/
def leftNew : Fin 2 → Fin 3 :=
  Fin.cases 0 (fun _ => 2)

/-- Rename two endpoints to a new last variable and the old right endpoint. -/
def newRight : Fin 2 → Fin 3 :=
  Fin.cases 2 (fun _ => 1)

/-- Formula saying that its two free variables have Gaifman distance at most
`d`. -/
noncomputable def distanceFormula (σ : Vocabulary) : ℕ → Formula σ 2
  | 0 => .eq (.var 0) (.var 1)
  | d + 1 =>
      .or (distanceFormula σ d)
        (.ex (Formula.conjunction
          (Formula.rename leftNew (adjacencyFormula σ))
          (Formula.rename newRight (distanceFormula σ d))))

@[simp] theorem leftNew_zero : leftNew 0 = 0 := rfl
@[simp] theorem leftNew_one : leftNew 1 = 2 := rfl
@[simp] theorem newRight_zero : newRight 0 = 2 := rfl
@[simp] theorem newRight_one : newRight 1 = 1 := rfl

@[simp] theorem snoc_fin3_zero {α : Type*} (env : Fin 2 → α) (x : α) :
    (Fin.snoc env x : Fin 3 → α) (0 : Fin 3) = env 0 := by
  rw [show (0 : Fin 3) = (0 : Fin 2).castSucc by rfl, Fin.snoc_castSucc]

@[simp] theorem snoc_fin3_one {α : Type*} (env : Fin 2 → α) (x : α) :
    (Fin.snoc env x : Fin 3 → α) (1 : Fin 3) = env 1 := by
  rw [show (1 : Fin 3) = (1 : Fin 2).castSucc by rfl, Fin.snoc_castSucc]

@[simp] theorem snoc_fin3_two {α : Type*} (env : Fin 2 → α) (x : α) :
    (Fin.snoc env x : Fin 3 → α) (2 : Fin 3) = x := by
  rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.snoc_last]

/-- Correctness of the bounded-distance formula. -/
theorem sat_distanceFormula {σ : Vocabulary} {M : Type*}
    (A : Structure σ M) (env : Fin 2 → M) (d : ℕ) :
    Formula.Sat A (distanceFormula σ d) env ↔
      distanceAtMost A d (env 0) (env 1) := by
  induction d generalizing env with
  | zero => rfl
  | succ d ih =>
      simp only [distanceFormula, Formula.Sat, Formula.sat_conjunction]
      apply or_congr (ih env)
      apply exists_congr
      intro x
      rw [Formula.sat_rename, Formula.sat_rename]
      rw [sat_adjacencyFormula, ih]
      rfl

/-- Relativizing the distance formula to a ball does not change its meaning
when the left endpoint starts at radius `s` and the entire distance budget fits
inside the ambient radius. -/
theorem satRestricted_distanceFormula_of_ball
    {σ : Vocabulary} {M : Type*} (A : Structure σ M)
    {k R s d : ℕ} (anchors : Fin k → M) (env : Fin 2 → M)
    (hstart : inBallAround A s anchors (env 0)) (hbudget : s + d ≤ R) :
    SatRestricted A (inBallAround A R anchors) (distanceFormula σ d) env ↔
      distanceAtMost A d (env 0) (env 1) := by
  induction d generalizing s env with
  | zero => rfl
  | succ d ih =>
      simp only [distanceFormula, SatRestricted, satRestricted_conjunction]
      constructor
      · rintro (hshort | ⟨x, hxR, hadjR, hdistR⟩)
        · exact Or.inl ((ih env hstart (by omega)).mp hshort)
        · have hadjIff :
              SatRestricted A (inBallAround A R anchors)
                  (adjacencyFormula σ) (Fin.snoc env x ∘ leftNew) ↔
                gaifmanAdjacent A (env 0) x := by
            have hclosed : ∀ (Q : σ.Relation)
                (tuple : Fin (σ.arity Q) → M) (i j : Fin (σ.arity Q)),
                A.relation Q tuple → tuple i = (Fin.snoc env x ∘ leftNew) 0 →
                tuple j = (Fin.snoc env x ∘ leftNew) 1 → i ≠ j →
                ∀ l, inBallAround A R anchors (tuple l) := by
              intro Q tuple i j hQ hi hj hij l
              have hi' : tuple i = env 0 := by
                simpa [Function.comp_apply] using hi
              have hiBall : inBallAround A s anchors (tuple i) := by
                simpa [hi'] using hstart
              have htuple := inBallAround_of_distance A anchors hiBall
                (relation_tuple_distance_one A hQ i l)
              exact inBallAround_mono A (by omega) anchors htuple
            simpa [Function.comp_apply] using
              satRestricted_adjacencyFormula A
                (inBallAround A R anchors) (Fin.snoc env x ∘ leftNew) hclosed
          rw [satRestricted_rename] at hadjR hdistR
          have hadj : gaifmanAdjacent A (env 0) x := hadjIff.mp hadjR
          have hxSmall : inBallAround A (s + 1) anchors x :=
            inBallAround_of_distance A anchors hstart
              (distanceAtMost_one_of_adjacent A hadj)
          have hdist : distanceAtMost A d x (env 1) := by
            have := (ih (Fin.snoc env x ∘ newRight) hxSmall
              (by omega)).mp hdistR
            simpa [Function.comp_apply] using this
          exact Or.inr ⟨x, hadj, hdist⟩
      · rintro (hshort | ⟨x, hadj, hdist⟩)
        · exact Or.inl ((ih env hstart (by omega)).mpr hshort)
        · have hxSmall : inBallAround A (s + 1) anchors x :=
            inBallAround_of_distance A anchors hstart
              (distanceAtMost_one_of_adjacent A hadj)
          have hxR : inBallAround A R anchors x :=
            inBallAround_mono A (by omega) anchors hxSmall
          refine Or.inr ⟨x, hxR, ?_, ?_⟩
          · rw [satRestricted_rename]
            have hclosed : ∀ (Q : σ.Relation)
                (tuple : Fin (σ.arity Q) → M) (i j : Fin (σ.arity Q)),
                A.relation Q tuple → tuple i = (Fin.snoc env x ∘ leftNew) 0 →
                tuple j = (Fin.snoc env x ∘ leftNew) 1 → i ≠ j →
                ∀ l, inBallAround A R anchors (tuple l) := by
              intro Q tuple i j hQ hi hj hij l
              have hi' : tuple i = env 0 := by
                simpa [Function.comp_apply] using hi
              have hiBall : inBallAround A s anchors (tuple i) := by
                simpa [hi'] using hstart
              have htuple := inBallAround_of_distance A anchors hiBall
                (relation_tuple_distance_one A hQ i l)
              exact inBallAround_mono A (by omega) anchors htuple
            exact (satRestricted_adjacencyFormula A
              (inBallAround A R anchors) (Fin.snoc env x ∘ leftNew) hclosed).mpr
                (by simpa [Function.comp_apply] using hadj)
          · rw [satRestricted_rename]
            exact (ih (Fin.snoc env x ∘ newRight) hxSmall
              (by omega)).mpr (by simpa [Function.comp_apply] using hdist)

end Lax185574Proofs.Gaifman.DistanceFormula
