import Lax457868Proofs.ClassBucketDomain
import Lax457868Proofs.ExceptionRefinementBridge
import Lax457868Proofs.SamplerInitialProbability
import Lax457868Proofs.SamplerFiniteMean

/-!
Transport compact numeric class labels and one representative per label to
the trace-class product choice space already used by the sampler's finite
probability model.
-/

namespace Lax457868Proofs.ClassChoiceTransport

open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.ExceptionRefinementBridge
open Lax457868Proofs.SamplerInitialExpectation
open Lax457868Proofs.SamplerInitialProbability
open Lax457868Proofs.SamplerFiniteMean
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

variable {A C : Finset ℕ} {N : ℕ → Finset ℕ} {r : ℕ}
  (draw : Fin r → A) (label : ℕ → ℕ) (q : ℕ)

/-- The representative fiber attached to compact label `d`. -/
abbrev NumericClassFiber (C : Finset ℕ) (label : ℕ → ℕ) (q : ℕ) (d : Fin q) :=
  {b // b ∈ C.filter (fun b => label b = d.val)}

/-- One explicit element of each occupied numeric class. -/
noncomputable def labelWitness (d : Fin q)
    (hoccupied : LabelsOccupyPrefix q label C) : NumericClassFiber C label q d := by
  have hpos : 0 < classMultiplicity label C d.val := hoccupied d.val d.isLt
  let hne : ∃ b, b ∈ C.filter (fun b => label b = d.val) :=
    Finset.card_pos.mp (by simpa [classMultiplicity] using hpos)
  exact ⟨Classical.choose hne, Classical.choose_spec hne⟩

/-- Turn a numeric label into the existing trace-class index, using its
explicit occupied witness. -/
noncomputable def classIndexOfLabel
    (hoccupied : LabelsOccupyPrefix q label C) (d : Fin q) :
    ClassIndex A C N draw := by
  let b := labelWitness label q d hoccupied
  refine ⟨trace N (drawSet A draw) b.1, ?_⟩
  exact Finset.mem_image.mpr ⟨b.1, (Finset.mem_filter.mp b.2).1, rfl⟩

lemma classIndexOfLabel_val (hoccupied : LabelsOccupyPrefix q label C) (d : Fin q) :
    (classIndexOfLabel (A := A) (C := C) (N := N) (draw := draw)
      (label := label) (q := q) hoccupied d).1 =
      trace N (drawSet A draw) (labelWitness label q d hoccupied).1 := rfl

/-- Compact labels and the existing trace classes are explicitly
equivalent, with each label sent to the trace of its selected class member. -/
noncomputable def classIndexEquiv
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace N (drawSet A draw) b = trace N (drawSet A draw) b')) :
    Fin q ≃ ClassIndex A C N draw := by
  classical
  apply Equiv.ofBijective (classIndexOfLabel draw label q hoccupied)
  constructor
  · intro d e hde
    let hb := labelWitness label q d hoccupied
    let he := labelWitness label q e hoccupied
    have hbEq : hb = labelWitness label q d hoccupied := rfl
    have heEq : he = labelWitness label q e hoccupied := rfl
    have htrace : trace N (drawSet A draw) hb.1 =
        trace N (drawSet A draw) he.1 := by
      have htrace' := congrArg Subtype.val hde
      rw [classIndexOfLabel_val (draw := draw) (label := label) (q := q)
        hoccupied d, classIndexOfLabel_val (draw := draw) (label := label) (q := q)
        hoccupied e] at htrace'
      rw [← hbEq, ← heEq] at htrace'
      change trace N (drawSet A draw) hb.1 = trace N (drawSet A draw) he.1 at htrace'
      exact htrace'
    have hlabels := (hlabel hb.1 (Finset.mem_filter.mp hb.2).1
      he.1 (Finset.mem_filter.mp he.2).1).2 htrace
    rw [(Finset.mem_filter.mp hb.2).2, (Finset.mem_filter.mp he.2).2] at hlabels
    exact Fin.ext hlabels
  · intro T
    obtain ⟨b, hbC, htrace⟩ := Finset.mem_image.mp T.2
    let d : Fin q := ⟨label b, hrange b hbC⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    let hw := labelWitness label q d hoccupied
    have hwEq : hw = labelWitness label q d hoccupied := rfl
    have hlabels : label b = label hw.1 := by
      calc
        label b = d.val := rfl
        _ = label hw.1 := (Finset.mem_filter.mp hw.2).2.symm
    rw [classIndexOfLabel_val (draw := draw) (label := label) (q := q) hoccupied d]
    rw [← hwEq]
    exact ((hlabel b hbC hw.1 (Finset.mem_filter.mp hw.2).1).1 hlabels).symm.trans htrace

/-- Every existing representative fiber is the same subtype as its numeric
label class, via the established label/trace-fiber bridge. -/
noncomputable def numericFiberEquiv (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace N (drawSet A draw) b = trace N (drawSet A draw) b'))
    (d : Fin q) :
    NumericClassFiber C label q d ≃
      RepFiber A C N draw (classIndexEquiv draw label q hrange hoccupied hlabel d) := by
  classical
  let b := labelWitness label q d hoccupied
  let heq := labelClass_eq_traceFiber A C N draw label d.val b.1
    (Finset.mem_filter.mp b.2).2 (Finset.mem_filter.mp b.2).1 hlabel
  have hindex : classIndexEquiv draw label q hrange hoccupied hlabel d =
      classIndexOfLabel draw label q hoccupied d := rfl
  have heq' : C.filter (fun x => label x = d.val) =
      traceFiber A C N draw (classIndexEquiv draw label q hrange hoccupied hlabel d).1 := by
    rw [hindex]
    rw [classIndexOfLabel_val (draw := draw) (label := label) (q := q) hoccupied d]
    change C.filter (fun x => label x = d.val) =
      traceFiber A C N draw (trace N (drawSet A draw) b.1)
    exact heq
  exact Equiv.setCongr (congrArg (fun X : Finset ℕ => (X : Set ℕ)) heq')

/-- Explicit equivalence from per-label source choices to the sampler's
existing independent trace-class representative choices. -/
noncomputable def numericChoicesEquiv
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace N (drawSet A draw) b = trace N (drawSet A draw) b')) :
    (∀ d : Fin q, NumericClassFiber C label q d) ≃
      RepChoices A C N draw :=
  Equiv.piCongr (classIndexEquiv draw label q hrange hoccupied hlabel)
    (numericFiberEquiv draw label q hrange hoccupied hlabel)

/-- At the class corresponding to `d`, transport returns the selected source
representative from exactly that numeric class. -/
lemma numericChoicesEquiv_lookup
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace N (drawSet A draw) b = trace N (drawSet A draw) b'))
    (choices : ∀ d : Fin q, NumericClassFiber C label q d) (d : Fin q) :
    (numericChoicesEquiv draw label q hrange hoccupied hlabel choices
      (classIndexOfLabel draw label q hoccupied d)).1 = (choices d).1 := by
  change ((classIndexEquiv draw label q hrange hoccupied hlabel).piCongr
    (numericFiberEquiv draw label q hrange hoccupied hlabel) choices
      (classIndexEquiv draw label q hrange hoccupied hlabel d)).1 = _
  rw [Equiv.piCongr_apply_apply]
  let hb := labelWitness label q d hoccupied
  let heq := labelClass_eq_traceFiber A C N draw label d.val hb.1
    (Finset.mem_filter.mp hb.2).2 (Finset.mem_filter.mp hb.2).1 hlabel
  have hindex : classIndexEquiv draw label q hrange hoccupied hlabel d =
      classIndexOfLabel draw label q hoccupied d := rfl
  have heq' : C.filter (fun x => label x = d.val) =
      traceFiber A C N draw (classIndexEquiv draw label q hrange hoccupied hlabel d).1 := by
    rw [hindex]
    change C.filter (fun x => label x = d.val) =
      traceFiber A C N draw (trace N (drawSet A draw) hb.1)
    exact heq
  exact congrArg Subtype.val (Equiv.setCongr_apply
    (congrArg (fun X : Finset ℕ => (X : Set ℕ)) heq') (choices d))

private lemma finiteMean_equiv_transport {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (f : Ξ → ℚ) :
    finiteMean (fun x => f (e x)) = finiteMean f := by
  classical
  unfold finiteMean
  rw [Fintype.sum_equiv e (fun x => f (e x)) f (by intro x; rfl),
    Fintype.card_congr e]

/-- The numeric product's finite mean of the existing sampler distance is
exactly its established conditional mean. This only reindexes the already
defined finite law; it introduces no new probability model. -/
lemma numericChoicesMean_eq_conditionalMeanZ
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace N (drawSet A draw) b = trace N (drawSet A draw) b')) :
    finiteMean (fun choices : ∀ d : Fin q, NumericClassFiber C label q d =>
      (totalDistance A C N draw
        (numericChoicesEquiv draw label q hrange hoccupied hlabel choices) : ℚ)) =
      conditionalMeanZ A C N draw := by
  rw [finiteMean_equiv_transport
    (numericChoicesEquiv draw label q hrange hoccupied hlabel)
    (fun reps : RepChoices A C N draw => (totalDistance A C N draw reps : ℚ))]
  exact conditionalMeanZ_eq_repMean A C N draw

end Lax457868Proofs.ClassChoiceTransport
