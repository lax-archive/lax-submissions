import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Lax457868Proofs.SamplerPhases

/-!
Finite trace representatives contract both sides of the incidence relation.
The resulting size recurrence yields a logarithmic number of rounds.
-/

namespace Lax457868Proofs.ContractionRounds

open Lax457868Proofs.SamplerPhases

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A legal representative map for a finite set equipped with a label. -/
structure RepresentativeChoice (S : Finset α) (label : α → β) where
  representative : α → α
  representative_mem : ∀ x ∈ S, representative x ∈ S
  representative_label : ∀ x ∈ S, label (representative x) = label x
  representative_constant : ∀ x ∈ S, ∀ y ∈ S,
    label x = label y → representative x = representative y

/-- A deterministic choice from each nonempty finite label fiber. -/
noncomputable def representativeByLabel (S : Finset α) (label : α → β)
    (z : β) : Option α := by
  classical
  exact if h : ∃ x, x ∈ S ∧ label x = z then some (Classical.choose h) else none

/-- Choose one member of each label class, with the choice depending only on
that label. -/
noncomputable def chooseRepresentatives (S : Finset α) (label : α → β) :
    RepresentativeChoice S label := by
  classical
  let rep : α → α := fun x => (representativeByLabel S label (label x)).getD x
  refine ⟨rep, ?_, ?_, ?_⟩
  · intro x hx
    have hxExists : ∃ y, y ∈ S ∧ label y = label x := ⟨x, hx, rfl⟩
    have hspec := Classical.choose_spec hxExists
    simpa [rep, representativeByLabel, hxExists] using hspec.1
  · intro x hx
    have hxExists : ∃ y, y ∈ S ∧ label y = label x := ⟨x, hx, rfl⟩
    have hspec := Classical.choose_spec hxExists
    simpa [rep, representativeByLabel, hxExists] using hspec.2
  · intro x hx y hy hxy
    have hxExists : ∃ z, z ∈ S ∧ label z = label x := ⟨x, hx, rfl⟩
    have hyExists : ∃ z, z ∈ S ∧ label z = label y := ⟨y, hy, rfl⟩
    have hxopt : representativeByLabel S label (label x) = some (rep x) := by
      simp [rep, representativeByLabel, hxExists]
    have hyopt : representativeByLabel S label (label y) = some (rep y) := by
      simp [rep, representativeByLabel, hyExists]
    have hlabels : representativeByLabel S label (label x) =
        representativeByLabel S label (label y) := congrArg
          (representativeByLabel S label) hxy
    have hsame : some (rep x) = some (rep y) := hxopt.symm.trans (hlabels.trans hyopt)
    exact Option.some.inj hsame

/-- The chosen representatives have exactly as many elements as there are
labels on the original finite set. -/
lemma representative_image_card_eq (S : Finset α) (label : α → β)
    (choice : RepresentativeChoice S label) :
    (S.image choice.representative).card = (S.image label).card := by
  classical
  let R := S.image choice.representative
  have himage : R.image label = S.image label := by
    rw [show R = S.image choice.representative by rfl, Finset.image_image]
    apply Finset.image_congr
    intro x hx
    exact choice.representative_label x hx
  have hinj : Set.InjOn label (↑R : Set α) := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    exact choice.representative_constant a ha b hb
      ((choice.representative_label a ha).symm.trans
        (hxy.trans (choice.representative_label b hb)))
  have hcard : (R.image label).card = R.card := Finset.card_image_iff.mpr hinj
  rw [himage] at hcard
  simpa [R] using hcard.symm

/-- The distinct neighborhood traces on a sample. -/
def primalTraceClasses (N : β → Finset α) (W : Finset α)
    (B : Finset β) : Finset (Finset α) :=
  traceClasses N W B

/-- The distinct incidence traces of ground vertices on a finite set of
neighborhood indices. -/
def dualTraceClasses (N : β → Finset α) (A : Finset α)
    (Y : Finset β) : Finset (Finset β) :=
  A.image (fun a => Y.filter fun b => a ∈ N b)

/-- Contract both sides of the incidence relation: first choose one vertex
per neighborhood trace on `W`, then one ground vertex per incidence trace on
the retained vertices. -/
structure TraceContraction (A : Finset α) (B : Finset β)
    (N : β → Finset α) (W : Finset α) where
  retainedB : Finset β
  retainedB_subset : retainedB ⊆ B
  retainedB_card : retainedB.card = (primalTraceClasses N W B).card
  retainedA : Finset α
  retainedA_subset : retainedA ⊆ A
  retainedA_card : retainedA.card = (dualTraceClasses N A retainedB).card

/-- A finite contraction exists by taking actual representatives of both
finite label maps. -/
noncomputable def chooseTraceContraction (A : Finset α) (B : Finset β)
    (N : β → Finset α) (W : Finset α) : TraceContraction A B N W := by
  classical
  let bChoice := chooseRepresentatives B (fun b => N b ∩ W)
  let B' := B.image bChoice.representative
  let aChoice := chooseRepresentatives A (fun a => B'.filter fun b => a ∈ N b)
  refine ⟨B', ?_, ?_, A.image aChoice.representative, ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨x, hx, rfl⟩
    exact bChoice.representative_mem x hx
  · rw [representative_image_card_eq B (fun b => N b ∩ W) bChoice]
    rfl
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    exact aChoice.representative_mem x hx
  · rw [representative_image_card_eq A (fun a => B'.filter (fun b => a ∈ N b)) aChoice]
    rfl

/-- A one-label bound also covers an empty trace ground set: there is at most
one distinct trace, including when the original family is empty. -/
lemma primalTraceClasses_card_le_one_of_empty {α β : Type*} [DecidableEq α]
    (N : β → Finset α) (B : Finset β) : (primalTraceClasses N ∅ B).card ≤ 1 := by
  classical
  unfold primalTraceClasses
  have hsub : B.image (fun b => N b ∩ ∅) ⊆ {∅} := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨b, _, rfl⟩
    simp
  exact (Finset.card_le_card hsub).trans (by simp)

/-- On an empty index set every dual trace is empty, so at most one trace
occurs regardless of the ground set. -/
lemma dualTraceClasses_card_le_one_of_empty (N : β → Finset α)
    (A : Finset α) :
    (dualTraceClasses N A (∅ : Finset β)).card ≤ 1 := by
  classical
  unfold dualTraceClasses
  have hsub : A.image (fun a => (∅ : Finset β).filter fun b => a ∈ N b) ⊆ {∅} := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨a, _, rfl⟩
    simp
  exact (Finset.card_le_card hsub).trans (by simp)

/-- The two representative contractions obey the refined linear size bound.
The two exceptional empty cases use the fact that a trace family on an empty
or singleton ground set has at most one member. -/
theorem traceContraction_size_bound
    (A : Finset α) (B : Finset β) (N : β → Finset α) (W : Finset α)
    (c : ℕ) (hc : 1 ≤ c)
    (hW : W ⊆ A)
    (hWsize : W.card ≤ (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2))
    (hprimal : ∀ X : Finset α, X ⊆ A → X.Nonempty →
      (primalTraceClasses N X B).card ≤ c * X.card)
    (hdual : ∀ Y : Finset β, Y ⊆ B → Y.Nonempty →
      (dualTraceClasses N A Y).card ≤ c * Y.card)
    (contraction : TraceContraction A B N W) :
    2 * contraction.retainedA.card ≤ A.card + 2 * c ^ 2 := by
  classical
  by_cases hW0 : W = ∅
  · have hBsmall : contraction.retainedB.card ≤ 1 := by
      rw [contraction.retainedB_card, hW0]
      exact primalTraceClasses_card_le_one_of_empty N B
    have hAsmall : contraction.retainedA.card ≤ c := by
      by_cases hB0 : contraction.retainedB = ∅
      · rw [contraction.retainedA_card, hB0]
        have hone := dualTraceClasses_card_le_one_of_empty N A
        omega
      · have hBne := Finset.nonempty_iff_ne_empty.mpr hB0
        have hdual' := hdual contraction.retainedB contraction.retainedB_subset hBne
        rw [contraction.retainedA_card]
        calc
          (dualTraceClasses N A contraction.retainedB).card ≤
              c * contraction.retainedB.card := hdual'
          _ ≤ c * 1 := Nat.mul_le_mul_left c hBsmall
          _ = c := by simp
    have hfinal : 2 * contraction.retainedA.card ≤ A.card + 2 * c ^ 2 := by
      have hc2 : c ≤ c ^ 2 := by nlinarith
      nlinarith
    exact hfinal
  · have hWne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW0
    have hBbound : contraction.retainedB.card ≤ c * W.card := by
      rw [contraction.retainedB_card]
      exact hprimal W hW hWne
    have hAbound : contraction.retainedA.card ≤ c ^ 2 * W.card := by
      by_cases hB0 : contraction.retainedB = ∅
      · rw [contraction.retainedA_card, hB0]
        have hone := dualTraceClasses_card_le_one_of_empty N A
        have hWcard : 1 ≤ W.card := Finset.card_pos.mpr hWne
        have hc2 : 1 ≤ c ^ 2 := by nlinarith
        nlinarith
      · have hBne := Finset.nonempty_iff_ne_empty.mpr hB0
        have hdual' := hdual contraction.retainedB contraction.retainedB_subset hBne
        rw [contraction.retainedA_card]
        calc
          (dualTraceClasses N A contraction.retainedB).card ≤
              c * contraction.retainedB.card := hdual'
          _ ≤ c * (c * W.card) := Nat.mul_le_mul_left c hBbound
          _ = c ^ 2 * W.card := by ring
    let M := A.card + 2 * c ^ 2 - 1
    have hden : 0 < 2 * c ^ 2 := by positivity
    have hqmul : ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) *
        (2 * c ^ 2) ≤ M := by
      dsimp [M]
      exact Nat.div_mul_le_self _ _
    have hceil : c ^ 2 * ((A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)) ≤ M / 2 := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      nlinarith [hqmul]
    have hscaled : c ^ 2 * W.card ≤ M / 2 :=
      (Nat.mul_le_mul_left (c ^ 2) hWsize).trans hceil
    have hfinal : 2 * contraction.retainedA.card ≤ A.card + 2 * c ^ 2 := by
      calc
        2 * contraction.retainedA.card ≤ 2 * (c ^ 2 * W.card) :=
          Nat.mul_le_mul_left 2 hAbound
        _ ≤ M := by omega
        _ ≤ A.card + 2 * c ^ 2 := by dsimp [M]; omega
    exact hfinal

/-- The doubled contraction-size inequality implies the paper's rounded
half-size recurrence. -/
lemma contraction_size_to_quotient_step {n nnext c : ℕ}
    (h : 2 * nnext ≤ n + 2 * c ^ 2) :
    nnext ≤ n / 2 + c ^ 2 := by
  omega

/-- A strict rounded half-size bound yields the sharper doubled inequality,
including its natural-number minus-one margin. -/
lemma strict_quotient_step_to_size {n nnext c : ℕ}
    (h : nnext < n / 2 + c ^ 2) :
    2 * nnext ≤ n + 2 * c ^ 2 - 1 := by
  omega

/-- Clearing denominators in the contraction recurrence gives the geometric
bound after any number of rounds. -/
theorem contraction_geometric_bound (n : ℕ → ℕ) (c : ℕ)
    (hstep : ∀ t, 2 * n (t + 1) ≤ n t + 2 * c ^ 2) (t : ℕ) :
    2 ^ t * n t ≤ n 0 + 2 * c ^ 2 * (2 ^ t - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hmul := Nat.mul_le_mul_left (2 ^ t) (hstep t)
      have hpow : 2 ^ (t + 1) = 2 ^ t * 2 := by simp [pow_succ]
      rw [hpow]
      calc
        2 ^ t * 2 * n (t + 1) = 2 ^ t * (2 * n (t + 1)) := by ring
        _ ≤ 2 ^ t * (n t + 2 * c ^ 2) := hmul
        _ = 2 ^ t * n t + 2 * c ^ 2 * 2 ^ t := by ring
        _ ≤ n 0 + 2 * c ^ 2 * (2 ^ t - 1) + 2 * c ^ 2 * 2 ^ t :=
          Nat.add_le_add_right ih _
        _ = n 0 + 2 * c ^ 2 * ((2 ^ t - 1) + 2 ^ t) := by
          ring
        _ = n 0 + 2 * c ^ 2 * (2 ^ (t + 1) - 1) := by
          have hpow' : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
            rw [pow_succ]
            ring
          rw [hpow']
          congr 2
          omega

/-- The contracted size is at most `2k` after `clog2(n₀)-1` rounds when the
paper's stronger cutoff `6c² ≤ k` holds. -/
theorem contraction_logarithmic_rounds (n : ℕ → ℕ) (c k : ℕ)
    (hc : 2 ≤ c) (hk : 6 * c ^ 2 ≤ k)
    (hn0 : 2 ≤ n 0)
    (hstep : ∀ t, 2 * n (t + 1) ≤ n t + 2 * c ^ 2) :
    n (Nat.clog 2 (n 0) - 1) ≤ 2 * k := by
  let t := Nat.clog 2 (n 0) - 1
  have htpos : 0 < 2 ^ t := by positivity
  have hclog : n 0 ≤ 2 ^ Nat.clog 2 (n 0) :=
    Nat.le_pow_clog (by decide : 1 < 2) (n 0)
  have hlogpos : 1 ≤ Nat.clog 2 (n 0) := by
    by_contra h
    have hle : Nat.clog 2 (n 0) ≤ 0 := by omega
    have hsmall := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1 hle
    norm_num at hsmall
    omega
  have hpow : 2 ^ Nat.clog 2 (n 0) = 2 ^ t * 2 := by
    change 2 ^ Nat.clog 2 (n 0) = 2 ^ (Nat.clog 2 (n 0) - 1) * 2
    calc
      2 ^ Nat.clog 2 (n 0) =
          2 ^ ((Nat.clog 2 (n 0) - 1) + 1) := by
            rw [Nat.sub_add_cancel hlogpos]
      _ = 2 ^ (Nat.clog 2 (n 0) - 1) * 2 := by
            rw [pow_succ]
  have hbase : n 0 ≤ 2 ^ t * 2 := by omega
  have hgeom := contraction_geometric_bound n c hstep t
  have hratio : n t ≤ 2 * c ^ 2 + 2 := by
    have hupper : n 0 + 2 * c ^ 2 * (2 ^ t - 1) ≤
        2 ^ t * (2 + 2 * c ^ 2) := by
      calc
        n 0 + 2 * c ^ 2 * (2 ^ t - 1) ≤
            2 ^ t * 2 + 2 * c ^ 2 * (2 ^ t - 1) :=
          Nat.add_le_add_right hbase _
        _ ≤ 2 ^ t * 2 + 2 * c ^ 2 * 2 ^ t := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_left (2 * c ^ 2) (Nat.sub_le (2 ^ t) 1)) _
        _ = 2 ^ t * (2 + 2 * c ^ 2) := by ring
    have hmul : 2 ^ t * n t ≤ 2 ^ t * (2 + 2 * c ^ 2) := hgeom.trans hupper
    simpa [Nat.add_comm] using (Nat.le_of_mul_le_mul_left hmul htpos)
  have hsmall : 2 * c ^ 2 + 2 ≤ 2 * k := by nlinarith
  simpa [t, Nat.add_comm] using (hratio.trans hsmall)

end Lax457868Proofs.ContractionRounds
