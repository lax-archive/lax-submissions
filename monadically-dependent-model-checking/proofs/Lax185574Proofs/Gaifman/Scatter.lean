import Lax185574Proofs.Gaifman.Distance
import Mathlib.Tactic

/-!
The finite scatter argument at the heart of Gaifman's existential step.  The
result is stated for an arbitrary unary predicate. Later modules instantiate
it with the semantics of a one-variable local formula.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/Scatter.lean`.
-/

namespace Lax185574Proofs.Gaifman.Scatter

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality
open Lax185574Proofs.Gaifman.Distance

variable {σ : Vocabulary} {M : Type*} (A : Structure σ M)

/-- A point is near a tuple if it lies in the union of the indicated balls. -/
def NearTuple {k : ℕ} (r : ℕ) (env : Fin k → M) (x : M) : Prop :=
  ∃ i, distanceAtMost A r (env i) x

/-- A tuple consists of pairwise `2r`-separated points satisfying `p`. -/
def IsScatter (r : ℕ) (p : M → Prop) {n : ℕ} (w : Fin n → M) : Prop :=
  (∀ i, p (w i)) ∧
    ∀ i j, i ≠ j → ¬ distanceAtMost A (2 * r) (w i) (w j)

/-- There is a scatter of the given size. -/
def HasScatter (r : ℕ) (p : M → Prop) (n : ℕ) : Prop :=
  ∃ w : Fin n → M, IsScatter A r p w

/-- There is a scatter of the given size entirely near the anchor tuple. -/
def HasNearScatter {k : ℕ} (r : ℕ) (env : Fin k → M)
    (p : M → Prop) (n : ℕ) : Prop :=
  ∃ w : Fin n → M,
    IsScatter A r p w ∧ ∀ i, NearTuple A r env (w i)

/-- The far existential that the normal-form construction must eliminate. -/
def HasFarWitness {k : ℕ} (r : ℕ) (env : Fin k → M) (p : M → Prop) : Prop :=
  ∃ x, ¬ NearTuple A r env x ∧ p x

/-- The local annulus case in the scatter argument. -/
def HasAnnulusWitness {k : ℕ} (r : ℕ) (env : Fin k → M)
    (p : M → Prop) : Prop :=
  ∃ x, NearTuple A (3 * r) env x ∧ ¬ NearTuple A r env x ∧ p x

/-- Successive truth and falsity in a finite sequence have a boundary. -/
theorem exists_boundary (P : ℕ → Prop) {k : ℕ}
    (h₁ : P 1) (hstop : ¬ P (k + 1)) :
    ∃ l, 1 ≤ l ∧ l ≤ k ∧ P l ∧ ¬ P (l + 1) := by
  induction k with
  | zero => exact False.elim (hstop h₁)
  | succ k ih =>
      by_cases hk : P (k + 1)
      · exact ⟨k + 1, by omega, by omega, hk, by simpa [Nat.succ_eq_add_one] using hstop⟩
      · obtain ⟨l, h1l, hlk, hPl, hnPl⟩ := ih hk
        exact ⟨l, h1l, by omega, hPl, hnPl⟩

/-- A scatter of `k+1` points contains a point outside the union of `k`
radius-`r` balls. -/
theorem far_of_large_scatter {k : ℕ} {r : ℕ} {env : Fin k → M}
    {p : M → Prop} (h : HasScatter A r p (k + 1)) :
    HasFarWitness A r env p := by
  rcases h with ⟨w, hp, hsep⟩
  by_contra hfar
  simp only [HasFarWitness, not_exists, not_and] at hfar
  have hnear : ∀ i, NearTuple A r env (w i) := by
    intro i
    by_contra hn
    exact (hfar (w i) hn) (hp i)
  choose anchor hanchor using hnear
  have hinj : Function.Injective anchor := by
    intro i j hij
    by_contra hne
    have hdist : distanceAtMost A (2 * r) (w i) (w j) := by
      have h₁ := distanceAtMost_symm A (hanchor i)
      have h₂ := distanceAtMost_trans A h₁ (hij ▸ hanchor j)
      simpa [two_mul] using h₂
    exact hsep i j hne hdist
  have hcard := Fintype.card_le_of_injective anchor hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- A far point appends to a near scatter when it lies outside the larger
`3r`-neighbourhood. -/
theorem snoc_scatter_of_far {k n r : ℕ} {env : Fin k → M} {p : M → Prop}
    {w : Fin n → M} {x : M}
    (hw : IsScatter A r p w) (hwNear : ∀ i, NearTuple A r env (w i))
    (hx : p x) (hxFar : ¬ NearTuple A (3 * r) env x) :
    IsScatter A r p (Fin.snoc w x) := by
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa using hw.1 j
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact False.elim (hij rfl)
      | cast j' =>
        intro hdist
        have hdist' : distanceAtMost A (2 * r) (w j') x :=
          distanceAtMost_symm A (by simpa using hdist)
        rcases hwNear j' with ⟨a, ha⟩
        apply hxFar
        refine ⟨a, ?_⟩
        have hpath := distanceAtMost_trans A ha hdist'
        convert hpath using 1 <;> omega
    | cast i' =>
      induction j using Fin.lastCases with
      | last =>
        intro hdist
        rcases hwNear i' with ⟨a, ha⟩
        apply hxFar
        refine ⟨a, ?_⟩
        have hpath := distanceAtMost_trans A ha (by simpa using hdist)
        convert hpath using 1 <;> omega
      | cast j' =>
        intro hdist
        apply hw.2 i' j'
        · intro h
          subst j'
          exact hij rfl
        · simpa using hdist

/-- Semantic form of the scatter case distinction.  A far witness exists iff
either there are `k+1` globally scattered witnesses, or the maximum global
scatter size `l ≤ k` is attained and one of the two local exceptional cases
occurs. -/
theorem hasFarWitness_iff {k r : ℕ} (env : Fin k → M) (p : M → Prop) :
    HasFarWitness A r env p ↔
      HasScatter A r p (k + 1) ∨
        ∃ l, 1 ≤ l ∧ l ≤ k ∧
          HasScatter A r p l ∧ ¬ HasScatter A r p (l + 1) ∧
            (¬ HasNearScatter A r env p l ∨ HasAnnulusWitness A r env p) := by
  constructor
  · intro hfar
    by_cases hlarge : HasScatter A r p (k + 1)
    · exact Or.inl hlarge
    · rcases hfar with ⟨x, hxNear, hpx⟩
      have hsingle : HasScatter A r p 1 := by
        refine ⟨fun _ => x, ?_⟩
        constructor
        · exact fun _ => hpx
        · intro i j hij
          exact False.elim (hij (Subsingleton.elim _ _))
      obtain ⟨l, h1l, hlk, hscatter, hnext⟩ :=
        exists_boundary (HasScatter A r p) hsingle hlarge
      refine Or.inr ⟨l, h1l, hlk, hscatter, hnext, ?_⟩
      by_cases hnear : HasNearScatter A r env p l
      · right
        by_cases hx3 : NearTuple A (3 * r) env x
        · exact ⟨x, hx3, hxNear, hpx⟩
        · rcases hnear with ⟨w, hw, hwNear⟩
          exact False.elim (hnext ⟨Fin.snoc w x,
            snoc_scatter_of_far A hw hwNear hpx hx3⟩)
      · exact Or.inl hnear
  · rintro (hlarge | ⟨l, h1l, hlk, hscatter, hnext, hlocal⟩)
    · exact far_of_large_scatter A hlarge
    · rcases hlocal with hnoNear | hannulus
      · rcases hscatter with ⟨w, hw⟩
        by_contra hfar
        simp only [HasFarWitness, not_exists, not_and] at hfar
        apply hnoNear
        refine ⟨w, hw, ?_⟩
        intro i
        by_contra hn
        exact (hfar (w i) hn) (hw.1 i)
      · rcases hannulus with ⟨x, hx3, hxr, hpx⟩
        exact ⟨x, hxr, hpx⟩

end Lax185574Proofs.Gaifman.Scatter
