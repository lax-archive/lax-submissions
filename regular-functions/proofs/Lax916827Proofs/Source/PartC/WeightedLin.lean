/-
Linear representations of weighted automata, with an arbitrary initial vector.

This file provides the converse of `Transducers.WNF.exists_linRep`: a function
given by a linear representation is computed by a weighted automaton.  It is the
basic tool for the proof of Theorem `thm:decidable-equivalence-regular` in the book (*Transducers*,
M. Bojańczyk), where the equivalence problem for regular functions is reduced to
the zeroness problem for weighted automata by showing that weighted automata are
closed under pre-composition with the prime regular functions: the constructions
for map reverse and map duplicate are carried out on linear representations, in
`RequestProject/PartC/WeightedMapLift.lean`.

The weighted automaton for a linear representation is obtained for free from the
product construction of `RequestProject/PartB/WeightedPrecomp.lean`, applied to
the identity function (which is rational, hence computed by a bimachine).  An
arbitrary initial row vector is then accommodated by adding one fresh state.
-/
import Lax132576Proofs.Source.PartB.WeightedPrecomp
import Lax916827Proofs.Source.PartC.RatBuild
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace WLin

open WPre

variable {B S : Type} [Semiring S] {Q : Type} [Fintype Q] [DecidableEq Q]

/-! ## Elementary facts about `tailVal` -/

@[simp] lemma tailVal_nil (m : B → Matrix Q Q S) (bta : Q → S) (q : Q) :
    tailVal m bta q [] = bta q := by
  simp [tailVal, mStr, Matrix.one_apply, ite_mul]

lemma tailVal_cons (m : B → Matrix Q Q S) (bta : Q → S) (q : Q) (b : B) (v : List B) :
    tailVal m bta q (b :: v) = ∑ q' : Q, m b q q' * tailVal m bta q' v := by
  have h := tailVal_append m bta q [b] v
  simpa [mStr] using h

/-- The value of a linear representation with an arbitrary initial row vector. -/
noncomputable def lval (alpha : Q → S) (m : B → Matrix Q Q S) (bta : Q → S) (v : List B) : S :=
  ∑ q : Q, alpha q * tailVal m bta q v

lemma lval_nil (alpha : Q → S) (m : B → Matrix Q Q S) (bta : Q → S) :
    lval alpha m bta [] = ∑ q : Q, alpha q * bta q := by
  simp [lval]

lemma lval_cons (alpha : Q → S) (m : B → Matrix Q Q S) (bta : Q → S) (b : B) (v : List B) :
    lval alpha m bta (b :: v) = ∑ q : Q, alpha q * ∑ q' : Q, m b q q' * tailVal m bta q' v := by
  simp [lval, tailVal_cons]

/-! ## A weighted automaton for a linear representation -/

/-- A function given by a linear representation is computed by a weighted
automaton.  This is the converse of `Transducers.WNF.exists_linRep`. -/
theorem isWeighted_of_linRep [Finite B] (m : B → Matrix Q Q S) (I : Finset Q) (bta : Q → S) :
    IsWeighted (fun v : List B => val m I bta v) := by
  classical
  obtain ⟨P, R, hP, hR, bm, hbm⟩ :=
    isBimachine_of_rationalFun (isRationalFun_map (id : B → B))
  letI : Fintype P := Fintype.ofFinite P
  letI : Fintype R := Fintype.ofFinite R
  refine ⟨WPre.WSt P R Q, inferInstance, WPre.W bm m I bta,
    WPre.W_finitelyManyRuns bm m I bta, ?_⟩
  funext v
  rw [WPre.wEval_W bm m I bta v]
  have : bm.eval v = v := by rw [hbm]; simp
  rw [this]

/-! ### Adding an initial vector -/

section Vec

variable (alpha : Q → S) (m : B → Matrix Q Q S) (bta : Q → S)

/-- The matrices of the linear representation with one extra state, which
carries the initial vector. -/
noncomputable def vecMat : B → Matrix (Option Q) (Option Q) S := fun b =>
  Matrix.of fun s t =>
    match s, t with
    | none, none => 0
    | none, some t' => ∑ q : Q, alpha q * m b q t'
    | some _, none => 0
    | some s', some t' => m b s' t'

/-- The final vector of the linear representation with one extra state. -/
noncomputable def vecBta : Option Q → S
  | none => ∑ q : Q, alpha q * bta q
  | some q => bta q

lemma tailVal_vec_some (q : Q) (v : List B) :
    tailVal (vecMat alpha m) (vecBta alpha bta) (some q) v = tailVal m bta q v := by
  induction v generalizing q with
  | nil => simp [vecBta]
  | cons b v ih =>
      rw [tailVal_cons, tailVal_cons, Fintype.sum_option]
      have h0 : (vecMat alpha m) b (some q) none = 0 := rfl
      rw [h0, zero_mul, zero_add]
      exact Finset.sum_congr rfl (fun q' _ => by rw [ih q']; rfl)

lemma tailVal_vec_none (v : List B) :
    tailVal (vecMat alpha m) (vecBta alpha bta) none v = lval alpha m bta v := by
  cases v with
  | nil => simp [vecBta, lval]
  | cons b v =>
      rw [tailVal_cons, Fintype.sum_option]
      have h0 : (vecMat alpha m) b none none = 0 := rfl
      rw [h0, zero_mul, zero_add]
      have hstep : ∀ q' : Q, (vecMat alpha m) b none (some q') = ∑ q : Q, alpha q * m b q q' :=
        fun _ => rfl
      calc ∑ q' : Q, (vecMat alpha m) b none (some q') *
              tailVal (vecMat alpha m) (vecBta alpha bta) (some q') v
          = ∑ q' : Q, ∑ q : Q, alpha q * (m b q q' * tailVal m bta q' v) := by
            refine Finset.sum_congr rfl (fun q' _ => ?_)
            rw [hstep q', tailVal_vec_some, Finset.sum_mul]
            exact Finset.sum_congr rfl (fun q _ => by rw [mul_assoc])
        _ = ∑ q : Q, ∑ q' : Q, alpha q * (m b q q' * tailVal m bta q' v) := Finset.sum_comm
        _ = lval alpha m bta (b :: v) := by
            rw [lval]
            refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [tailVal_cons, Finset.mul_sum]

/-- A function given by a linear representation with an arbitrary initial row
vector is computed by a weighted automaton. -/
theorem isWeighted_lval [Finite B] : IsWeighted (lval alpha m bta) := by
  classical
  have h := isWeighted_of_linRep (vecMat alpha m) ({none} : Finset (Option Q)) (vecBta alpha bta)
  have heq : (fun v : List B => val (vecMat alpha m) ({none} : Finset (Option Q))
      (vecBta alpha bta) v) = lval alpha m bta := by
    funext v
    rw [val, Finset.sum_singleton, tailVal_vec_none]
  rwa [heq] at h

end Vec

/-- Every function computed by a weighted automaton is the value of a linear
representation with an initial row vector. -/
theorem exists_lval {h : List B → S} (hw : IsWeighted h) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (alpha : Q → S) (m : B → Matrix Q Q S)
      (bta : Q → S), h = lval alpha m bta := by
  classical
  obtain ⟨Q, hQ, hdec, I, m, bta, hlin⟩ := WNF.exists_linRep hw
  refine ⟨Q, hQ, hdec, fun q => if q ∈ I then 1 else 0, m, bta, ?_⟩
  funext v
  rw [hlin v, lval]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rfl

/-! ## Differences of weighted automata -/

section Sub

variable {B S : Type} [Ring S] {Q₁ Q₂ : Type} [Fintype Q₁] [DecidableEq Q₁]
  [Fintype Q₂] [DecidableEq Q₂]

/-- The matrices of the direct sum of two linear representations. -/
noncomputable def sumMat (m₁ : B → Matrix Q₁ Q₁ S) (m₂ : B → Matrix Q₂ Q₂ S) :
    B → Matrix (Q₁ ⊕ Q₂) (Q₁ ⊕ Q₂) S :=
  fun b => Matrix.fromBlocks (m₁ b) 0 0 (m₂ b)

lemma tailVal_sumMat_inl (m₁ : B → Matrix Q₁ Q₁ S) (m₂ : B → Matrix Q₂ Q₂ S)
    (bta₁ : Q₁ → S) (bta₂ : Q₂ → S) (q : Q₁) (v : List B) :
    tailVal (sumMat m₁ m₂) (Sum.elim bta₁ (fun q => -bta₂ q)) (Sum.inl q) v
      = tailVal m₁ bta₁ q v := by
  induction v generalizing q with
  | nil => simp
  | cons b v ih =>
      rw [tailVal_cons, tailVal_cons, Fintype.sum_sum_type]
      have h2 : ∀ q' : Q₂, (sumMat m₁ m₂) b (Sum.inl q) (Sum.inr q') = 0 := by
        intro q'; simp [sumMat]
      simp only [h2, zero_mul, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl (fun q' _ => ?_)
      rw [ih q']
      congr 1

lemma tailVal_sumMat_inr (m₁ : B → Matrix Q₁ Q₁ S) (m₂ : B → Matrix Q₂ Q₂ S)
    (bta₁ : Q₁ → S) (bta₂ : Q₂ → S) (q : Q₂) (v : List B) :
    tailVal (sumMat m₁ m₂) (Sum.elim bta₁ (fun q => -bta₂ q)) (Sum.inr q) v
      = -tailVal m₂ bta₂ q v := by
  induction v generalizing q with
  | nil => simp
  | cons b v ih =>
      rw [tailVal_cons, tailVal_cons, Fintype.sum_sum_type]
      have h1 : ∀ q' : Q₁, (sumMat m₁ m₂) b (Sum.inr q) (Sum.inl q') = 0 := by
        intro q'; simp [sumMat]
      simp only [h1, zero_mul, Finset.sum_const_zero, zero_add]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun q' _ => ?_)
      rw [ih q']
      have : (sumMat m₁ m₂) b (Sum.inr q) (Sum.inr q') = m₂ b q q' := by simp [sumMat]
      rw [this, mul_neg]

/-- Functions computed by weighted automata over a ring are closed under
differences.  This is the reduction of the equivalence problem to the zeroness
problem. -/
theorem isWeighted_sub [Finite B] {h₁ h₂ : List B → S}
    (hw₁ : IsWeighted h₁) (hw₂ : IsWeighted h₂) : IsWeighted (fun v => h₁ v - h₂ v) := by
  classical
  obtain ⟨Q₁, hQ₁, hd₁, alpha₁, m₁, bta₁, hrep₁⟩ := exists_lval hw₁
  obtain ⟨Q₂, hQ₂, hd₂, alpha₂, m₂, bta₂, hrep₂⟩ := exists_lval hw₂
  have heq : (fun v : List B => h₁ v - h₂ v)
      = lval (Sum.elim alpha₁ alpha₂) (sumMat m₁ m₂)
        (Sum.elim bta₁ (fun q => -bta₂ q)) := by
    funext v
    rw [lval, Fintype.sum_sum_type]
    have e1 : ∀ q : Q₁, (Sum.elim alpha₁ alpha₂) (Sum.inl q) *
        tailVal (sumMat m₁ m₂) (Sum.elim bta₁ (fun q => -bta₂ q)) (Sum.inl q) v
        = alpha₁ q * tailVal m₁ bta₁ q v := by
      intro q
      rw [tailVal_sumMat_inl]
      rfl
    have e2 : ∀ q : Q₂, (Sum.elim alpha₁ alpha₂) (Sum.inr q) *
        tailVal (sumMat m₁ m₂) (Sum.elim bta₁ (fun q => -bta₂ q)) (Sum.inr q) v
        = -(alpha₂ q * tailVal m₂ bta₂ q v) := by
      intro q
      rw [tailVal_sumMat_inr]
      simp
    rw [Finset.sum_congr rfl (fun q _ => e1 q), Finset.sum_congr rfl (fun q _ => e2 q),
      Finset.sum_neg_distrib, hrep₁, hrep₂, lval, lval, sub_eq_add_neg]
  rw [heq]
  exact isWeighted_lval _ _ _

end Sub

end WLin

end Lax916827Proofs.Transducers
