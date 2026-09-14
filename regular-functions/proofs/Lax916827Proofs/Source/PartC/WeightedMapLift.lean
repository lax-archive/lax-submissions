/-
Weighted automata are closed under pre-composition with map lifting of the
prime block functions, i.e. with map reverse and map duplicate.

This is the construction of the proof of Theorem `thm:decidable-equivalence-regular` in the book
(*Transducers*, M. Bojańczyk): equivalence of regular functions is decided by a
reduction to zeroness of weighted automata over the rationals, and the reduction
needs that the class of functions that can be post-composed with weighted
automata contains the prime regular functions.  The two prime cases are map
reverse and map duplicate, which the book describes by pictures of automata with
triples of states.

The constructions are carried out here on *linear representations* rather than
on automata: a weighted automaton is turned into a linear representation
(`Transducers.WNF.exists_linRep`), the construction is a construction on
matrices, and the resulting linear representation is turned back into a weighted
automaton (`Transducers.WLin.isWeighted_lval`).  What both prime functions have
in common is isolated in the property `Transducers.WMap.MatLin`: the matrix of
the block `g v` is a fixed linear combination of the entries of the matrix of
`v` in an auxiliary representation.  For map reverse the auxiliary
representation consists of the transposed matrices (this is the "run the block
backwards" of the book, and it is where commutativity of the semiring is used),
and for map duplicate it consists of the Kronecker squares (the weight of a
transition is a product of the weights of two transitions of the original
automaton, as the book says).

The state space of the new representation is `Q × P × P`, matching the triples
of states in the book's pictures: the state of the original automaton at the
beginning of the current block, and the pair of auxiliary states.
-/
import Lax916827Proofs.Source.PartC.WeightedLin
import Lax916827Proofs.Source.PartC.ContAux
import Mathlib.LinearAlgebra.Matrix.Kronecker
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace WMap

open WPre WLin Matrix
open scoped Kronecker

/-! ## Matrix-linear block functions -/

/-- A block function `g` is *matrix-linear* over the commutative semiring `S` if,
for every family of matrices `m`, the matrix of `g v` is a fixed linear
combination of the entries of the matrix of `v` in an auxiliary family `N`. -/
def MatLin (S : Type) [CommSemiring S] {A₀ : Type} (g : List A₀ → List A₀) : Prop :=
  ∀ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (m : A₀ → Matrix Q Q S),
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (N : A₀ → Matrix P P S)
      (c : Q → Q → P → P → S),
      ∀ (v : List A₀) (i j : Q),
        mStr m (g v) i j = ∑ p : P, ∑ p' : P, c i j p p' * mStr N v p p'

/-! ## Splitting a string over `A + 1` at its first separator -/

lemma option_list_split {A : Type} (w : List (Option A)) :
    (∃ u : List A, w = u.map some) ∨
      ∃ (u : List A) (v : List (Option A)), w = u.map some ++ none :: v := by
  induction w with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons x w ih =>
      cases x with
      | none => exact Or.inr ⟨[], w, rfl⟩
      | some a =>
          rcases ih with ⟨u, rfl⟩ | ⟨u, v, rfl⟩
          · exact Or.inl ⟨a :: u, rfl⟩
          · exact Or.inr ⟨a :: u, v, rfl⟩

/-! ## Auxiliary facts about matrices of strings -/

section Aux

variable {S : Type} [CommSemiring S] {B Q P : Type} [Fintype Q] [DecidableEq Q]
  [Fintype P] [DecidableEq P]

lemma mStr_cons (m : B → Matrix Q Q S) (b : B) (v : List B) :
    mStr m (b :: v) = m b * mStr m v := by
  simp [mStr]

lemma mStr_one (v : List B) : mStr (fun _ : B => (1 : Matrix Q Q S)) v = 1 := by
  induction v with
  | nil => simp [mStr]
  | cons b v ih => rw [mStr_cons, ih, one_mul]

lemma mStr_map_some {A₀ : Type} (m : Option A₀ → Matrix Q Q S) (u : List A₀) :
    mStr m (u.map some) = mStr (fun a => m (some a)) u := by
  simp [mStr, List.map_map, Function.comp_def]

lemma mStr_kron (f : B → Matrix Q Q S) (g : B → Matrix P P S) (v : List B) :
    mStr (fun b => f b ⊗ₖ g b) v = mStr f v ⊗ₖ mStr g v := by
  induction v with
  | nil => simp [mStr]
  | cons b v ih =>
      rw [mStr_cons, ih, mStr_cons, mStr_cons, Matrix.mul_kronecker_mul]

lemma mStr_transpose (f : B → Matrix Q Q S) (v : List B) :
    mStr (fun b => (f b)ᵀ) v = (mStr f v.reverse)ᵀ := by
  induction v with
  | nil => simp [mStr]
  | cons b v ih =>
      rw [mStr_cons, ih, List.reverse_cons, mStr_append, ← Matrix.transpose_mul]
      simp [mStr]

end Aux

/-! ## The construction -/

section Construction

variable {A₀ S : Type} [CommSemiring S] {Q P : Type} [Fintype Q] [DecidableEq Q]
  [Fintype P] [DecidableEq P]
variable (m : Option A₀ → Matrix Q Q S) (bta : Q → S) (N : A₀ → Matrix P P S)
  (c : Q → Q → P → P → S)

/-- The matrices of the new linear representation, on the state space
`Q × P × P`.  Inside a block the two auxiliary coordinates run the block in the
auxiliary representation `N` and the first coordinate is unchanged; the
separator closes the block, applies the coefficients `c` and starts the next
one. -/
noncomputable def bmat : Option A₀ → Matrix (Q × P × P) (Q × P × P) S
  | some a => (1 : Matrix Q Q S) ⊗ₖ ((N a) ⊗ₖ (1 : Matrix P P S))
  | none => Matrix.of fun t t' =>
      if t.2.1 = t.2.2 then ∑ j : Q, m none t.1 j * c j t'.1 t'.2.1 t'.2.2 else 0

/-- The final vector of the new linear representation. -/
noncomputable def bbta : Q × P × P → S := fun t => if t.2.1 = t.2.2 then bta t.1 else 0

/-- The initial vector of the new linear representation, obtained from the
initial vector `alpha` of the original one. -/
noncomputable def balpha (alpha : Q → S) : Q × P × P → S :=
  fun t => ∑ i : Q, alpha i * c i t.1 t.2.1 t.2.2

lemma mStr_bmat_block (u : List A₀) :
    mStr (bmat m N c) (u.map some)
      = (1 : Matrix Q Q S) ⊗ₖ ((mStr N u) ⊗ₖ (1 : Matrix P P S)) := by
  rw [mStr_map_some]
  have h1 : (fun a => bmat m N c (some a))
      = fun a => (1 : Matrix Q Q S) ⊗ₖ ((N a) ⊗ₖ (1 : Matrix P P S)) := rfl
  rw [h1, mStr_kron (fun _ : A₀ => (1 : Matrix Q Q S))
    (fun a => (N a) ⊗ₖ (1 : Matrix P P S)), mStr_kron, mStr_one, mStr_one]

lemma mStr_bmat_block_apply (u : List A₀) (j j' : Q) (r q r' q' : P) :
    mStr (bmat m N c) (u.map some) (j, r, q) (j', r', q')
      = if j = j' ∧ q = q' then mStr N u r r' else 0 := by
  rw [mStr_bmat_block]
  by_cases hj : j = j' <;> by_cases hq : q = q' <;>
    simp [hj, hq]

/-- The value carried by the new representation at the start of a block:
the state of the run of the original representation is `j`, the two auxiliary
coordinates must agree, and the remaining value is `V j`. -/
def BlockVal (V : Q → S) (z : List (Option A₀)) : Prop :=
  ∀ (j : Q) (r q : P),
    tailVal (bmat m N c) (bbta bta) (j, r, q) z = if r = q then V j else 0

lemma blockVal_nil : BlockVal m bta N c bta [] := by
  intro j r q
  rw [tailVal_nil]
  rfl

/-- Reading a block: the value of the new representation over a block followed
by `z`. -/
lemma tailVal_block {V : Q → S} {z : List (Option A₀)} (hz : BlockVal m bta N c V z)
    (u : List A₀) (j : Q) (r q : P) :
    tailVal (bmat m N c) (bbta bta) (j, r, q) (u.map some ++ z) = mStr N u r q * V j := by
  classical
  rw [tailVal_append]
  rw [Fintype.sum_prod_type]
  have hstep : ∀ j' : Q, ∑ x : P × P,
      mStr (bmat m N c) (u.map some) (j, r, q) (j', x.1, x.2) *
        tailVal (bmat m N c) (bbta bta) (j', x.1, x.2) z
        = if j = j' then mStr N u r q * V j' else 0 := by
    intro j'
    rw [Fintype.sum_prod_type]
    by_cases hj : j = j'
    · subst hj
      simp only []
      have : ∀ r' : P, ∑ q' : P,
          mStr (bmat m N c) (u.map some) (j, r, q) (j, r', q') *
            tailVal (bmat m N c) (bbta bta) (j, r', q') z
          = mStr N u r r' * (if r' = q then V j else 0) := by
        intro r'
        have hsum : ∀ q' : P,
            mStr (bmat m N c) (u.map some) (j, r, q) (j, r', q') *
              tailVal (bmat m N c) (bbta bta) (j, r', q') z
            = if q' = q then mStr N u r r' * (if r' = q then V j else 0) else 0 := by
          intro q'
          rw [mStr_bmat_block_apply, hz j r' q']
          by_cases hq : q' = q
          · subst hq; simp
          · have hq' : ¬ (q = q') := fun h => hq h.symm
            simp [hq, hq']
        rw [Finset.sum_congr rfl (fun q' _ => hsum q'), Finset.sum_ite_eq' Finset.univ q]
        simp
      rw [Finset.sum_congr rfl (fun r' _ => this r')]
      have : ∀ r' : P, mStr N u r r' * (if r' = q then V j else 0)
          = if r' = q then mStr N u r q * V j else 0 := by
        intro r'
        by_cases h : r' = q
        · subst h; simp
        · simp [h]
      rw [Finset.sum_congr rfl (fun r' _ => this r'), Finset.sum_ite_eq' Finset.univ q]
      simp
    · have : ∀ r' q' : P,
          mStr (bmat m N c) (u.map some) (j, r, q) (j', r', q') *
            tailVal (bmat m N c) (bbta bta) (j', r', q') z = 0 := by
        intro r' q'
        rw [mStr_bmat_block_apply]
        simp [hj]
      simp [this, hj]
  rw [Finset.sum_congr rfl (fun j' _ => hstep j'), Finset.sum_ite_eq Finset.univ j]
  simp

/-- The contraction of the new representation against the coefficients `c`,
which is the quantity that the induction is about. -/
noncomputable def contract (w : List (Option A₀)) (i : Q) : S :=
  ∑ t : Q × P × P, c i t.1 t.2.1 t.2.2 * tailVal (bmat m N c) (bbta bta) t w

variable {g : List A₀ → List A₀}
  (hc : ∀ (v : List A₀) (i j : Q),
    mStr (fun a => m (some a)) (g v) i j = ∑ p : P, ∑ p' : P, c i j p p' * mStr N v p p')

include hc in
/-- The contraction over a block followed by `z`. -/
lemma contract_block {V : Q → S} {z : List (Option A₀)} (hz : BlockVal m bta N c V z)
    (u : List A₀) (i : Q) :
    contract m bta N c (u.map some ++ z) i
      = ∑ j : Q, mStr (fun a => m (some a)) (g u) i j * V j := by
  classical
  rw [contract, Fintype.sum_prod_type]
  have h1 : ∀ j : Q, ∑ x : P × P,
      c i j x.1 x.2 * tailVal (bmat m N c) (bbta bta) (j, x.1, x.2) (u.map some ++ z)
      = (∑ p : P, ∑ p' : P, c i j p p' * mStr N u p p') * V j := by
    intro j
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [tailVal_block m bta N c hz u j r q, mul_assoc]
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  exact Finset.sum_congr rfl (fun j _ => by rw [hc u i j])

include hc in
/-- The key induction: the contraction of the new representation computes the
tail value of the original representation on the map lifting. -/
lemma contract_eq : ∀ (n : ℕ) (w : List (Option A₀)), w.length ≤ n → ∀ i : Q,
    contract m bta N c w i = tailVal m bta i (mapLift g w) := by
  classical
  have hnosep : ∀ (u : List A₀) (V : Q → S) (z : List (Option A₀)) (z' : List (Option A₀)),
      BlockVal m bta N c V z → (∀ j : Q, V j = tailVal m bta j z') → ∀ i : Q,
      contract m bta N c (u.map some ++ z) i
        = tailVal m bta i ((g u).map some ++ z') := by
    intro u V z z' hz hV i
    rw [contract_block m bta N c hc hz u i, tailVal_append, ← mStr_map_some]
    exact Finset.sum_congr rfl (fun j _ => by rw [hV j])
  intro n
  induction n with
  | zero =>
      intro w hw i
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw)
      subst hw0
      have h := hnosep [] bta [] [] (blockVal_nil m bta N c) (fun j => (tailVal_nil m bta j).symm) i
      rw [List.append_nil] at h
      have h0 : mapLift g ([] : List (Option A₀)) = (g []).map some := by
        have := mapLift_map_some g ([] : List A₀)
        simpa using this
      rw [h0]
      simpa using h
  | succ n ih =>
      intro w hw i
      rcases option_list_split w with ⟨u, rfl⟩ | ⟨u, v, rfl⟩
      · have h := hnosep u bta [] [] (blockVal_nil m bta N c)
          (fun j => (tailVal_nil m bta j).symm) i
        rw [List.append_nil, List.append_nil] at h
        rw [mapLift_map_some]
        exact h
      · -- the value at the separator
        have hlen : v.length ≤ n := by
          simp only [List.length_append, List.length_map, List.length_cons] at hw
          omega
        set V : Q → S := fun j => tailVal m bta j (none :: mapLift g v) with hVdef
        have hz : BlockVal m bta N c V (none :: v) := by
          intro j r q
          rw [tailVal_cons]
          by_cases hrq : r = q
          · subst hrq
            simp only [hVdef]
            rw [tailVal_cons]
            have hb : ∀ t' : Q × P × P, (bmat m N c) none (j, r, r) t'
                = ∑ j2 : Q, m none j j2 * c j2 t'.1 t'.2.1 t'.2.2 := by
              intro t'
              simp [bmat]
            calc ∑ t' : Q × P × P, (bmat m N c) none (j, r, r) t' *
                    tailVal (bmat m N c) (bbta bta) t' v
                = ∑ t' : Q × P × P, ∑ j2 : Q, m none j j2 *
                    (c j2 t'.1 t'.2.1 t'.2.2 * tailVal (bmat m N c) (bbta bta) t' v) := by
                  refine Finset.sum_congr rfl (fun t' _ => ?_)
                  rw [hb t', Finset.sum_mul]
                  exact Finset.sum_congr rfl (fun j2 _ => by rw [mul_assoc])
              _ = ∑ j2 : Q, m none j j2 * contract m bta N c v j2 := by
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl (fun j2 _ => ?_)
                  rw [contract, Finset.mul_sum]
              _ = ∑ j2 : Q, m none j j2 * tailVal m bta j2 (mapLift g v) := by
                  exact Finset.sum_congr rfl
                    (fun j2 _ => by rw [ih v hlen j2])
          · have hb : ∀ t' : Q × P × P, (bmat m N c) none (j, r, q) t' = 0 := by
              intro t'
              simp [bmat, hrq]
            simp [hb, hrq]
        have h := hnosep u V (none :: v) (none :: mapLift g v) hz (fun j => rfl) i
        rw [h, mapLift_map_some_cons_none]

include hc in
/-- The new linear representation computes the composition with the map
lifting. -/
lemma lval_bmat (alpha : Q → S) (w : List (Option A₀)) :
    lval (balpha c alpha) (bmat m N c) (bbta bta) w = lval alpha m bta (mapLift g w) := by
  classical
  have hcontract : ∀ i : Q, contract m bta N c w i = tailVal m bta i (mapLift g w) :=
    contract_eq m bta N c hc w.length w le_rfl
  calc lval (balpha c alpha) (bmat m N c) (bbta bta) w
      = ∑ t : Q × P × P, (∑ i : Q, alpha i * c i t.1 t.2.1 t.2.2) *
          tailVal (bmat m N c) (bbta bta) t w := rfl
    _ = ∑ t : Q × P × P, ∑ i : Q,
          alpha i * (c i t.1 t.2.1 t.2.2 * tailVal (bmat m N c) (bbta bta) t w) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_assoc])
    _ = ∑ i : Q, ∑ t : Q × P × P,
          alpha i * (c i t.1 t.2.1 t.2.2 * tailVal (bmat m N c) (bbta bta) t w) :=
        Finset.sum_comm
    _ = ∑ i : Q, alpha i * contract m bta N c w i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [contract, Finset.mul_sum]
    _ = lval alpha m bta (mapLift g w) := by
        rw [lval]
        exact Finset.sum_congr rfl (fun i _ => by rw [hcontract i])

end Construction

/-! ## Closure of weighted automata under the map lifting -/

/-- Weighted automata are closed under pre-composition with the map lifting of a
matrix-linear block function. -/
theorem isWeighted_comp_mapLift {A₀ S : Type} [Finite A₀] [CommSemiring S]
    {g : List A₀ → List A₀} (hg : MatLin S g) {h : List (Option A₀) → S}
    (hh : IsWeighted h) : IsWeighted (fun w => h (mapLift g w)) := by
  classical
  obtain ⟨Q, hQ, hdec, alpha, m, bta, hm⟩ := WLin.exists_lval hh
  obtain ⟨P, hP, hdecP, N, c, hc⟩ := hg Q hQ hdec (fun a => m (some a))
  have heq : (fun w : List (Option A₀) => h (mapLift g w))
      = lval (balpha c alpha) (bmat m N c) (bbta bta) := by
    funext w
    rw [lval_bmat m bta N c hc alpha w, hm]
  rw [heq]
  exact WLin.isWeighted_lval _ _ _

/-! ## The two prime block functions -/

/-- Reversal of a block is matrix-linear: the auxiliary representation consists
of the transposed matrices (this is where commutativity of the semiring is
used). -/
theorem matLin_reverse {A₀ S : Type} [CommSemiring S] :
    MatLin S (List.reverse : List A₀ → List A₀) := by
  classical
  intro Q hQ hdec m
  refine ⟨Q, hQ, hdec, fun a => (m a)ᵀ, fun i j p p' => if p = j ∧ p' = i then 1 else 0, ?_⟩
  intro v i j
  have hT : mStr (fun a => (m a)ᵀ) v = (mStr m v.reverse)ᵀ := mStr_transpose m v
  have : ∑ p : Q, ∑ p' : Q, (if p = j ∧ p' = i then (1 : S) else 0) *
      mStr (fun a => (m a)ᵀ) v p p' = mStr (fun a => (m a)ᵀ) v j i := by
    simp [ite_and, Finset.sum_ite_eq']
  rw [this, hT]
  rfl

/-- Duplication of a block is matrix-linear: the auxiliary representation
consists of the Kronecker squares of the matrices, so that the weight of a
transition is a product of the weights of two transitions of the original
automaton. -/
theorem matLin_dup {A₀ S : Type} [CommSemiring S] :
    MatLin S (fun v : List A₀ => v ++ v) := by
  classical
  intro Q hQ hdec m
  refine ⟨Q × Q, inferInstance, inferInstance, fun a => (m a) ⊗ₖ (m a),
    fun i j p p' => if p.1 = i ∧ p.2 = p'.1 ∧ p'.2 = j then 1 else 0, ?_⟩
  intro v i j
  have hK : mStr (fun a => (m a) ⊗ₖ (m a)) v = (mStr m v) ⊗ₖ (mStr m v) :=
    mStr_kron m m v
  rw [mStr_append, Matrix.mul_apply]
  simp only [hK, Fintype.sum_prod_type, Matrix.kronecker_apply, ite_and, ite_mul, one_mul,
    zero_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

end WMap

end Lax916827Proofs.Transducers
