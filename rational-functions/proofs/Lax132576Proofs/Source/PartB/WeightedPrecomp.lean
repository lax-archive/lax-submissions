/- Lemma `lem:closure-weighted-automata-precomposition`: weighted automata are closed under
pre-composition with rational functions.

Let `f : A* → B*` be a rational function and `h : B* → S` a function computed by
a weighted automaton.  By Theorem `thm:bimachines` the function `f` is computed by a
bimachine, and by `WNF.exists_linRep` the function `h` has a linear
representation: matrices `m b` for the letters `b` and a final vector `bta`,
such that `h v` is the sum over the initial states of `m v₁ ⋯ m v_k *ᵥ bta`.

The weighted automaton for `h ∘ f` reads the input from left to right in a state
`(l, r, q)` consisting of the state `l` of the prefix automaton at the current
gap, the *guessed* state `r` of the suffix automaton at that gap, and a state
`q` of the weighted automaton.  The transition reading the letter `a` carries the
weight of the matrix of the output block produced at the previous gap.  Since
the guessed states are determined by the input, the accepting runs of the
product are in bijection with the pairs consisting of the (unique) run of the
bimachine and a sequence of states of the weighted automaton, so summing the
weights gives exactly `h (f w)`.
-/
import Lax132576Proofs.Source.PartB.WeightedLinRep
import Lax132576Proofs.Source.PartB.RatBimach
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace WPre

open LabAut WNF

variable {A B P R Q S : Type} [Semiring S] [Fintype Q] [DecidableEq Q]

/-- The matrix of a string in a linear representation. -/
noncomputable def mStr (m : B → Matrix Q Q S) (v : List B) : Matrix Q Q S := (v.map m).prod

@[simp] lemma mStr_nil (m : B → Matrix Q Q S) : mStr m ([] : List B) = 1 := rfl

lemma mStr_append (m : B → Matrix Q Q S) (v w : List B) :
    mStr m (v ++ w) = mStr m v * mStr m w := by
  simp [mStr, List.prod_append]

/-- The value contributed by a state `q` of the weighted automaton and the
remaining output `v`. -/
noncomputable def tailVal (m : B → Matrix Q Q S) (bta : Q → S) (q : Q) (v : List B) : S :=
  ∑ q' : Q, mStr m v q q' * bta q'

/-- The value of the linear representation on a string. -/
noncomputable def val (m : B → Matrix Q Q S) (I : Finset Q) (bta : Q → S) (v : List B) : S :=
  ∑ q ∈ I, tailVal m bta q v

lemma tailVal_append (m : B → Matrix Q Q S) (bta : Q → S) (q : Q) (x y : List B) :
    tailVal m bta q (x ++ y) = ∑ q' : Q, mStr m x q q' * tailVal m bta q' y := by
  simp only [tailVal, mStr_append, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

variable (bm : Bimachine A B P R)

/-- The state of the suffix automaton at the gap in front of `w`. -/
def sufSt (w : List A) : R := strTrans bm.suffixStep w.reverse bm.suffixInit

@[simp] lemma sufSt_nil : sufSt bm [] = bm.suffixInit := rfl

lemma sufSt_cons (a : A) (w : List A) : sufSt bm (a :: w) = bm.suffixStep (sufSt bm w) a := by
  simp [sufSt, strTrans]

/-- The states of the product automaton. -/
abbrev WSt (P R Q : Type) : Type := Bool ⊕ (P × R × Q)

/-- The initial state of the product automaton. -/
def wstart : WSt P R Q := Sum.inl false

/-- The final state of the product automaton. -/
def wstop : WSt P R Q := Sum.inl true

/-- A state of the product automaton at a gap. -/
def wmid (l : P) (r : R) (q : Q) : WSt P R Q := Sum.inr (l, r, q)

variable [Finite A] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
variable (m : B → Matrix Q Q S) (I : Finset Q) (bta : Q → S)

/-- The weighted automaton computing `h ∘ f`. -/
def W : LabAut A S (WSt P R Q) where
  init := {wstart}
  final := {wstop}
  δ := {tr | tr = (wstart, [], val m I bta (bm.eval []), wstop) ∨
    (∃ (a : A) (r' : R) (q' : Q), tr = (wstart, [a],
        ∑ q₀ ∈ I, mStr m (bm.out bm.prefixInit (bm.suffixStep r' a)) q₀ q',
        wmid (bm.prefixStep bm.prefixInit a) r' q')) ∨
    (∃ (l : P) (q : Q) (a : A) (r' : R) (q' : Q),
        tr = (wmid l (bm.suffixStep r' a) q, [a],
          mStr m (bm.out l (bm.suffixStep r' a)) q q',
          wmid (bm.prefixStep l a) r' q')) ∨
    (∃ (l : P) (q : Q), tr = (wmid l bm.suffixInit q, [],
        tailVal m bta q (bm.out l bm.suffixInit), wstop))}
  δ_finite := by
    have h1 : ({(wstart, [], val m I bta (bm.eval []), wstop)} :
      Set (WSt P R Q × List A × S × WSt P R Q)).Finite := Set.finite_singleton _
    have h2 : (Set.range (fun x : A × R × Q => ((wstart : WSt P R Q), [x.1],
        ∑ q₀ ∈ I, mStr m (bm.out bm.prefixInit (bm.suffixStep x.2.1 x.1)) q₀ x.2.2,
        wmid (bm.prefixStep bm.prefixInit x.1) x.2.1 x.2.2))).Finite := Set.finite_range _
    have h3 : (Set.range (fun x : P × Q × A × R × Q =>
        ((wmid x.1 (bm.suffixStep x.2.2.2.1 x.2.2.1) x.2.1 : WSt P R Q), [x.2.2.1],
          mStr m (bm.out x.1 (bm.suffixStep x.2.2.2.1 x.2.2.1)) x.2.1 x.2.2.2.2,
          wmid (bm.prefixStep x.1 x.2.2.1) x.2.2.2.1 x.2.2.2.2))).Finite := Set.finite_range _
    have h4 : (Set.range (fun x : P × Q =>
        (((wmid x.1 bm.suffixInit x.2 : WSt P R Q), ([] : List A),
          tailVal m bta x.2 (bm.out x.1 bm.suffixInit), (wstop : WSt P R Q)) :
          WSt P R Q × List A × S × WSt P R Q))).Finite := Set.finite_range _
    refine (((h1.union h2).union h3).union h4).subset ?_
    rintro tr (rfl | ⟨a, r', q', rfl⟩ | ⟨l, q, a, r', q', rfl⟩ | ⟨l, q, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inl (Or.inl (Or.inr ⟨(a, r', q'), rfl⟩))
    · exact Or.inl (Or.inr ⟨(l, q, a, r', q'), rfl⟩)
    · exact Or.inr ⟨(l, q), rfl⟩

omit [Fintype Q] [DecidableEq Q] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
lemma wstart_ne_wstop : (wstart : WSt P R Q) ≠ wstop := by simp [wstart, wstop]

omit [DecidableEq P] [DecidableEq R] in
lemma W_atomic : Atomic (W bm m I bta) := by
  rintro tr (rfl | ⟨a, r', q', rfl⟩ | ⟨l, q, a, r', q', rfl⟩ | ⟨l, q, rfl⟩) <;> simp

omit [DecidableEq P] [DecidableEq R] in
lemma W_no_out_wstop : ∀ tr ∈ (W bm m I bta).δ, tr.1 ≠ wstop := by
  rintro tr (rfl | ⟨a, r', q', rfl⟩ | ⟨l, q, a, r', q', rfl⟩ | ⟨l, q, rfl⟩)
  · exact wstart_ne_wstop
  · exact wstart_ne_wstop
  · simp [wmid, wstop]
  · simp [wmid, wstop]

omit [DecidableEq P] [DecidableEq R] in
lemma W_path_from_wstop {σ : List (WSt P R Q × List A × S × WSt P R Q)} {y : WSt P R Q}
    (h : (W bm m I bta).Path wstop σ y) : σ = [] := by
  cases σ with
  | nil => rfl
  | cons t σ' =>
      rw [path_cons_iff] at h
      exact absurd h.1 (fun hh => W_no_out_wstop bm m I bta t h.2.1 hh)

omit [DecidableEq P] [DecidableEq R] in
lemma W_eps_target {tr : WSt P R Q × List A × S × WSt P R Q} (htr : tr ∈ (W bm m I bta).δ)
    (h : tr.2.1 = []) : tr.2.2.2 = wstop := by
  rcases htr with rfl | ⟨a, r', q', rfl⟩ | ⟨l, q, a, r', q', rfl⟩ | ⟨l, q, rfl⟩
  · rfl
  · simp at h
  · simp at h
  · rfl

omit [DecidableEq P] [DecidableEq R] in
lemma W_path_length {x y : WSt P R Q} {σ : List (WSt P R Q × List A × S × WSt P R Q)}
    (h : (W bm m I bta).Path x σ y) : σ.length ≤ (inputOf σ).length + 1 := by
  induction h with
  | nil q => simp
  | @cons q u l q' σ p ht hpath ih =>
      rcases hu : u with _ | ⟨a, rest⟩
      · have : q' = wstop := W_eps_target bm m I bta (tr := (q, u, l, q')) ht (by simp [hu])
        subst this
        rw [W_path_from_wstop bm m I bta hpath]
        simp
      · have hrest : rest = [] := by
          have := W_atomic bm m I bta (q, u, l, q') ht
          simp only [hu] at this
          simpa using List.length_eq_zero_iff.mp (by simpa using this)
        subst hrest
        simp only [List.length_cons, inputOf_cons, List.length_append]
        omega

omit [DecidableEq P] [DecidableEq R] in
lemma W_pathsFinite : PathsFinite (W bm m I bta) := by
  intro q p x
  refine (bounded_paths_finite (W bm m I bta) (x.length + 1)).subset ?_
  rintro σ ⟨hpath, hin⟩
  exact ⟨path_mem hpath, by have := W_path_length bm m I bta hpath; rw [hin] at this; exact this⟩

omit [DecidableEq P] [DecidableEq R] in
lemma W_uniqueEmptyRun : UniqueEmptyRun (W bm m I bta) := by
  intro x hx y hy _ _
  rw [show x = wstart from hx, show y = wstart from hy]

omit [DecidableEq P] [DecidableEq R] in
lemma W_finitelyManyRuns : (W bm m I bta).FinitelyManyRuns := by
  intro w
  refine (W_pathsFinite bm m I bta wstart wstop w).subset ?_
  rintro σ ⟨⟨x, hx, y, hy, hpath⟩, hin⟩
  rw [show x = wstart from hx] at hpath
  rw [show y = wstop from hy] at hpath
  exact ⟨hpath, hin⟩

/-! ### The transitions leaving a state -/

/-- The weight of the transition from `x` to `x'` reading the letter `a`, when
such a transition exists. -/
noncomputable def wt (x : WSt P R Q) (a : A) (x' : WSt P R Q) : S :=
  match x', x with
  | Sum.inr (_, r', q'), Sum.inl _ =>
      ∑ q₀ ∈ I, mStr m (bm.out bm.prefixInit (bm.suffixStep r' a)) q₀ q'
  | Sum.inr (_, _, q'), Sum.inr (l, r, q) => mStr m (bm.out l r) q q'
  | _, _ => 0

omit [DecidableEq P] [DecidableEq R] in
/-- The weight of a transition is determined by its source, letter and target. -/
lemma W_weight_eq {x x' : WSt P R Q} {a : A} {s : S}
    (h : ((x, [a], s, x') : WSt P R Q × List A × S × WSt P R Q) ∈ (W bm m I bta).δ) :
    s = wt bm m I x a x' := by
  rcases h with heq | ⟨a₁, r₁, q₁, heq⟩ | ⟨l₁, p₁, a₁, r₁, q₁, heq⟩ | ⟨l₁, q₁, heq⟩
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.2.1 (by simp)
  · simp only [Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨hx, ⟨ha, -⟩, hs, hx'⟩ := heq
    subst ha; subst hx; subst hx'; subst hs
    rfl
  · simp only [Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨hx, ⟨ha, -⟩, hs, hx'⟩ := heq
    subst ha; subst hx; subst hx'; subst hs
    rfl
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.2.1 (by simp)

omit [DecidableEq P] [DecidableEq R] in
lemma rcSet_singleton_of_mem {x x' : WSt P R Q} {a : A} {s : S}
    (ht : ((x, [a], s, x') : WSt P R Q × List A × S × WSt P R Q) ∈ (W bm m I bta).δ) :
    rcSet (W bm m I bta) x a x' = {[(x, [a], s, x')]} := by
  apply Set.Subset.antisymm
  · rintro σ ⟨hpath, hin, hrc⟩
    cases σ with
    | nil => simp [inputOf] at hin
    | cons t σ' =>
        rw [path_cons_iff] at hpath
        obtain ⟨hsrc, hmem, htail⟩ := hpath
        have hσ' : σ' = [] := by
          by_contra hne
          have htd : t ∈ (t :: σ').dropLast := by
            rw [List.dropLast_cons_of_ne_nil hne]
            exact List.mem_cons_self
          have h0 : t.2.1 = [] := hrc t htd
          have : t.2.2.2 = wstop := W_eps_target bm m I bta hmem h0
          rw [this] at htail
          exact hne (W_path_from_wstop bm m I bta htail)
        subst hσ'
        rw [path_nil_iff] at htail
        rw [inputOf_cons] at hin
        simp only [inputOf_nil, List.append_nil] at hin
        have hteq : t = (x, [a], t.2.2.1, x') :=
          Prod.ext hsrc (Prod.ext hin (Prod.ext rfl htail))
        have hw : t.2.2.1 = s := by
          rw [hteq] at hmem
          rw [W_weight_eq bm m I bta hmem, ← W_weight_eq bm m I bta ht]
        rw [hteq, hw]
        simp
  · rintro σ rfl
    refine ⟨LabAut.Path.cons ht (LabAut.Path.nil x'), ?_, ?_⟩
    · rw [inputOf_cons]
      rfl
    · intro t ht'
      simp at ht'

omit [DecidableEq P] [DecidableEq R] in
lemma rcSet_empty_of_not_mem {x x' : WSt P R Q} {a : A}
    (ht : ∀ s : S, ((x, [a], s, x') : WSt P R Q × List A × S × WSt P R Q) ∉ (W bm m I bta).δ) :
    rcSet (W bm m I bta) x a x' = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro σ ⟨hpath, hin, hrc⟩
  cases σ with
  | nil => simp [inputOf] at hin
  | cons t σ' =>
      rw [path_cons_iff] at hpath
      obtain ⟨hsrc, hmem, htail⟩ := hpath
      have hσ' : σ' = [] := by
        by_contra hne
        have htd : t ∈ (t :: σ').dropLast := by
          rw [List.dropLast_cons_of_ne_nil hne]
          exact List.mem_cons_self
        have h0 : t.2.1 = [] := hrc t htd
        have : t.2.2.2 = wstop := W_eps_target bm m I bta hmem h0
        rw [this] at htail
        exact hne (W_path_from_wstop bm m I bta htail)
      subst hσ'
      rw [path_nil_iff] at htail
      rw [inputOf_cons] at hin
      simp only [inputOf_nil, List.append_nil] at hin
      have : t = (x, [a], t.2.2.1, x') := Prod.ext hsrc (Prod.ext hin (Prod.ext rfl htail))
      rw [this] at hmem
      exact ht t.2.2.1 hmem

omit [DecidableEq P] [DecidableEq R] in
lemma mu_of_mem {x x' : WSt P R Q} {a : A} {s : S}
    (ht : ((x, [a], s, x') : WSt P R Q × List A × S × WSt P R Q) ∈ (W bm m I bta).δ) :
    mu (W bm m I bta) a x x' = s := by
  rw [mu, Matrix.of_apply, rcSet_singleton_of_mem bm m I bta ht, finsum_mem_singleton]
  simp [weightOf, labelsOf]

omit [DecidableEq P] [DecidableEq R] in
lemma mu_of_not_mem {x x' : WSt P R Q} {a : A}
    (ht : ∀ s : S, ((x, [a], s, x') : WSt P R Q × List A × S × WSt P R Q) ∉ (W bm m I bta).δ) :
    mu (W bm m I bta) a x x' = 0 := by
  rw [mu, Matrix.of_apply, rcSet_empty_of_not_mem bm m I bta ht]
  simp

/-! ### The transitions with empty input -/

omit [DecidableEq P] [DecidableEq R] in
lemma eps_from_mid {l : P} {r : R} {q : Q} {s : S} {x' : WSt P R Q}
    (h : ((wmid l r q, [], s, x') : WSt P R Q × List A × S × WSt P R Q) ∈ (W bm m I bta).δ) :
    r = bm.suffixInit ∧ s = tailVal m bta q (bm.out l bm.suffixInit) ∧ x' = wstop := by
  rcases h with heq | ⟨a₁, r₁, q₁, heq⟩ | ⟨l₁, q₁, a₁, r₁, q₁', heq⟩ | ⟨l₁, q₁, heq⟩
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.1 (by simp [wmid, wstart])
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.2.1 (by simp)
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.2.1 (by simp)
  · simp only [Prod.mk.injEq, wmid, Sum.inr.injEq] at heq
    obtain ⟨⟨hl, hr, hq⟩, -, hs, hx'⟩ := heq
    subst hl; subst hr; subst hq
    exact ⟨rfl, hs, hx'⟩

omit [DecidableEq P] [DecidableEq R] in
lemma eps_from_start {s : S} {x' : WSt P R Q}
    (h : ((wstart, [], s, x') : WSt P R Q × List A × S × WSt P R Q) ∈ (W bm m I bta).δ) :
    s = val m I bta (bm.eval []) ∧ x' = wstop := by
  rcases h with heq | ⟨a₁, r₁, q₁, heq⟩ | ⟨l₁, q₁, a₁, r₁, q₁', heq⟩ | ⟨l₁, q₁, heq⟩
  · simp only [Prod.mk.injEq] at heq
    exact ⟨heq.2.2.1, heq.2.2.2⟩
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.2.1 (by simp)
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.2.1 (by simp)
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.1 (by simp [wmid, wstart])

omit [Semiring S] [Fintype Q] [DecidableEq Q] [Finite A] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
/-- Every transition of a path with empty input reads nothing. -/
lemma eps_of_inputOf_nil {σ : List (WSt P R Q × List A × S × WSt P R Q)}
    (h : inputOf σ = []) : ∀ t ∈ σ, t.2.1 = [] := by
  intro t ht
  simp only [inputOf, List.flatten_eq_nil_iff, List.mem_map] at h
  exact h t.2.1 ⟨t, ht, rfl⟩

omit [DecidableEq P] in
lemma accWeight_mid_nil (l : P) (r : R) (q : Q) :
    accWeight (W bm m I bta) (wmid l r q) [] =
      if r = bm.suffixInit then tailVal m bta q (bm.out l bm.suffixInit) else 0 := by
  by_cases hr : r = bm.suffixInit
  · subst hr
    rw [if_pos rfl]
    have hset : accFrom (W bm m I bta) (wmid l bm.suffixInit q) [] =
        {[(wmid l bm.suffixInit q, [], tailVal m bta q (bm.out l bm.suffixInit), wstop)]} := by
      apply Set.Subset.antisymm
      · rintro σ ⟨⟨p, hp, hpath⟩, hin⟩
        have hpstop : p = wstop := hp
        subst hpstop
        cases σ with
        | nil =>
            rw [path_nil_iff] at hpath
            exact absurd hpath (by simp [wmid, wstop])
        | cons t σ' =>
            rw [path_cons_iff] at hpath
            obtain ⟨hsrc, hmem, htail⟩ := hpath
            have h0 : t.2.1 = [] := eps_of_inputOf_nil hin t (by simp)
            have hteq : t = (wmid l bm.suffixInit q, [], t.2.2.1, t.2.2.2) :=
              Prod.ext hsrc (Prod.ext h0 (Prod.ext rfl rfl))
            rw [hteq] at hmem
            obtain ⟨-, hs, hx'⟩ := eps_from_mid bm m I bta hmem
            rw [hx'] at htail
            have : σ' = [] := W_path_from_wstop bm m I bta htail
            subst this
            rw [hteq, hs, hx']
            simp
      · rintro σ rfl
        refine ⟨⟨wstop, rfl, ?_⟩, rfl⟩
        exact LabAut.Path.cons (Or.inr (Or.inr (Or.inr ⟨l, q, rfl⟩))) (LabAut.Path.nil _)
    rw [accWeight, hset, finsum_mem_singleton]
    simp [weightOf, labelsOf]
  · have hset : accFrom (W bm m I bta) (wmid l r q) [] = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro σ ⟨⟨p, hp, hpath⟩, hin⟩
      have hpstop : p = wstop := hp
      subst hpstop
      cases σ with
      | nil =>
          rw [path_nil_iff] at hpath
          exact absurd hpath (by simp [wmid, wstop])
      | cons t σ' =>
          rw [path_cons_iff] at hpath
          obtain ⟨hsrc, hmem, htail⟩ := hpath
          have h0 : t.2.1 = [] := eps_of_inputOf_nil hin t (by simp)
          have hteq : t = (wmid l r q, [], t.2.2.1, t.2.2.2) :=
            Prod.ext hsrc (Prod.ext h0 (Prod.ext rfl rfl))
          rw [hteq] at hmem
          exact hr (eps_from_mid bm m I bta hmem).1
    rw [accWeight, hset, if_neg hr]
    simp

omit [DecidableEq P] [DecidableEq R] in
lemma accWeight_start_nil :
    accWeight (W bm m I bta) wstart [] = val m I bta (bm.eval []) := by
  have hset : accFrom (W bm m I bta) wstart [] =
      {[((wstart : WSt P R Q), [], val m I bta (bm.eval []), wstop)]} := by
    apply Set.Subset.antisymm
    · rintro σ ⟨⟨p, hp, hpath⟩, hin⟩
      have hpstop : p = wstop := hp
      subst hpstop
      cases σ with
      | nil =>
          rw [path_nil_iff] at hpath
          exact absurd hpath wstart_ne_wstop
      | cons t σ' =>
          rw [path_cons_iff] at hpath
          obtain ⟨hsrc, hmem, htail⟩ := hpath
          have h0 : t.2.1 = [] := eps_of_inputOf_nil hin t (by simp)
          have hteq : t = (wstart, [], t.2.2.1, t.2.2.2) :=
            Prod.ext hsrc (Prod.ext h0 (Prod.ext rfl rfl))
          rw [hteq] at hmem
          obtain ⟨hs, hx'⟩ := eps_from_start bm m I bta hmem
          rw [hx'] at htail
          have : σ' = [] := W_path_from_wstop bm m I bta htail
          subst this
          rw [hteq, hs, hx']
          simp
    · rintro σ rfl
      exact ⟨⟨wstop, rfl, LabAut.Path.cons (Or.inl rfl) (LabAut.Path.nil _)⟩, rfl⟩
  rw [accWeight, hset, finsum_mem_singleton]
  simp [weightOf, labelsOf]

/-! ### The matrices of the product automaton -/

omit [DecidableEq P] [DecidableEq R] in
lemma mu_to_inl (a : A) (x : WSt P R Q) (b : Bool) :
    mu (W bm m I bta) a x (Sum.inl b) = 0 := by
  refine mu_of_not_mem bm m I bta (fun s hs => ?_)
  rcases hs with heq | ⟨a₁, r₁, q₁, heq⟩ | ⟨l₁, q₁, a₁, r₁, q₁', heq⟩ | ⟨l₁, q₁, heq⟩ <;>
    simp only [Prod.mk.injEq] at heq
  · exact absurd heq.2.1 (by simp)
  · exact absurd heq.2.2.2.symm (by simp [wmid])
  · exact absurd heq.2.2.2.symm (by simp [wmid])
  · exact absurd heq.2.1 (by simp)

lemma mu_mid_mid (a : A) (l : P) (r : R) (q : Q) (l₂ : P) (r' : R) (q' : Q) :
    mu (W bm m I bta) a (wmid l r q) (wmid l₂ r' q') =
      if l₂ = bm.prefixStep l a ∧ r = bm.suffixStep r' a then mStr m (bm.out l r) q q' else 0 := by
  by_cases hc : l₂ = bm.prefixStep l a ∧ r = bm.suffixStep r' a
  · obtain ⟨hl, hr⟩ := hc
    subst hl; subst hr
    rw [if_pos ⟨rfl, rfl⟩]
    exact mu_of_mem bm m I bta (Or.inr (Or.inr (Or.inl ⟨l, q, a, r', q', rfl⟩)))
  · rw [if_neg hc]
    refine mu_of_not_mem bm m I bta (fun s hs => ?_)
    rcases hs with heq | ⟨a₁, r₁, q₁, heq⟩ | ⟨l₁, q₁, a₁, r₁, q₁', heq⟩ | ⟨l₁, q₁, heq⟩ <;>
      simp only [Prod.mk.injEq, wmid, wstart, wstop, Sum.inr.injEq, List.cons.injEq] at heq
    · exact absurd heq.2.1 (by simp)
    · exact absurd heq.1 (by simp)
    · obtain ⟨⟨hl₁, hr₁, hq₁⟩, ⟨ha, -⟩, -, hl₂, hr₂, hq₂⟩ := heq
      subst hl₁; subst hq₁; subst ha; subst hr₂; subst hq₂
      exact hc ⟨hl₂, hr₁⟩
    · exact absurd heq.2.1 (by simp)

omit [DecidableEq R] in
lemma mu_start_mid (a : A) (l₂ : P) (r' : R) (q' : Q) :
    mu (W bm m I bta) a (wstart : WSt P R Q) (wmid l₂ r' q') =
      if l₂ = bm.prefixStep bm.prefixInit a then
        ∑ q₀ ∈ I, mStr m (bm.out bm.prefixInit (bm.suffixStep r' a)) q₀ q' else 0 := by
  by_cases hc : l₂ = bm.prefixStep bm.prefixInit a
  · subst hc
    rw [if_pos rfl]
    exact mu_of_mem bm m I bta (Or.inr (Or.inl ⟨a, r', q', rfl⟩))
  · rw [if_neg hc]
    refine mu_of_not_mem bm m I bta (fun s hs => ?_)
    rcases hs with heq | ⟨a₁, r₁, q₁, heq⟩ | ⟨l₁, q₁, a₁, r₁, q₁', heq⟩ | ⟨l₁, q₁, heq⟩ <;>
      simp only [Prod.mk.injEq, wmid, wstart, wstop, Sum.inr.injEq,
        List.cons.injEq] at heq
    · exact absurd heq.2.1 (by simp)
    · obtain ⟨-, ⟨ha, -⟩, -, hl₂, -⟩ := heq
      subst ha
      exact hc hl₂
    · exact absurd heq.1 (by simp)
    · exact absurd heq.2.1 (by simp)

/-! ### The value of the product automaton -/

omit [Fintype Q] [DecidableEq Q] [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R] in
@[simp] lemma inr_eq_wmid (l : P) (r : R) (q : Q) :
    (Sum.inr (l, r, q) : WSt P R Q) = wmid l r q := rfl

/-- From a state at a gap, the sum of the weights of the accepting runs is the
value of the linear representation on the remaining output, provided the guessed
state of the suffix automaton is the correct one. -/
lemma key : ∀ (w : List A) (l : P) (r : R) (q : Q),
    accWeight (W bm m I bta) (wmid l r q) w
      = if r = sufSt bm w then tailVal m bta q (bm.evalFrom l w) else 0 := by
  intro w
  induction w with
  | nil =>
      intro l r q
      rw [accWeight_mid_nil bm m I bta l r q, sufSt_nil]
      by_cases hr : r = bm.suffixInit
      · rw [if_pos hr, if_pos hr, Bimachine.evalFrom_nil]
      · rw [if_neg hr, if_neg hr]
  | cons a y ih =>
      intro l r q
      rw [accWeight_cons (W bm m I bta) (W_pathsFinite bm m I bta) (W_atomic bm m I bta)
        (wmid l r q) a y, Fintype.sum_sum_type]
      rw [Finset.sum_eq_zero (fun b (_ : b ∈ (Finset.univ : Finset Bool)) => by
        rw [mu_to_inl bm m I bta, zero_mul]), zero_add]
      have hz : ∀ (l₂ : P) (r' : R) (q' : Q),
          mu (W bm m I bta) a (wmid l r q) (wmid l₂ r' q') *
              accWeight (W bm m I bta) (wmid l₂ r' q') y
            = (if l₂ = bm.prefixStep l a ∧ r = bm.suffixStep r' a then
                mStr m (bm.out l r) q q' else 0)
              * (if r' = sufSt bm y then tailVal m bta q' (bm.evalFrom l₂ y) else 0) := by
        intro l₂ r' q'
        rw [mu_mid_mid, ih l₂ r' q']
      simp only [inr_eq_wmid, Fintype.sum_prod_type, hz]
      rw [Finset.sum_eq_single (bm.prefixStep l a) (fun l₂ _ hne => by
        refine Finset.sum_eq_zero (fun r' _ => Finset.sum_eq_zero (fun q' _ => ?_))
        rw [if_neg (fun hh => hne hh.1), zero_mul]) (by simp)]
      rw [Finset.sum_eq_single (sufSt bm y) (fun r' _ hne => by
        refine Finset.sum_eq_zero (fun q' _ => ?_)
        rw [if_neg hne, mul_zero]) (by simp)]
      rw [sufSt_cons]
      have hsuf : strTrans bm.suffixStep (a :: y).reverse bm.suffixInit
          = bm.suffixStep (sufSt bm y) a := by
        rw [← sufSt_cons]
        rfl
      by_cases hr : r = bm.suffixStep (sufSt bm y) a
      · have hRHS : tailVal m bta q (bm.evalFrom l (a :: y))
            = ∑ q' : Q, mStr m (bm.out l r) q q' *
                tailVal m bta q' (bm.evalFrom (bm.prefixStep l a) y) := by
          rw [Bimachine.evalFrom_cons, hsuf, ← hr, tailVal_append]
        rw [if_pos hr, hRHS]
        refine Finset.sum_congr rfl (fun q' _ => ?_)
        rw [if_pos ⟨rfl, hr⟩, if_pos rfl]
      · rw [if_neg hr]
        refine Finset.sum_eq_zero (fun q' _ => ?_)
        rw [if_neg (fun hh => hr hh.2), zero_mul]

/-- The sum of the weights of the accepting runs starting in the initial state is
the value of the linear representation on the output of the bimachine. -/
lemma key_start : ∀ w : List A,
    accWeight (W bm m I bta) wstart w = val m I bta (bm.eval w) := by
  intro w
  cases w with
  | nil => exact accWeight_start_nil bm m I bta
  | cons a y =>
      rw [accWeight_cons (W bm m I bta) (W_pathsFinite bm m I bta) (W_atomic bm m I bta)
        wstart a y, Fintype.sum_sum_type]
      rw [Finset.sum_eq_zero (fun b (_ : b ∈ (Finset.univ : Finset Bool)) => by
        rw [mu_to_inl bm m I bta, zero_mul]), zero_add]
      have hz : ∀ (l₂ : P) (r' : R) (q' : Q),
          mu (W bm m I bta) a wstart (wmid l₂ r' q') *
              accWeight (W bm m I bta) (wmid l₂ r' q') y
            = (if l₂ = bm.prefixStep bm.prefixInit a then
                ∑ q₀ ∈ I, mStr m (bm.out bm.prefixInit (bm.suffixStep r' a)) q₀ q' else 0)
              * (if r' = sufSt bm y then tailVal m bta q' (bm.evalFrom l₂ y) else 0) := by
        intro l₂ r' q'
        rw [mu_start_mid, key bm m I bta y l₂ r' q']
      simp only [inr_eq_wmid, Fintype.sum_prod_type, hz]
      rw [Finset.sum_eq_single (bm.prefixStep bm.prefixInit a) (fun l₂ _ hne => by
        refine Finset.sum_eq_zero (fun r' _ => Finset.sum_eq_zero (fun q' _ => ?_))
        rw [if_neg hne, zero_mul]) (by simp)]
      rw [Finset.sum_eq_single (sufSt bm y) (fun r' _ hne => by
        refine Finset.sum_eq_zero (fun q' _ => ?_)
        rw [if_neg hne, mul_zero]) (by simp)]
      simp only [if_true]
      -- exchange the two sums and use the multiplicativity of the matrices
      have hsuf : strTrans bm.suffixStep (a :: y).reverse bm.suffixInit
          = bm.suffixStep (sufSt bm y) a := by
        rw [← sufSt_cons]
        rfl
      rw [val, Bimachine.eval_eq_evalFrom, Bimachine.evalFrom_cons, hsuf]
      have hterm : ∀ q₀ : Q,
          tailVal m bta q₀ (bm.out bm.prefixInit (bm.suffixStep (sufSt bm y) a) ++
              bm.evalFrom (bm.prefixStep bm.prefixInit a) y)
            = ∑ q' : Q, mStr m (bm.out bm.prefixInit (bm.suffixStep (sufSt bm y) a)) q₀ q' *
                tailVal m bta q' (bm.evalFrom (bm.prefixStep bm.prefixInit a) y) := by
        intro q₀
        exact tailVal_append m bta q₀ _ _
      rw [Finset.sum_congr rfl (fun q₀ _ => hterm q₀), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q' _ => ?_)
      rw [Finset.sum_mul]

/-- The product automaton computes the composition. -/
theorem wEval_W (w : List A) :
    (W bm m I bta).wEval w = val m I bta (bm.eval w) := by
  rw [wEval_eq_finsum_accWeight (W_uniqueEmptyRun bm m I bta) (W_finitelyManyRuns bm m I bta) w]
  have hinit : (W bm m I bta).init = {(wstart : WSt P R Q)} := rfl
  rw [hinit, finsum_mem_singleton]
  exact key_start bm m I bta w

end WPre

/-- **Lemma `lem:closure-weighted-automata-precomposition`.**  Weighted automata are closed under
pre-composition with rational functions. -/
theorem weighted_precomp_rational_aux {A B S : Type} [Finite A] [Finite B] [Semiring S]
    {f : List A → List B} {h : List B → S}
    (hf : IsRationalFun f) (hh : IsWeighted h) : IsWeighted (h ∘ f) := by
  classical
  obtain ⟨P, R, hP, hR, bmach, hbm⟩ := isBimachine_of_rationalFun hf
  obtain ⟨Q, hQ, hdec, I, m, bta, hlin⟩ := WNF.exists_linRep hh
  letI : Fintype P := Fintype.ofFinite P
  letI : Fintype R := Fintype.ofFinite R
  refine ⟨WPre.WSt P R Q, inferInstance, WPre.W bmach m I bta,
    WPre.W_finitelyManyRuns bmach m I bta, ?_⟩
  funext w
  rw [WPre.wEval_W bmach m I bta w]
  have : WPre.val m I bta (bmach.eval w) = h (bmach.eval w) := (hlin (bmach.eval w)).symm
  rw [this, hbm]
  rfl

end Lax132576Proofs.Transducers
