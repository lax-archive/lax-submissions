/-
The state transformation transducer of a pre-automaton and the proof of
Lemma `lem:Mealy-map-lifting` of *Transducers* (M. Bojańczyk, June 25, 2026).

Lemma `lem:Mealy-map-lifting` says that the state transformation transducer of a pre-automaton is
a composition of prime Mealy machines.  The proof is by induction, following the
book, with one deviation that keeps the input alphabet fixed: instead of
removing the letter `a` from the alphabet, we replace its state transformation
by the identity.  The two induction parameters are therefore

* the number of states, and
* the number of letters whose state transformation is not a permutation,

ordered lexicographically.  The induction basis (all letters act as
permutations) is `stateTransTransducer_prime_of_reversible`.

For the induction step we fix a letter `a` whose state transformation is not a
permutation, write `P` for its image (a proper subset of the state space) and
follow the book's tripartite decomposition of the input into the first
`a`-block, the middle part (all further `a`-blocks) and the `a`-free suffix.
The computation is organised as a chain of stages, each of which adds one
component to an *enriched letter*

    (letter, seen, L, prev, fp, mid) : Enr δ a

with the following intended meaning at a position `i` of the input `w`
(`v` denotes the prefix of `w` of length `i`):

* `letter` : the `i`-th letter of the input;
* `seen`   : whether `a` occurs strictly before position `i`;
* `L`      : the state transformation of the maximal `a`-free suffix of `v`
             (this is the book's first stage, computed with the map lifting of Lemma
             `lem:map-lifting-decomposition-mealy` applied to the pre-automaton in which `a` acts as
             the identity);
* `prev`   : the value of `L` at the previous position (a delay machine);
* `fp`     : the value of `prev` at the first `a`-position, if any (this
             determines the state transformation of the first `a`-block, which
             is `prev` followed by `a`);
* `mid`    : the state transformation of the middle part, as a map `P → P`
             (computed by the induction assumption for the smaller state
             space `P`).

The state transformation of `v` is then reconstructed from `L`, `fp` and `mid`
by a letter-to-letter homomorphism.
-/
import Lax765601Proofs.Source.PartA.MapLift

namespace Lax765601Proofs.Transducers

/-! ## The state transformation transducer -/

/-- The state transformation transducer of a pre-automaton `δ : Q × A → Q`
(a dfa without designated initial and accepting states): the Mealy machine whose
`n`-th output letter is the state transformation of the first `n` input
letters. -/
def stateTransTransducer {A Q : Type} (δ : Q → A → Q) : Mealy A (Q → Q) (Q → Q) where
  init := id
  step := fun t y => (fun q => δ (t q) y, fun q => δ (t q) y)

/-- Induction basis of Lemma `lem:Mealy-map-lifting`: if every letter of the pre-automaton acts as
a permutation of the state space, then the state transformation transducer is
itself reversible. -/
lemma stateTransTransducer_reversible {A Q : Type} {δ : Q → A → Q}
    (h : ∀ y : A, Function.Bijective (fun q => δ q y)) :
    (stateTransTransducer δ).Reversible := by
  intro y
  constructor
  · intro t₁ t₂ ht
    funext q
    exact (h y).injective (congrFun ht q)
  · intro t
    choose g hg using fun q => (h y).surjective (t q)
    exact ⟨g, funext hg⟩

/-- Induction basis of Lemma `lem:Mealy-map-lifting`, in the form of a decomposition. -/
lemma stateTransTransducer_prime_of_reversible {A Q : Type} [Finite A] [Finite Q]
    {δ : Q → A → Q} (h : ∀ y : A, Function.Bijective (fun q => δ q y)) :
    CompClosure PrimeMealyFam A (Q → Q) (stateTransTransducer δ).eval :=
  CompClosure.base
    (Or.inl ⟨Q → Q, inferInstance, stateTransTransducer δ, rfl,
      stateTransTransducer_reversible h⟩)

/-- The state of the state transformation transducer after reading `v` from the
state `t`. -/
lemma stateTransTransducer_trans {A Q : Type} (δ : Q → A → Q) (v : List A) (t : Q → Q) :
    (stateTransTransducer δ).trans v t = fun q => strTrans δ v (t q) := by
  simp [Mealy.trans, strTrans]
  funext q
  induction v generalizing t with
  | nil => rfl
  | cons a w ih => 
    simp [ih]
    rfl

/-- The last output letter of the state transformation transducer on a nonempty
input. -/
lemma stateTransTransducer_getLast? {A Q : Type} (δ : Q → A → Q) (t : Q → Q)
    (u : List A) (y : A) :
    ((stateTransTransducer δ).run t (u ++ [y])).getLast?
      = some (fun q => strTrans δ (u ++ [y]) (t q)) := by
  induction u generalizing t with
  | nil =>
    simp [Mealy.run_cons, stateTransTransducer]
    rfl
  | cons a u ih =>
    simp [Mealy.run_cons]
    rw [List.getLast?_cons]
    rw [ih ((stateTransTransducer δ).step t a).1]
    simp [stateTransTransducer, strTrans]

lemma stateTransTransducer_eval_getLast? {A Q : Type} (δ : Q → A → Q) (u : List A) (y : A) :
    ((stateTransTransducer δ).eval (u ++ [y])).getLast? = some (strTrans δ (u ++ [y])) :=
  stateTransTransducer_getLast? δ id u y

/-! ## The induction step of Lemma `lem:Mealy-map-lifting` -/

section Step

variable {A Q : Type} [DecidableEq A] (δ : Q → A → Q) (a : A)

/-- The image of the state transformation of the letter `a`; in the book this is
the proper subset `P ⊂ Q`. -/
abbrev Img : Type := {q : Q // ∃ p, δ p a = q}

/-- The enriched alphabet: the input letter together with the values computed by
the successive stages. -/
abbrev Enr : Type :=
  A × Bool × (Q → Q) × (Q → Q) × Option (Q → Q) × (Img δ a → Img δ a)

/-- The pre-automaton in which the letter `a` acts as the identity.  It has the
same behaviour as `δ` on `a`-free words, and one non-permutation letter less. -/
def deltaFree : Q → A → Q := fun q y => if y = a then q else δ q y

/-- A state transformation is *realisable* if it is the state transformation of
some input word. -/
def Realisable (δ : Q → A → Q) (t : Q → Q) : Prop := ∃ w : List A, t = strTrans δ w

/-- The pre-automaton on the smaller state space `Img δ a`, used for the middle
part of the tripartite decomposition: at an `a`-position which is not the first
one, apply the state transformation of the block that ends there.

Only *realisable* transformations are applied.  This restriction is invisible in
the correctness proof, because the transformations that the earlier stages store
are realisable; its purpose is that every state transformation of this smaller
pre-automaton is then realisable in the original one, so that aperiodicity is
inherited (this is what the book means by "every new machine will only use state
transformations that arise from the original machine"). -/
noncomputable def deltaMid : Img δ a → Enr δ a → Img δ a :=
  open Classical in
  fun p e => if e.1 = a ∧ e.2.1 = true ∧ Realisable δ e.2.2.2.1 then
      ⟨δ (e.2.2.2.1 (p : Q)) a, ⟨e.2.2.2.1 (p : Q), rfl⟩⟩
    else p

/-! ### The individual stages -/

/-- Stage 1: has the letter `a` occurred strictly before the current position? -/
def seenMealy : Mealy (Enr δ a) Bool Bool where
  init := false
  step := fun s e => (s || decide (e.1 = a), s)

/-- Stage 2, as a Mealy machine: the state transformation of the maximal
`a`-free suffix of the current prefix.  This machine is *not* prime; it is only
used as a description of the semantics of `tailFun` below. -/
def tailMealy : Mealy (Enr δ a) (Q → Q) (Q → Q) where
  init := id
  step := fun t e =>
    ((if e.1 = a then id else fun q => δ (t q) e.1),
      (if e.1 = a then id else fun q => δ (t q) e.1))

/-- Stage 2, as a composition of primes: the map lifting (Lemma
`lem:map-lifting-decomposition-mealy`) of the state transformation transducer of `deltaFree`, with
the `a`-positions used as separators. -/
def tailFun : List (Enr δ a) → List (Q → Q) :=
  List.map (fun o : Option (Q → Q) => o.getD id) ∘
    mapLift (stateTransTransducer (deltaFree δ a)).eval ∘
    List.map (fun e : Enr δ a => if e.1 = a then none else some e.1)

/-- Stage 3: the delay machine, which outputs the value of the second stage at
the previous position. -/
def prevMealy : Mealy (Enr δ a) (Q → Q) (Q → Q) where
  init := id
  step := fun t e => (e.2.2.1, t)

/-- Stage 4: store the value of the third stage at the first `a`-position. -/
def firstMealy : Mealy (Enr δ a) (Option (Q → Q)) (Option (Q → Q)) where
  init := none
  step := fun o e =>
    if e.1 = a ∧ e.2.1 = false then (some e.2.2.2.1, some e.2.2.2.1) else (o, o)

/-- The letter-to-letter homomorphism of the last stage: it reconstructs the
state transformation of the current prefix from the three parts of the
tripartite decomposition. -/
def combineEnr : Enr δ a → (Q → Q) :=
  fun e =>
    match e.2.2.2.2.1 with
    | none => e.2.2.1
    | some d => fun q => e.2.2.1 ((e.2.2.2.2.2 ⟨δ (d q) a, ⟨d q, rfl⟩⟩ : Img δ a) : Q)

/-! ### Masks and packing functions -/

/-- The initial enrichment: only the input letter is meaningful. -/
def init0 : A → Enr δ a := fun y => (y, false, id, id, none, id)

def mask0 : Enr δ a → Enr δ a := fun e => (e.1, false, id, id, none, id)
def mask1 : Enr δ a → Enr δ a := fun e => (e.1, e.2.1, id, id, none, id)
def mask2 : Enr δ a → Enr δ a := fun e => (e.1, e.2.1, e.2.2.1, id, none, id)
def mask3 : Enr δ a → Enr δ a := fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1, none, id)
def mask4 : Enr δ a → Enr δ a := fun e => (e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1, id)

def pack1 : Enr δ a × Bool → Enr δ a := fun p => (p.1.1, p.2, id, id, none, id)
def pack2 : Enr δ a × (Q → Q) → Enr δ a := fun p => (p.1.1, p.1.2.1, p.2, id, none, id)
def pack3 : Enr δ a × (Q → Q) → Enr δ a :=
  fun p => (p.1.1, p.1.2.1, p.1.2.2.1, p.2, none, id)
def pack4 : Enr δ a × Option (Q → Q) → Enr δ a :=
  fun p => (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.2, id)
def pack5 : Enr δ a × (Img δ a → Img δ a) → Enr δ a :=
  fun p => (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.2)

/-- The whole chain of stages. -/
noncomputable def krStages : List A → List (Q → Q) :=
  List.map (combineEnr δ a) ∘
    (List.map (pack5 δ a) ∘ zipInput (stateTransTransducer (deltaMid δ a)).eval) ∘
    (List.map (pack4 δ a) ∘ zipInput (firstMealy δ a).eval) ∘
    (List.map (pack3 δ a) ∘ zipInput (prevMealy δ a).eval) ∘
    (List.map (pack2 δ a) ∘ zipInput (tailFun δ a)) ∘
    (List.map (pack1 δ a) ∘ zipInput (seenMealy δ a).eval) ∘
    List.map (init0 δ a)

/-! ### The specification machine

The following Mealy machine computes the intended value of every component of
every enriched letter.  It is of course not prime -- it is only used to state
the correctness of the individual stages. -/

/-- The state of the specification machine: the state transformation of the
maximal `a`-free suffix, whether `a` has been seen, the value stored at the
first `a`-position, and the state transformation of the middle part. -/
abbrev SpecSt : Type := (Q → Q) × Bool × Option (Q → Q) × (Img δ a → Img δ a)

/-- The specification machine. -/
def specMealy : Mealy A (Enr δ a) (SpecSt δ a) where
  init := (id, false, none, id)
  step := fun s y =>
    (((if y = a then id else fun q => δ (s.1 q) y),
        s.2.1 || decide (y = a),
        (if y = a ∧ s.2.1 = false then some s.1 else s.2.2.1),
        (if y = a ∧ s.2.1 = true then
          (fun p : Img δ a => (⟨δ (s.1 (p : Q)) a, ⟨s.1 (p : Q), rfl⟩⟩ : Img δ a)) ∘ s.2.2.2
        else s.2.2.2)),
      (y, s.2.1, (if y = a then id else fun q => δ (s.1 q) y), s.1,
        (if y = a ∧ s.2.1 = false then some s.1 else s.2.2.1),
        (if y = a ∧ s.2.1 = true then
          (fun p : Img δ a => (⟨δ (s.1 (p : Q)) a, ⟨s.1 (p : Q), rfl⟩⟩ : Img δ a)) ∘ s.2.2.2
        else s.2.2.2)))

/-- The state transformation described by a state of the specification
machine. -/
def specVal : SpecSt δ a → (Q → Q) :=
  fun s =>
    match s.2.2.1 with
    | none => s.1
    | some d => fun q => s.1 ((s.2.2.2 ⟨δ (d q) a, ⟨d q, rfl⟩⟩ : Img δ a) : Q)

/-- The invariant of the specification machine: the letter `a` has been seen
exactly when a value has been stored at the first `a`-position, and before that
the middle part is empty. -/
def SpecInv (s : SpecSt δ a) : Prop :=
  (s.2.1 = s.2.2.1.isSome) ∧ (s.2.2.1 = none → s.2.2.2 = id)

/-! ### Correctness of the stages -/

/-- The input letters are copied by the specification machine. -/
lemma specMealy_letters (s : SpecSt δ a) (w : List A) :
    ((specMealy δ a).run s w).map (fun e => e.1) = w := by
  induction w generalizing s with
  | nil => rfl
  | cons y w ih =>
    simp [ih]
    rfl

lemma stage0 (s : SpecSt δ a) (w : List A) :
    w.map (init0 δ a) = ((specMealy δ a).run s w).map (mask0 δ a) := by
  induction w generalizing s with
  | nil => rfl
  | cons y w ih =>
    simp only [Mealy.run_cons, List.map_cons]
    congr 1
    exact ih ((specMealy δ a).step s y).1

lemma stage1_run (s : SpecSt δ a) (w : List A) :
    (seenMealy δ a).run s.2.1 (((specMealy δ a).run s w).map (mask0 δ a))
      = ((specMealy δ a).run s w).map (fun e => e.2.1) := by
  induction w generalizing s with
  | nil => rfl
  | cons y w ih =>
      rw [Mealy.run_cons, List.map_cons, Mealy.run_cons]
      exact congrArg _ (ih ((specMealy δ a).step s y).1)

/-- Correctness of the map lifting stage: the second component is the state
transformation of the maximal `a`-free suffix. -/
lemma stage2_aux (s : SpecSt δ a) (w : List A) (u : List A)
    (hu : s.1 = strTrans (deltaFree δ a) u) :
    (mapLiftAux (stateTransTransducer (deltaFree δ a)).eval u
        ((((specMealy δ a).run s w).map (mask1 δ a)).map
          (fun e : Enr δ a => if e.1 = a then none else some e.1))).map
        (fun o : Option (Q → Q) => o.getD id)
      = ((specMealy δ a).run s w).map (fun e => e.2.2.1) := by
  induction w generalizing s u with
  | nil => rfl
  | cons y w ih =>
      have hhead : (mask1 δ a ((specMealy δ a).step s y).2).1 = y := rfl
      rw [Mealy.run_cons, List.map_cons, List.map_cons, List.map_cons, hhead]
      by_cases h : y = a
      · rw [if_pos h, mapLiftAux, List.map_cons]
        refine congrArg₂ List.cons ?_ (ih _ [] (by simp [specMealy, h]; rfl))
        simp [specMealy, h]
      · rw [if_neg h, mapLiftAux, List.map_cons, stateTransTransducer_eval_getLast?]
        have hstep : strTrans (deltaFree δ a) (u ++ [y]) = fun q => δ (s.1 q) y := by
          funext q
          rw [hu]
          simp [strTrans, deltaFree, h]
        refine congrArg₂ List.cons ?_ (ih _ (u ++ [y]) ?_)
        · simp [hstep, specMealy, h]
        · simp [hstep, specMealy, h]

lemma stage2_run (w : List A) :
    tailFun δ a (((specMealy δ a).eval w).map (mask1 δ a))
      = ((specMealy δ a).eval w).map (fun e => e.2.2.1) := by
  show List.map _ (mapLift _ (List.map _ _)) = _
  rw [mapLift_eq_aux (Mealy.oneStep _)]
  exact stage2_aux δ a _ w [] rfl

lemma stage2_eq (w : List A) :
    List.map (pack2 δ a) (zipInput (tailFun δ a) (((specMealy δ a).eval w).map (mask1 δ a)))
      = ((specMealy δ a).eval w).map (mask2 δ a) := by
  simp only [zipInput]
  rw [stage2_run δ a w, List.zip_map', List.map_map]
  rfl

lemma stage3_run (s : SpecSt δ a) (w : List A) :
    (prevMealy δ a).run s.1 (((specMealy δ a).run s w).map (mask2 δ a))
      = ((specMealy δ a).run s w).map (fun e => e.2.2.2.1) := by
  induction w generalizing s with
  | nil => rfl
  | cons y w ih =>
      rw [Mealy.run_cons, List.map_cons, Mealy.run_cons]
      exact congrArg _ (ih ((specMealy δ a).step s y).1)

lemma stage3_eq (w : List A) :
    List.map (pack3 δ a)
        (zipInput (prevMealy δ a).eval (((specMealy δ a).eval w).map (mask2 δ a)))
      = ((specMealy δ a).eval w).map (mask3 δ a) := by
  simp only [zipInput, Mealy.eval]
  rw [show (prevMealy δ a).init = ((specMealy δ a).init).1 from rfl, stage3_run δ a _ w,
    List.zip_map', List.map_map]
  rfl

lemma stage4_run (s : SpecSt δ a) (w : List A) :
    (firstMealy δ a).run s.2.2.1 (((specMealy δ a).run s w).map (mask3 δ a))
      = ((specMealy δ a).run s w).map (fun e => e.2.2.2.2.1) := by
  induction w generalizing s with
  | nil => rfl
  | cons y w ih =>
      have hstep : (firstMealy δ a).step s.2.2.1 (mask3 δ a ((specMealy δ a).step s y).2)
          = ((((specMealy δ a).step s y).1).2.2.1, (((specMealy δ a).step s y).2).2.2.2.2.1) := by
        by_cases h : y = a ∧ s.2.1 = false <;> simp [firstMealy, specMealy, mask3, h]
      rw [Mealy.run_cons, List.map_cons, Mealy.run_cons, hstep]
      exact congrArg _ (ih ((specMealy δ a).step s y).1)

lemma stage4_eq (w : List A) :
    List.map (pack4 δ a)
        (zipInput (firstMealy δ a).eval (((specMealy δ a).eval w).map (mask3 δ a)))
      = ((specMealy δ a).eval w).map (mask4 δ a) := by
  simp only [zipInput, Mealy.eval]
  rw [show (firstMealy δ a).init = ((specMealy δ a).init).2.2.1 from rfl, stage4_run δ a _ w,
    List.zip_map', List.map_map]
  rfl

/-- The state transformation stored by the specification machine is always
realisable. -/
lemma specMealy_realisable (s : SpecSt δ a) (hs : Realisable δ s.1) (y : A) :
    Realisable δ (((specMealy δ a).step s y).1).1 := by
  obtain ⟨u, hu⟩ := hs
  by_cases h : y = a
  · exact ⟨[], by simp [specMealy, h]; rfl⟩
  · refine ⟨u ++ [y], ?_⟩
    funext q
    simp [specMealy, h, hu, strTrans]

lemma stage5_run (s : SpecSt δ a) (hs : Realisable δ s.1) (w : List A) :
    (stateTransTransducer (deltaMid δ a)).run s.2.2.2
        (((specMealy δ a).run s w).map (mask4 δ a))
      = ((specMealy δ a).run s w).map (fun e => e.2.2.2.2.2) := by
  induction w generalizing s with
  | nil => rfl
  | cons y w ih =>
      have hstep : (stateTransTransducer (deltaMid δ a)).step s.2.2.2
            (mask4 δ a ((specMealy δ a).step s y).2)
          = ((((specMealy δ a).step s y).1).2.2.2, (((specMealy δ a).step s y).2).2.2.2.2.2) := by
        by_cases h : y = a ∧ s.2.1 = true
        · simp [stateTransTransducer, deltaMid, specMealy, mask4, h, hs]
          rfl
        · have hc : ¬(y = a ∧ s.2.1 = true ∧ Realisable δ s.1) := by tauto
          simp [stateTransTransducer, deltaMid, specMealy, mask4, h, hc]
      rw [Mealy.run_cons, List.map_cons, Mealy.run_cons, hstep]
      exact congrArg _ (ih ((specMealy δ a).step s y).1 (specMealy_realisable δ a s hs y))

lemma stage5_eq (w : List A) :
    List.map (pack5 δ a)
        (zipInput (stateTransTransducer (deltaMid δ a)).eval
          (((specMealy δ a).eval w).map (mask4 δ a)))
      = (specMealy δ a).eval w := by
  simp only [zipInput, Mealy.eval]
  rw [show (stateTransTransducer (deltaMid δ a)).init = ((specMealy δ a).init).2.2.2 from rfl,
    stage5_run δ a _ ⟨[], rfl⟩ w, List.zip_map', List.map_map]
  have h : (fun e : Enr δ a => (pack5 δ a) ((mask4 δ a e, e.2.2.2.2.2))) = id := by
    funext e
    rfl
  rw [Function.comp_def, h, List.map_id]

lemma stage1_eq (w : List A) :
    List.map (pack1 δ a)
        (zipInput (seenMealy δ a).eval (((specMealy δ a).eval w).map (mask0 δ a)))
      = ((specMealy δ a).eval w).map (mask1 δ a) := by
  simp only [zipInput, Mealy.eval]
  rw [show (seenMealy δ a).init = ((specMealy δ a).init).2.1 from rfl, stage1_run δ a _ w,
    List.zip_map', List.map_map]
  rfl

/-- The invariant of the specification machine is preserved. -/
lemma specInv_step (s : SpecSt δ a) (hs : SpecInv δ a s) (y : A) :
    SpecInv δ a ((specMealy δ a).step s y).1 := by
  obtain ⟨hseen, hmid⟩ := hs
  by_cases h : y = a
  · subst h
    by_cases h2 : s.2.1 = false
    · refine ⟨by simp [specMealy, h2], ?_⟩
      intro hc
      simp [specMealy, h2] at hc
    · have h3 : s.2.1 = true := by simpa using h2
      have h4 : s.2.2.1.isSome = true := by rw [← hseen, h3]
      refine ⟨by simp [specMealy, h2, ← hseen], ?_⟩
      intro hc
      simp [specMealy, h2] at hc
      simp [hc] at h4
  · exact ⟨by simpa [specMealy, h] using hseen, by simpa [specMealy, h] using hmid⟩

/-- Reading one letter composes the state transformation described by the state
of the specification machine with the state transformation of that letter. -/
lemma specVal_step (s : SpecSt δ a) (hs : SpecInv δ a s) (y : A) :
    specVal δ a ((specMealy δ a).step s y).1 = fun q => δ (specVal δ a s q) y := by
  obtain ⟨hseen, hmid⟩ := hs
  by_cases h : y = a
  · subst h
    by_cases h2 : s.2.1 = false
    · have hfp : s.2.2.1 = none := by
        cases hc : s.2.2.1 with
        | none => rfl
        | some d => rw [hc] at hseen; simp [h2] at hseen
      have hm : s.2.2.2 = id := hmid hfp
      funext q
      simp [specVal, specMealy, h2, hfp, hm]
    · have h3 : s.2.1 = true := by simpa using h2
      cases hc : s.2.2.1 with
      | none => rw [hc] at hseen; simp [h3] at hseen
      | some d =>
        funext q
        simp [specVal, specMealy, h2, hc]
  · funext q
    cases hc : s.2.2.1 with
    | none => simp [specVal, specMealy, h, hc]
    | some d => simp [specVal, specMealy, h, hc]

/-- The output letter of the specification machine describes the state
transformation of the new state. -/
lemma combineEnr_step (s : SpecSt δ a) (y : A) :
    combineEnr δ a ((specMealy δ a).step s y).2 = specVal δ a ((specMealy δ a).step s y).1 := by
  simp [specMealy, combineEnr, specVal]

/-- The last stage: the state transformation of the current prefix is
reconstructed from the three parts of the tripartite decomposition. -/
lemma combine_run (s : SpecSt δ a) (hs : SpecInv δ a s) (w : List A) :
    ((specMealy δ a).run s w).map (combineEnr δ a)
      = (stateTransTransducer δ).run (specVal δ a s) w := by
  induction w generalizing s with
  | nil => rfl
  | cons y w ih =>
      rw [Mealy.run_cons, Mealy.run_cons, List.map_cons, combineEnr_step,
        ih _ (specInv_step δ a s hs y), specVal_step δ a s hs y]
      rfl

/-- **Correctness of the chain of stages.** -/
theorem krStages_eq : krStages δ a = (stateTransTransducer δ).eval := by
  funext w
  have h0 : w.map (init0 δ a) = ((specMealy δ a).eval w).map (mask0 δ a) := stage0 δ a _ w
  show List.map (combineEnr δ a) _ = _
  simp only [Function.comp_apply, h0, stage1_eq, stage2_eq, stage3_eq, stage4_eq, stage5_eq]
  show List.map (combineEnr δ a) ((specMealy δ a).run (specMealy δ a).init w) = _
  rw [combine_run δ a _ ⟨rfl, fun _ => rfl⟩ w]
  rfl

/-! ### The chain of stages is a composition of primes -/

lemma seenMealy_flipFlop : (seenMealy δ a).FlipFlop := by
  intro e
  by_cases h : e.1 = a
  · exact Or.inr ⟨true, fun s => by simp [Mealy.letterTrans, seenMealy, h]⟩
  · exact Or.inl (by funext s; simp [Mealy.letterTrans, seenMealy, h])

omit [DecidableEq A] in
lemma prevMealy_flipFlop : (prevMealy δ a).FlipFlop := by
  intro e
  right
  exact ⟨e.2.2.1, fun t => rfl⟩

lemma firstMealy_flipFlop : (firstMealy δ a).FlipFlop := by
  intro e
  by_cases h : e.1 = a ∧ e.2.1 = false
  · exact Or.inr ⟨some e.2.2.2.1, fun o => by simp [Mealy.letterTrans, firstMealy, h]⟩
  · exact Or.inl (by funext o; simp [Mealy.letterTrans, firstMealy, h])

lemma tailFun_compClosure [Finite A] [Finite Q]
    (hfree : CompClosure PrimeMealyFam A (Q → Q) (stateTransTransducer (deltaFree δ a)).eval) :
    CompClosure PrimeMealyFam (Enr δ a) (Q → Q) (tailFun δ a) := by
  have h1 : CompClosure PrimeMealyFam (Enr δ a) (Option A)
      (List.map (fun e : Enr δ a => if e.1 = a then none else some e.1)) :=
    CompClosure.base (prime_map _)
  have h2 : CompClosure PrimeMealyFam (Option A) (Option (Q → Q))
      (mapLift (stateTransTransducer (deltaFree δ a)).eval) :=
    mapLift_compClosure inferInstance hfree
  have h3 : CompClosure PrimeMealyFam (Option (Q → Q)) (Q → Q)
      (List.map (fun o : Option (Q → Q) => o.getD id)) := CompClosure.base (prime_map _)
  have h4 := CompClosure.comp h1 (CompClosure.comp h2 h3)
  exact h4

/-- The chain of stages is a composition of prime Mealy machines, provided the
two smaller pre-automata satisfy the conclusion of Lemma `lem:Mealy-map-lifting`. -/
theorem krStages_compClosure [Finite A] [Finite Q]
    (hfree : CompClosure PrimeMealyFam A (Q → Q) (stateTransTransducer (deltaFree δ a)).eval)
    (hmid : CompClosure PrimeMealyFam (Enr δ a) (Img δ a → Img δ a)
      (stateTransTransducer (deltaMid δ a)).eval) :
    CompClosure PrimeMealyFam A (Q → Q) (krStages δ a) := by
  have htail := tailFun_compClosure δ a hfree
  have c0 : CompClosure PrimeMealyFam A (Enr δ a) (List.map (init0 δ a)) :=
    CompClosure.base (prime_map _)
  have g1 : CompClosure PrimeMealyFam (Enr δ a) Bool (seenMealy δ a).eval :=
    CompClosure.base (Or.inr ⟨Bool, inferInstance, seenMealy δ a, rfl, seenMealy_flipFlop δ a⟩)
  have g3 : CompClosure PrimeMealyFam (Enr δ a) (Q → Q) (prevMealy δ a).eval :=
    CompClosure.base (Or.inr ⟨Q → Q, inferInstance, prevMealy δ a, rfl, prevMealy_flipFlop δ a⟩)
  have g4 : CompClosure PrimeMealyFam (Enr δ a) (Option (Q → Q)) (firstMealy δ a).eval :=
    CompClosure.base
      (Or.inr ⟨Option (Q → Q), inferInstance, firstMealy δ a, rfl, firstMealy_flipFlop δ a⟩)
  have c1 := CompClosure.comp (compClosure_zipInput inferInstance g1)
    (CompClosure.base (prime_map (pack1 δ a)))
  have c2 := CompClosure.comp (compClosure_zipInput inferInstance htail)
    (CompClosure.base (prime_map (pack2 δ a)))
  have c3 := CompClosure.comp (compClosure_zipInput inferInstance g3)
    (CompClosure.base (prime_map (pack3 δ a)))
  have c4 := CompClosure.comp (compClosure_zipInput inferInstance g4)
    (CompClosure.base (prime_map (pack4 δ a)))
  have c5 := CompClosure.comp (compClosure_zipInput inferInstance hmid)
    (CompClosure.base (prime_map (pack5 δ a)))
  have c6 : CompClosure PrimeMealyFam (Enr δ a) (Q → Q) (List.map (combineEnr δ a)) :=
    CompClosure.base (prime_map _)
  have h := CompClosure.comp c0 (CompClosure.comp c1 (CompClosure.comp c2
    (CompClosure.comp c3 (CompClosure.comp c4 (CompClosure.comp c5 c6)))))
  exact h

end Step

/-! ### The induction -/

/-- The set of letters whose state transformation is not a permutation. -/
def nonBijSet {A Q : Type} (δ : Q → A → Q) : Set A :=
  {y : A | ¬ Function.Bijective (fun q => δ q y)}

lemma nonBijSet_deltaFree_ssubset {A Q : Type} [DecidableEq A] (δ : Q → A → Q) {a : A}
    (ha : ¬ Function.Bijective (fun q => δ q a)) :
    nonBijSet (deltaFree δ a) ⊂ nonBijSet δ := by
  constructor
  · intro y hy
    simp only [nonBijSet, Set.mem_setOf_eq, deltaFree] at hy ⊢
    by_cases h : y = a
    · exact absurd (by simpa [h, Function.id_def] using Function.bijective_id) hy
    · simpa [h] using hy
  · intro hsub
    have h1 : a ∈ nonBijSet (deltaFree δ a) := hsub ha
    simp only [nonBijSet, Set.mem_setOf_eq, deltaFree] at h1
    exact h1 Function.bijective_id

lemma card_img_lt {A Q : Type} [Finite Q] (δ : Q → A → Q) {a : A}
    (ha : ¬ Function.Bijective (fun q => δ q a)) :
    Nat.card (Img δ a) < Nat.card Q := by
  have h2 : ¬ Function.Surjective (fun q => δ q a) := by
    intro hs
    exact ha ⟨(Finite.injective_iff_surjective).2 hs, hs⟩
  have hss : Set.range (fun q => δ q a) ⊂ Set.univ := by
    rw [Set.ssubset_univ_iff]
    simpa [Set.eq_univ_iff_forall, Function.Surjective] using h2
  have h3 := Set.ncard_lt_ncard hss Set.finite_univ
  rw [Set.ncard_univ, ← Nat.card_coe_set_eq] at h3
  exact h3

/-- The double induction of Lemma `lem:Mealy-map-lifting`. -/
theorem stateTrans_aux : ∀ (n : ℕ) (Q : Type) (_ : Finite Q), Nat.card Q ≤ n →
    ∀ (m : ℕ) (A : Type) (_ : Finite A) (δ : Q → A → Q), (nonBijSet δ).ncard ≤ m →
    CompClosure PrimeMealyFam A (Q → Q) (stateTransTransducer δ).eval := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro Q hQ hQn m
    haveI := hQ
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro A hA δ hm
      haveI := hA
      classical
      by_cases hrev : ∀ y : A, Function.Bijective (fun q => δ q y)
      · exact stateTransTransducer_prime_of_reversible hrev
      · push_neg at hrev
        obtain ⟨a, ha⟩ := hrev
        have hfree : CompClosure PrimeMealyFam A (Q → Q)
            (stateTransTransducer (deltaFree δ a)).eval := by
          have hlt : (nonBijSet (deltaFree δ a)).ncard < (nonBijSet δ).ncard :=
            Set.ncard_lt_ncard (nonBijSet_deltaFree_ssubset δ ha) (Set.toFinite _)
          exact ihm _ (lt_of_lt_of_le hlt hm) A hA _ le_rfl
        have hmid : CompClosure PrimeMealyFam (Enr δ a) (Img δ a → Img δ a)
            (stateTransTransducer (deltaMid δ a)).eval :=
          ihn (Nat.card (Img δ a)) (lt_of_lt_of_le (card_img_lt δ ha) hQn) (Img δ a)
            inferInstance le_rfl _ (Enr δ a) inferInstance _ le_rfl
        rw [← krStages_eq δ a]
        exact krStages_compClosure δ a hfree hmid

/-- **Lemma `lem:Mealy-map-lifting`.**  For every pre-automaton, its state transformation
transducer is a composition of prime Mealy machines. -/
theorem stateTransTransducer_prime_decomposition {A Q : Type} [Finite A] [Finite Q]
    (δ : Q → A → Q) :
    CompClosure PrimeMealyFam A (Q → Q) (stateTransTransducer δ).eval :=
  stateTrans_aux (Nat.card Q) Q inferInstance le_rfl ((nonBijSet δ).ncard) A inferInstance δ le_rfl

end Lax765601Proofs.Transducers