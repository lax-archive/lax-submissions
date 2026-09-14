/-
Part A: Mealy machines
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Part A and the statements of all its
theorems, lemmas and claims, together with their proofs.

All the results of Part A are proved.  Lemma `lem:Mealy-map-lifting`, the main ingredient of the
Krohn-Rhodes Theorem `thm:krohn-rhodes`, is proved in
`RequestProject/PartA/StateTrans.lean`, and its aperiodic version, which gives the implication
"aperiodic ⇒ composition of flip-flops" of Theorem `thm:aperiodic-mealy`, is proved in
`RequestProject/PartA/StateTransAperiodic.lean`. -/
import Lax765601Proofs.Source.PartA.MealyBasic
import Lax765601Proofs.Source.Common.Auxiliary
import Lax765601Proofs.Source.PartA.PrimeClosure
import Lax765601Proofs.Source.PartA.MapLift
import Lax765601Proofs.Source.PartA.StateTrans
import Lax765601Proofs.Source.PartA.StateTransAperiodic

namespace Lax765601Proofs.Transducers

/-! ### Equivalence, compositions and continuity -/

/-- Cutting a loop out of an input string.  If two Mealy machines are in the
same pair of states after reading `w.take i` and after reading `w.take j`, and
if they produce the same output on `w.take j`, then any disagreement on `w`
persists on the shorter string `w.take i ++ w.drop j`. -/
lemma mealy_eval_cut {A B Q₁ Q₂ : Type} (M : Mealy A B Q₁) (N : Mealy A B Q₂)
    (w : List A) (i j : ℕ)
    (hM : M.trans (w.take i) M.init = M.trans (w.take j) M.init)
    (hN : N.trans (w.take i) N.init = N.trans (w.take j) N.init)
    (hj : M.eval (w.take j) = N.eval (w.take j))
    (hdiff : M.eval w ≠ N.eval w) :
    M.eval (w.take i ++ w.drop j) ≠ N.eval (w.take i ++ w.drop j) := by
  intro heq
  apply hdiff
  have hw : w = w.take j ++ w.drop j := (List.take_append_drop j w).symm
  rw [hw, Mealy.eval_append, Mealy.eval_append]
  rw [hj]
  have heq' := heq
  rw [Mealy.eval_append, Mealy.eval_append] at heq'
  rcases List.append_eq_append_iff.mp heq' with ⟨a, ha1, ha2⟩ | ⟨bs, hbs1, hbs2⟩
  · have ha_nil : a = [] := by
      have h1 : (N.eval (w.take i)).length = (M.eval (w.take i) ++ a).length := by rw [ha1]
      simp at h1
      exact h1
    simp [ha_nil] at ha1 ha2
    rw [hM] at ha2
    rw [hN] at ha2
    simp [ha2]
  · have hbs_nil : bs = [] := by
      have h1 : (M.eval (w.take i)).length = (N.eval (w.take i) ++ bs).length := by rw [hbs1]
      simp at h1
      exact h1
    simp [hbs_nil] at hbs1 hbs2
    rw [hM] at hbs2
    rw [hN] at hbs2
    simp [hbs2.symm]

/-- Pigeonhole: among the first `m` values of a sequence with values in a
product of two finite types, two coincide as soon as `m` exceeds the number of
pairs. -/
lemma exists_repeat_pair {Q₁ Q₂ : Type} [Fintype Q₁] [Fintype Q₂] (F : ℕ → Q₁ × Q₂) {m : ℕ}
    (hm : Fintype.card Q₁ * Fintype.card Q₂ < m) :
    ∃ i j : ℕ, i < j ∧ j < m ∧ F i = F j := by
  have hcard : Fintype.card (Q₁ × Q₂) = Fintype.card Q₁ * Fintype.card Q₂ := Fintype.card_prod Q₁ Q₂
  have hlt : Fintype.card (Q₁ × Q₂) < Fintype.card (Fin m) := by
    rw [hcard, Fintype.card_fin]
    exact hm
  let G : Fin m → Q₁ × Q₂ := fun i => F i
  have ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt G hlt
  rcases lt_trichotomy i j with hij' | hij' | hij'
  · exact ⟨i, j, hij', j.isLt, heq⟩
  · exact absurd hij' hij
  · exact ⟨j, i, hij', i.isLt, heq.symm⟩

/-- If two Mealy machines disagree on some input string, then they already
disagree on an input string whose length is at most the product of the numbers
of states. -/
lemma mealy_diff_short {A B Q₁ Q₂ : Type} [Fintype Q₁] [Fintype Q₂]
    (M : Mealy A B Q₁) (N : Mealy A B Q₂) (w : List A) (hw : M.eval w ≠ N.eval w) :
    ∃ v : List A, v.length ≤ Fintype.card Q₁ * Fintype.card Q₂ ∧ M.eval v ≠ N.eval v := by
  let m := Fintype.card Q₁ * Fintype.card Q₂
  suffices h : ∀ k, w.length = k → ∃ v, v.length ≤ m ∧ M.eval v ≠ N.eval v by
    exact h w.length rfl
  intro k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    intro hw'
    by_cases hk : k ≤ m
    · exact ⟨w, hw'.symm ▸ hk, hw⟩
    · have hlt : m < k := not_le.mp hk
      have hwlen : w.length = k := hw'
      have ⟨i, j, hij, hj, hstate⟩ :=
        exists_repeat_pair
          (fun i => (M.trans (w.take i) M.init, N.trans (w.take i) N.init)) hlt
      have hMs := congrArg Prod.fst hstate
      have hNs := congrArg Prod.snd hstate
      have hj_len : (w.take j).length < k := by simp [hwlen]; omega
      by_cases hj_agree : M.eval (w.take j) = N.eval (w.take j)
      · have hcut := mealy_eval_cut M N w i j hMs hNs hj_agree hw
        have hshort : (w.take i ++ w.drop j).length < k := by
          rw [List.length_append, List.length_take, List.length_drop, hwlen]
          omega
        exact ih (w.take i ++ w.drop j).length hshort _ hcut
          (by rw [List.length_append, List.length_take, List.length_drop])
      · exact ih (w.take j).length hj_len _ hj_agree rfl

/-- **Theorem `thm:equivalence-decidable-mealy`.**  The equivalence problem for Mealy machines is
decidable.

Decidability is expressed here by its mathematical content: two Mealy machines
are equivalent if and only if they agree on the finitely many input strings
whose length is at most the product of the numbers of states, which is a finite
check. -/
theorem mealy_equiv_iff_bounded {A B Q₁ Q₂ : Type} [Fintype Q₁] [Fintype Q₂]
    (M : Mealy A B Q₁) (N : Mealy A B Q₂) :
    M.eval = N.eval ↔
      ∀ w : List A, w.length ≤ Fintype.card Q₁ * Fintype.card Q₂ → M.eval w = N.eval w := by
  constructor
  · intro h w _
    rw [h]
  · intro h
    funext w
    by_contra hne
    obtain ⟨v, hv, hvne⟩ := mealy_diff_short M N w hne
    exact hvne (h v hv)

/-- **Theorem `thm:composition-mealy`.**  Mealy machines are closed under composition. -/
theorem mealy_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsMealy f) (hg : IsMealy g) : IsMealy (g ∘ f) := by
  obtain ⟨Q, hQ, M, hM⟩ := hf
  obtain ⟨P, hP, N, hN⟩ := hg
  haveI := hQ
  haveI := hP
  exact ⟨Q × P, inferInstance, M.compose N, by rw [Mealy.eval_compose, hM, hN]⟩

/-- **Theorem `thm:continuity-mealy`.**  Mealy machines are continuous. -/
theorem mealy_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsMealy f) : Continuous f := by
  obtain ⟨Q, hQ, M, hM⟩ := hf
  intro L hL
  obtain ⟨σ, hσ, D, hD⟩ := hL
  refine ⟨Q × σ, Fintype.ofFinite _, M.dfaComp D, ?_⟩
  rw [M.dfaComp_accepts, hM, ← hD]

/-! ## The Krohn-Rhodes Decomposition Theorem -/

/-! Theorem `thm:krohn-rhodes`, the Krohn-Rhodes Theorem, is stated and proved below, after
Lemma `lem:Mealy-map-lifting`, on which its proof relies. -/

/-- **Lemma `lem:map-lifting-decomposition-mealy`.**  If a Mealy machine decomposes into prime Mealy
machines, then the same is true for its map lifting.

The construction is carried out in `RequestProject/PartA/MapLift.lean`; finiteness of
the output alphabet, which the book assumes globally, is not needed. -/
theorem mapLift_prime_decomposition {A B : Type} [Finite A]
    {f : List A → List B} (hf : CompClosure PrimeMealyFam A B f) :
    CompClosure PrimeMealyFam (Option A) (Option B) (mapLift f) :=
  mapLift_compClosure inferInstance hf

/-! ### State transformations -/

/-! The state transformation transducer of a pre-automaton, and the proof of
Lemma `lem:Mealy-map-lifting`, are in `RequestProject/PartA/StateTrans.lean`:

* `stateTransTransducer` -- the transducer itself;
* `stateTransTransducer_reversible` and `stateTransTransducer_prime_of_reversible`
  -- the induction basis (a reversible pre-automaton);
* `stateTransTransducer_prime_decomposition` -- **Lemma `lem:Mealy-map-lifting`**, proved by the
  book's induction, whose step uses the map lifting of Lemma `lem:map-lifting-decomposition-mealy`
  and the tripartite decomposition of the input into `a`-blocks. -/

/-- The machine which reconstructs the output of `M` from the input letters
paired with the state transformations of the prefixes of the input: its state is
the state transformation of the previous position, so it is a delay machine, and
in particular a flip-flop machine. -/
def outputMealy {A B Q : Type} (M : Mealy A B Q) : Mealy (A × (Q → Q)) B (Q → Q) where
  init := id
  step := fun t at' => (at'.2, (M.step (t M.init) at'.1).2)

lemma outputMealy_flipFlop {A B Q : Type} (M : Mealy A B Q) : (outputMealy M).FlipFlop :=
  fun at' => Or.inr ⟨at'.2, fun _ => rfl⟩

lemma outputMealy_run {A B Q : Type} (M : Mealy A B Q) (w : List A) (t : Q → Q) :
    (outputMealy M).run t (w.zip ((stateTransTransducer M.transFun).run t w))
      = M.run (t M.init) w := by
  induction w generalizing t with
  | nil => rfl
  | cons a w ih =>
      simpa [outputMealy, stateTransTransducer, Mealy.transFun] using
        ih (fun q => M.transFun (t q) a)

lemma outputMealy_eval {A B Q : Type} (M : Mealy A B Q) :
    (outputMealy M).eval ∘ zipInput (stateTransTransducer M.transFun).eval = M.eval := by
  funext w
  exact outputMealy_run M w id

/-- **Theorem `thm:krohn-rhodes` (Krohn-Rhodes Theorem).**  Every Mealy machine `f` admits a
decomposition `f = f₁ · f₂ ⋯ fₙ` in which every `fᵢ` is either reversible or
flip-flop.

The proof follows the book: the state transformations of the prefixes of the
input are computed by a composition of primes (Lemma `lem:Mealy-map-lifting`), they are paired
with the input letters (`compClosure_zipInput`), and the output of the machine
is then produced by the flip-flop machine `outputMealy`. -/
theorem krohn_rhodes {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsMealy f) : CompClosure PrimeMealyFam A B f := by
  obtain ⟨Q, hQ, M, rfl⟩ := hf
  haveI := hQ
  have h2 : CompClosure PrimeMealyFam A (A × (Q → Q))
      (zipInput (stateTransTransducer M.transFun).eval) :=
    compClosure_zipInput (A := A) inferInstance
      (stateTransTransducer_prime_decomposition M.transFun)
  have h3 : PrimeMealyFam (A × (Q → Q)) B (outputMealy M).eval :=
    Or.inr ⟨Q → Q, inferInstance, outputMealy M, rfl, outputMealy_flipFlop M⟩
  have h4 := CompClosure.comp h2 (CompClosure.base h3)
  rwa [outputMealy_eval] at h4

/-- The flip-flop version of the Krohn-Rhodes Theorem: a Mealy machine whose state transformations
satisfy condition (*) of Lemma `lem:aperiodicity-minimal-machine` is a composition of flip-flop
Mealy machines.  The proof is the one of `krohn_rhodes`, with the decomposition of the state
transformation transducer taken in the class of flip-flop machines
(`stateTransTransducer_flipFlop_decomposition`). -/
theorem krohn_rhodes_flipFlop {A B Q : Type} [Finite A] [Finite Q] (M : Mealy A B Q)
    (hM : M.TransStabilises) : CompClosure FlipFlopFam A B M.eval := by
  have h2 : CompClosure FlipFlopFam A (A × (Q → Q))
      (zipInput (stateTransTransducer M.transFun).eval) :=
    compClosure_zipInput_flipFlop inferInstance
      (stateTransTransducer_flipFlop_decomposition M.transFun hM)
  have h3 : FlipFlopFam (A × (Q → Q)) B (outputMealy M).eval :=
    ⟨Q → Q, inferInstance, outputMealy M, rfl, outputMealy_flipFlop M⟩
  have h4 := CompClosure.comp h2 (CompClosure.base h3)
  rwa [outputMealy_eval] at h4

/-- The product of two reversible Mealy machines is reversible. -/
lemma Mealy.Reversible.compose {A B C Q P : Type} {M : Mealy A B Q} {N : Mealy B C P}
    (hM : M.Reversible) (hN : N.Reversible) : (M.compose N).Reversible := by
  intro a
  have hM_bij := hM a
  refine ⟨?_, ?_⟩
  · intro ⟨q₁, p₁⟩ ⟨q₂, p₂⟩ h_eq
    simp [Mealy.letterTrans_compose] at h_eq
    have hq : q₁ = q₂ := hM_bij.injective h_eq.1
    rw [hq] at h_eq
    exact Prod.ext hq (hN _ |>.injective h_eq.2)
  · intro ⟨q', p'⟩
    obtain ⟨q, hq⟩ := hM_bij.surjective q'
    obtain ⟨p, hp⟩ := (hN ((M.step q a).2)).surjective p'
    exact ⟨(q, p), by simp [Mealy.letterTrans_compose, hq, hp]⟩

/-- **Lemma `lem:reversible-composition`.**  Reversible Mealy machines are closed under composition. -/
theorem reversible_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsReversibleMealy f) (hg : IsReversibleMealy g) : IsReversibleMealy (g ∘ f) := by
  obtain ⟨Q, hQ, M, hM, hMr⟩ := hf
  obtain ⟨P, hP, N, hN, hNr⟩ := hg
  haveI := hQ
  haveI := hP
  exact ⟨Q × P, inferInstance, M.compose N, by rw [Mealy.eval_compose, hM, hN], hMr.compose hNr⟩

/-! ### Aperiodic Mealy machines -/

/-- Condition (3) of Lemma `lemma:derivatives`: the `n`-th output letter depends only on the
first `n` input letters. -/
def PrefixDetermined {A B : Type} (f : List A → List B) : Prop :=
  ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n

/-- The derivative of a string-to-string function: `f⁽ʷ⁾` is the output that `f`
produces *after* having read `w`, that is `f⁽ʷ⁾ (v) = drop |w| (f (w v))`.

This is the definition of the book, which reads "`v ↦ f (w v)` with the first
`|w|` letters of the output removed".  An earlier edition wrote
`f⁽ʷ⁾ (v) = f (w v)`, without removing the part of the output that was produced
while reading `w`, and with that reading Lemma `lemma:derivatives` below would be
false: the identity function on `A*` is computed by a Mealy machine, yet the
functions `v ↦ w v` are pairwise different for different `w`, so there would be
infinitely many derivatives.  Dropping the first `|w|` output letters is also
what the book's proof uses, where the derivative is said to be determined by the
state of the machine after reading `w`. -/
def deriv {A B : Type} (f : List A → List B) (w : List A) : List A → List B :=
  fun v => (f (w ++ v)).drop w.length

/-- Derivatives of a letter-to-letter function are letter-to-letter. -/
lemma deriv_length {A B : Type} {f : List A → List B} (h2 : LengthPreserving f)
    (w v : List A) : (deriv f w v).length = v.length := by
  simp [deriv, h2 (w ++ v)]

/-- Derivatives commute with taking prefixes. -/
lemma deriv_take {A B : Type} {f : List A → List B} (h2 : LengthPreserving f)
    (h3 : PrefixDetermined f) (u v : List A) (n : ℕ) :
    (deriv f u v).take n = deriv f u (v.take n) := by
  show ((f (u ++ v)).drop u.length).take n = (f (u ++ v.take n)).drop u.length
  rw [List.take_drop]
  congr 1
  have hpref : (u ++ v).take (u.length + n) = (u ++ v.take n).take (u.length + n) := by
    simp [List.take_append]
  rw [h3 (u ++ v) (u ++ v.take n) (u.length + n) hpref]
  apply List.take_of_length_le
  rw [h2 (u ++ v.take n)]
  simp

/-- The derivatives of the semantics of a Mealy machine are the runs from the
reachable states. -/
lemma deriv_eval {A B Q : Type} (M : Mealy A B Q) (w : List A) :
    deriv M.eval w = fun v => M.run (M.trans w M.init) v := by
  funext v
  show (M.eval (w ++ v)).drop w.length = _
  rw [Mealy.eval_append]
  simp

/-- Derivatives compose. -/
lemma deriv_append {A B : Type} (f : List A → List B) (u z : List A) :
    deriv f (u ++ z) = fun v => (deriv f u (z ++ v)).drop z.length := by
  funext v
  simp [deriv, List.drop_drop, List.append_assoc]

/-- Derivatives are determined by one-letter extensions: this is what makes the
transition function of the minimal machine well defined. -/
lemma deriv_append_singleton {A B : Type} (f : List A → List B) (w : List A) (a : A) :
    deriv f (w ++ [a]) = fun v => (deriv f w (a :: v)).drop 1 := by
  rw [deriv_append]
  simp

/-- A derivative is determined by the last letters of its values. -/
lemma deriv_ext {A B : Type} {f : List A → List B} (h2 : LengthPreserving f)
    (h3 : PrefixDetermined f) (u u' : List A)
    (h : ∀ v : List A, (deriv f u v).getLast? = (deriv f u' v).getLast?) :
    deriv f u = deriv f u' := by
  funext v
  refine list_eq_of_take_getLast? _ _ (by rw [deriv_length h2, deriv_length h2]) (fun n => ?_)
  rw [deriv_take h2 h3, deriv_take h2 h3]
  exact h (v.take n)

/-- The set of derivatives of a function, as a type. -/
def Derivs {A B : Type} (f : List A → List B) : Type := {g : List A → List B // ∃ w, g = deriv f w}

/-- The set of derivatives, as a finite type. -/
lemma derivs_finite {A B : Type} {f : List A → List B}
    (h1 : {g | ∃ w : List A, g = deriv f w}.Finite) : Finite (Derivs f) :=
  h1.to_subtype

/-- The minimal Mealy machine of a function: its states are the derivatives of
the function, and reading a letter `a` in the state `g` outputs the first letter
of `g a` and moves to the derivative `v ↦ drop 1 (g (a v))`. -/
def derivMealy {A B : Type} [Inhabited B] (f : List A → List B) :
    Mealy A B (Derivs f) where
  init := ⟨deriv f [], [], rfl⟩
  step := fun g a =>
    (⟨fun v => (g.1 (a :: v)).drop 1, by
        obtain ⟨w, hw⟩ := g.2
        exact ⟨w ++ [a], by rw [deriv_append_singleton, hw]⟩⟩,
      (g.1 [a]).headI)

/-- Running the minimal machine from the state `g` produces exactly `g`, for a
function that is letter-to-letter and whose `n`-th output letter depends only on
the first `n` input letters. -/
lemma derivMealy_run {A B : Type} [Inhabited B] {f : List A → List B}
    (h2 : LengthPreserving f) (h3 : PrefixDetermined f) (g : Derivs f) (v : List A) :
    (derivMealy f).run g v = g.1 v := by
  induction v generalizing g with
  | nil =>
      obtain ⟨u, hu⟩ := g.2
      have : g.1 [] = [] := by
        rw [hu]
        exact List.eq_nil_of_length_eq_zero (by rw [deriv_length h2]; rfl)
      rw [Mealy.run_nil, this]
  | cons a v ih =>
      obtain ⟨u, hu⟩ := g.2
      have hlen : (g.1 (a :: v)).length = v.length + 1 := by
        rw [hu, deriv_length h2]
        simp
      have h1 : (g.1 (a :: v)).take 1 = g.1 [a] := by
        rw [hu, deriv_take h2 h3]
        rfl
      have hstep : ((derivMealy f).step g a).1.1 v = (g.1 (a :: v)).drop 1 := rfl
      have hout : ((derivMealy f).step g a).2 = (g.1 [a]).headI := rfl
      rw [Mealy.run_cons, ih, hstep, hout, ← h1]
      cases hl : g.1 (a :: v) with
      | nil => rw [hl] at hlen; simp at hlen
      | cons b l => simp

/-- The minimal machine computes the function. -/
lemma derivMealy_eval {A B : Type} [Inhabited B] {f : List A → List B}
    (h2 : LengthPreserving f) (h3 : PrefixDetermined f) : (derivMealy f).eval = f := by
  funext w
  have hrun := derivMealy_run h2 h3 (derivMealy f).init w
  rw [Mealy.eval, hrun]
  show (f ([] ++ w)).drop 0 = f w
  simp

/-- The state transformation of the minimal machine. -/
lemma derivMealy_trans {A B : Type} [Inhabited B] (f : List A → List B) (z : List A)
    (g : Derivs f) : ((derivMealy f).trans z g).1 = fun v => (g.1 (z ++ v)).drop z.length := by
  induction z generalizing g with
  | nil => simp
  | cons a z ih =>
      rw [Mealy.trans_cons, ih]
      funext v
      simp [derivMealy, Mealy.letterTrans]

/-- The state transformation of the minimal machine, on the state of a
derivative. -/
lemma derivMealy_trans_deriv {A B : Type} [Inhabited B] (f : List A → List B) (u z : List A) :
    (derivMealy f).trans z ⟨deriv f u, u, rfl⟩ = ⟨deriv f (u ++ z), u ++ z, rfl⟩ := by
  apply Subtype.ext
  rw [derivMealy_trans f z (⟨deriv f u, u, rfl⟩ : Derivs f)]
  exact (deriv_append f u z).symm

/-- Iterating the state transformation of the minimal machine. -/
lemma derivMealy_trans_iterate {A B : Type} [Inhabited B] (f : List A → List B) (u z : List A)
    (n : ℕ) :
    ((derivMealy f).trans z)^[n] ⟨deriv f u, u, rfl⟩ = ⟨deriv f (u ++ npow z n), _, rfl⟩ := by
  induction n with
  | zero => apply Subtype.ext; show deriv f u = _; simp
  | succ n ih =>
      rw [Function.iterate_succ_apply' ((derivMealy f).trans z) n
        (⟨deriv f u, u, rfl⟩ : Derivs f), ih, derivMealy_trans_deriv]
      apply Subtype.ext
      rw [npow_succ', ← List.append_assoc]

/-- If the input alphabet is nonempty, then a letter-to-letter function forces
the output alphabet to be nonempty. -/
lemma nonempty_output {A B : Type} {f : List A → List B} (h2 : LengthPreserving f) (a : A) :
    Nonempty B := by
  have hlen := h2 [a]
  match hfa : f [a] with
  | [] => rw [hfa] at hlen; simp at hlen
  | b :: _ => exact ⟨b⟩

/-- Degenerate case: over an empty input alphabet, every function mapping the
empty string to the empty string is computed by a Mealy machine, which
trivially satisfies condition (*). -/
lemma isEmpty_input_mealy {A B : Type} [IsEmpty A] (f : List A → List B) (hf : f [] = []) :
    ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ M.TransStabilises := by
  refine ⟨Unit, inferInstance, ⟨(), fun _ a => isEmptyElim a⟩, ?_, ?_⟩
  · funext w
    match w with
    | [] => exact hf.symm
    | a :: _ => exact isEmptyElim a
  · intro z
    exact ⟨0, fun n _ => Subsingleton.elim _ _⟩

/-- **Lemma `lemma:derivatives` (Myhill-Nerode for Mealy machines), left-to-right.** -/
lemma myhill_nerode_mealy_forward {A B : Type} (f : List A → List B) (hf : IsMealy f) :
    ({g | ∃ w : List A, g = deriv f w}.Finite ∧
      LengthPreserving f ∧
      ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n) := by
  obtain ⟨Q, _, M, rfl⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · apply Set.Finite.subset (Set.Finite.image (fun q : Q => fun v : List A => M.run q v)
      (Set.toFinite (Set.univ : Set Q)))
    intro g hg
    obtain ⟨w, rfl⟩ := hg
    rw [deriv_eval]
    exact ⟨M.trans w M.init, Set.mem_univ _, rfl⟩
  · exact fun w => Mealy.eval_length M w
  · intro w v n h
    have run_take : ∀ (q : Q) (w : List A) (n : ℕ), (M.run q w).take n = M.run q (w.take n) := by
      intro q w n
      induction w generalizing q n with
      | nil => simp
      | cons a w' ih =>
        cases n with
        | zero => simp
        | succ n => simp [ih]
    simp [Mealy.eval, run_take, h]

/-- **Lemma `lemma:derivatives` (Myhill-Nerode for Mealy machines), right-to-left.** -/
lemma myhill_nerode_mealy_backward {A B : Type} (f : List A → List B)
    (h1 : {g | ∃ w : List A, g = deriv f w}.Finite)
    (h2 : LengthPreserving f)
    (h3 : ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n) :
    IsMealy f := by
  by_cases hA : Nonempty A
  · obtain ⟨a⟩ := hA
    haveI : Nonempty B := nonempty_output h2 a
    haveI : Inhabited B := Classical.inhabited_of_nonempty ‹Nonempty B›
    haveI : Finite (Derivs f) := derivs_finite h1
    exact ⟨Derivs f, inferInstance, derivMealy f, derivMealy_eval h2 h3⟩
  · haveI : IsEmpty A := not_nonempty_iff.mp hA
    obtain ⟨Q, hQ, M, hM, _⟩ := isEmpty_input_mealy f (List.eq_nil_of_length_eq_zero (h2 []))
    exact ⟨Q, hQ, M, hM⟩

/-- **Lemma `lemma:derivatives` (Myhill-Nerode for Mealy machines).**  A string-to-string
function is computed by a Mealy machine if and only if: (1) it has finitely many
derivatives; (2) it is letter-to-letter; (3) the `n`-th output letter depends
only on the first `n` input letters. -/
theorem myhill_nerode_mealy {A B : Type} (f : List A → List B) :
    IsMealy f ↔
      ({g | ∃ w : List A, g = deriv f w}.Finite ∧
        LengthPreserving f ∧
        ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n) :=
  ⟨myhill_nerode_mealy_forward f, fun h => myhill_nerode_mealy_backward f h.1 h.2.1 h.2.2⟩

/-! #### Pumping and stabilisation of state transformations -/

/-- The state transformation of `vⁿ` is the `n`-th iterate of that of `v`. -/
lemma Mealy.trans_npow {A B Q : Type} (M : Mealy A B Q) (v : List A) (n : ℕ) (q : Q) :
    M.trans (npow v n) q = (M.trans v)^[n] q := by
  induction n generalizing q with
  | zero => simp
  | succ n ih => rw [npow_succ, Mealy.trans_append, ih, Function.iterate_succ_apply]

/-- The state reached after reading `u vⁿ`. -/
lemma trans_npow_iterate {A B Q : Type} (M : Mealy A B Q) (u v : List A) (n : ℕ) :
    M.trans (u ++ npow v n) M.init = (M.trans v)^[n] (M.trans u M.init) := by
  rw [Mealy.trans_append, Mealy.trans_npow]

/-- The output of a Mealy machine on `u vⁿ w`. -/
lemma eval_npow_decomposition {A B Q : Type} (M : Mealy A B Q) (u v w : List A) (n : ℕ) :
    M.eval (u ++ npow v n ++ w) =
      M.eval u ++ M.run (M.trans u M.init) (npow v n) ++
        M.run ((M.trans v)^[n] (M.trans u M.init)) w := by
  rw [List.append_assoc, Mealy.eval_append, Mealy.run_append, Mealy.trans_npow,
    ← List.append_assoc]

/-- If a state is fixed by the string `v`, then the outputs on `vⁿ` are
repetitions. -/
lemma run_npow_of_fixed {A B Q : Type} (M : Mealy A B Q) {v : List A} {q : Q}
    (hq : M.trans v q = q) (n : ℕ) : M.run q (npow v n) = npow (M.run q v) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [npow_succ, Mealy.run_append, hq, ih, npow_succ]

/-- A machine whose state transformations stabilise has the pumping property of
Claim `claim:aperiodic-pumping`. -/
lemma transStabilises_pumping {A B Q : Type} (M : Mealy A B Q) (hM : M.TransStabilises)
    (u v w : List A) :
    ∃ (x y z : List B) (k : ℕ), ∀ n > 0,
      M.eval (u ++ npow v (n + k) ++ w) = x ++ npow y n ++ z := by
  obtain ⟨N, hN⟩ := hM v
  have htr : strTrans M.transFun v = M.trans v := rfl
  rw [htr] at hN
  have hfixed : M.trans v ((M.trans v)^[N] (M.trans u M.init))
      = (M.trans v)^[N] (M.trans u M.init) := by
    have h1 := congrFun (hN (N + 1) (by omega)) (M.trans u M.init)
    rw [Function.iterate_succ_apply'] at h1
    exact h1
  refine ⟨M.eval u ++ M.run (M.trans u M.init) (npow v N),
    M.run ((M.trans v)^[N] (M.trans u M.init)) v,
    M.run ((M.trans v)^[N] (M.trans u M.init)) w, N, fun n hn => ?_⟩
  have hsplit : npow v (n + N) = npow v N ++ npow v n := by
    rw [Nat.add_comm, npow_add]
  have hstate : (M.trans v)^[n + N] (M.trans u M.init)
      = (M.trans v)^[N] (M.trans u M.init) := congrFun (hN (n + N) (by omega)) _
  rw [eval_npow_decomposition, hsplit, Mealy.run_append, Mealy.trans_npow, hstate,
    run_npow_of_fixed M hfixed n]
  simp [List.append_assoc]

/-- The pumping property of Claim `claim:aperiodic-pumping` implies aperiodicity. -/
lemma pumping_aperiodic {A B : Type} (f : List A → List B)
    (h : ∀ u v w : List A, ∃ (x y z : List B) (k : ℕ), ∀ n > 0,
      f (u ++ npow v (n + k) ++ w) = x ++ npow y n ++ z) : Aperiodic f := by
  intro u v w
  obtain ⟨x, y, z, k, hk⟩ := h u v w
  refine ⟨(x ++ npow y 1 ++ z).getLast?, k + 1, fun n hn => ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
  have hm1 : 0 < m := by omega
  subst hm
  rw [hk m hm1]
  exact getLast?_npow_const x y z m 1 hm1 (by norm_num)

/-- The last letter of a value of a derivative. -/
lemma getLast?_deriv {A B : Type} {f : List A → List B} (h2 : LengthPreserving f)
    (u v : List A) (hv : v ≠ []) : (deriv f u v).getLast? = (f (u ++ v)).getLast? := by
  have hlen : (f (u ++ v)).length = u.length + v.length := by
    rw [h2 (u ++ v)]; simp
  refine getLast?_drop _ ?_
  rw [hlen]
  have : 0 < v.length := List.length_pos_iff.mpr hv
  omega

/-- The derivatives of an aperiodic function stabilise along `u zⁿ`. -/
lemma aperiodic_deriv_eventually_const {A B : Type} {f : List A → List B}
    (h1 : {g | ∃ w : List A, g = deriv f w}.Finite) (h2 : LengthPreserving f)
    (h3 : PrefixDetermined f) (ha : Aperiodic f) (u z : List A) :
    ∃ N : ℕ, ∀ n ≥ N, deriv f (u ++ npow z n) = deriv f (u ++ npow z N) := by
  haveI : Finite (Derivs f) := derivs_finite h1
  have hsep : ∀ x y : Derivs f, (∀ v : List A, (x.1 v).getLast? = (y.1 v).getLast?) → x = y := by
    intro x y hxy
    obtain ⟨u1, hu1⟩ := x.2
    obtain ⟨u2, hu2⟩ := y.2
    apply Subtype.ext
    rw [hu1, hu2]
    refine deriv_ext h2 h3 u1 u2 (fun v => ?_)
    have hv := hxy v
    rw [hu1, hu2] at hv
    exact hv
  have hnil : ∀ w : List A, deriv f w [] = [] :=
    fun w => List.eq_nil_of_length_eq_zero (by rw [deriv_length h2]; rfl)
  have htest : ∀ v : List A, ∃ N : ℕ, ∀ n ≥ N,
      (deriv f (u ++ npow z n) v).getLast? = (deriv f (u ++ npow z N) v).getLast? := by
    intro v
    by_cases hv : v = []
    · subst hv
      exact ⟨0, fun n _ => by rw [hnil, hnil]⟩
    · obtain ⟨o, N, hNo⟩ := ha u z v
      refine ⟨N, fun n hn => ?_⟩
      rw [getLast?_deriv h2 _ _ hv, getLast?_deriv h2 _ _ hv, hNo n hn, hNo N le_rfl]
  obtain ⟨N, hN⟩ :=
    eventually_const_of_tests (S := Derivs f) (V := List A) (R := Option B)
      (fun n => (⟨deriv f (u ++ npow z n), u ++ npow z n, rfl⟩ : Derivs f))
      (fun g v => (g.1 v).getLast?) hsep htest
  exact ⟨N, fun n hn => congrArg Subtype.val (hN n hn)⟩

/-- An aperiodic function computed by a Mealy machine has a minimal machine
whose state transformations stabilise. -/
lemma aperiodic_derivMealy_transStabilises {A B : Type} [Inhabited B] {f : List A → List B}
    (h1 : {g | ∃ w : List A, g = deriv f w}.Finite) (h2 : LengthPreserving f)
    (h3 : PrefixDetermined f) (ha : Aperiodic f) : (derivMealy f).TransStabilises := by
  haveI : Finite (Derivs f) := derivs_finite h1
  intro z
  have htr : strTrans (derivMealy f).transFun z = (derivMealy f).trans z := rfl
  rw [htr]
  apply iterate_stabilises_of_pointwise
  intro g
  obtain ⟨u, hu⟩ := g.2
  obtain ⟨N, hNN⟩ := aperiodic_deriv_eventually_const h1 h2 h3 ha u z
  refine ⟨N, fun n hn => ?_⟩
  have hg : g = ⟨deriv f u, u, rfl⟩ := Subtype.ext hu
  rw [hg, derivMealy_trans_iterate, derivMealy_trans_iterate]
  exact Subtype.ext (hNN n hn)

/-- **Lemma `lem:aperiodicity-minimal-machine`.**  A function computed by a Mealy machine is
aperiodic if and only if its minimal Mealy machine satisfies condition (*): for every state
transformation `δ` arising from an input string, the sequence `δ¹, δ², …` eventually stabilises.

The statement below avoids constructing the minimal machine explicitly: since
condition (*) is inherited by the minimal machine from any machine computing
`f`, the condition "the minimal machine satisfies (*)" is equivalent to "some
machine computing `f` satisfies (*)".

The finiteness assumptions on the alphabets, which are global assumptions in the
book, are not needed. -/
theorem aperiodic_iff_transStabilises {A B : Type} {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔
      ∃ (Q : Type) (_ : Finite Q) (M : Mealy A B Q), M.eval = f ∧ M.TransStabilises := by
  obtain ⟨h1, h2, h3⟩ := myhill_nerode_mealy_forward f hf
  constructor
  · intro ha
    by_cases hA : Nonempty A
    · obtain ⟨a⟩ := hA
      haveI : Nonempty B := nonempty_output h2 a
      haveI : Inhabited B := Classical.inhabited_of_nonempty ‹Nonempty B›
      haveI : Finite (Derivs f) := derivs_finite h1
      exact ⟨Derivs f, inferInstance, derivMealy f, derivMealy_eval h2 h3,
        aperiodic_derivMealy_transStabilises h1 h2 h3 ha⟩
    · haveI : IsEmpty A := not_nonempty_iff.mp hA
      exact isEmpty_input_mealy f (List.eq_nil_of_length_eq_zero (h2 []))
  · rintro ⟨Q, hQ, M, heval, hM⟩
    rw [← heval]
    exact pumping_aperiodic _ (transStabilises_pumping M hM)

/-- **Claim `claim:aperiodic-pumping`.**  A function computed by a Mealy machine is
aperiodic if and only if for all input strings `u, v, w` there are output strings `x, y, z` and a
number `k` such that `f (u v^{n+k} w) = x yⁿ z` for all `n > 0`. -/
theorem aperiodic_iff_pumping {A B : Type} {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔
      ∀ u v w : List A, ∃ (x y z : List B) (k : ℕ), ∀ n > 0,
        f (u ++ npow v (n + k) ++ w) = x ++ npow y n ++ z := by
  constructor
  · intro ha
    obtain ⟨Q, hQ, M, heval, hM⟩ := (aperiodic_iff_transStabilises hf).mp ha
    intro u v w
    rw [← heval]
    exact transStabilises_pumping M hM u v w
  · exact pumping_aperiodic f

/-! #### Compositions of flip-flop machines are aperiodic -/

/-- In a flip-flop machine, the state transformation of every input string is
the identity or a constant. -/
lemma trans_flipflop {A B Q : Type} {M : Mealy A B Q} (h : M.FlipFlop) (z : List A) :
    M.trans z = id ∨ ∃ q₀ : Q, ∀ q : Q, M.trans z q = q₀ := by
  induction z with
  | nil => left; rfl
  | cons a w ih =>
    rcases h a with ha | ⟨q₀, hq₀⟩
    · have hstep : M.trans (a :: w) = M.trans w := by
        ext q
        rw [Mealy.trans_cons, ha]
        rfl
      rw [hstep]; exact ih
    · right; use M.trans w q₀; intro q; rw [Mealy.trans_cons, hq₀]

/-- Flip-flop machines satisfy condition (*). -/
lemma flipflop_transStabilises {A B Q : Type} {M : Mealy A B Q} (h : M.FlipFlop) :
    M.TransStabilises := by
  intro z
  refine ⟨1, fun n hn => ?_⟩
  rcases trans_flipflop h z with hid | ⟨q₀, hq₀⟩
  · have ht : strTrans M.transFun z = id := hid
    rw [ht]
    simp
  · have ht : strTrans M.transFun z = M.trans z := rfl
    have key : ∀ (m : ℕ) (q : Q), (M.trans z)^[m + 1] q = q₀ := by
      intro m
      induction m with
      | zero => intro q; simpa using hq₀ q
      | succ m ih =>
        intro q
        rw [Function.iterate_succ_apply', ih q, hq₀ q₀]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [ht]
    funext q
    rw [key m q]
    simpa using (hq₀ q).symm

/-- The identity function is computed by a one-state Mealy machine. -/
lemma isMealy_id {A : Type} : IsMealy (id : List A → List A) := by
  refine ⟨Unit, inferInstance, ⟨(), fun _ a => ((), a)⟩, ?_⟩
  funext w
  show Mealy.run _ () w = w
  induction w with
  | nil => rfl
  | cons a w ih => simpa using ih

/-- A composition of flip-flop machines is computed by a Mealy machine. -/
lemma isMealy_of_flipflop_composition {A B : Type} {f : List A → List B}
    (h : CompClosure FlipFlopFam A B f) : IsMealy f := by
  induction h with
  | base hf =>
      obtain ⟨Q, hQ, M, hM, _⟩ := hf
      exact ⟨Q, hQ, M, hM⟩
  | id A => exact isMealy_id
  | comp _ _ ihf ihg => exact mealy_comp ihf ihg

/-- Aperiodicity is preserved by composition. -/
lemma aperiodic_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsMealy f) (hg : IsMealy g) (haf : Aperiodic f) (hag : Aperiodic g) :
    Aperiodic (g ∘ f) := by
  have hpf := (aperiodic_iff_pumping hf).mp haf
  have hpg := (aperiodic_iff_pumping hg).mp hag
  apply pumping_aperiodic
  intro u v w
  obtain ⟨x, y, z, k, hk⟩ := hpf u v w
  obtain ⟨x', y', z', k', hk'⟩ := hpg x y z
  refine ⟨x', y', z', k + k', fun n hn => ?_⟩
  have harith : n + (k + k') = (n + k') + k := by omega
  show g (f (u ++ npow v (n + (k + k')) ++ w)) = _
  rw [harith, hk (n + k') (by omega), hk' n hn]

/-- A composition of flip-flop Mealy machines is aperiodic: this is the
right-to-left implication of Theorem `thm:aperiodic-mealy`. -/
lemma flipflop_composition_aperiodic {A B : Type} {f : List A → List B}
    (h : CompClosure FlipFlopFam A B f) : Aperiodic f := by
  induction h with
  | base hf =>
      obtain ⟨Q, hQ, M, rfl, hM⟩ := hf
      exact pumping_aperiodic _ (transStabilises_pumping M (flipflop_transStabilises hM))
  | id A =>
      apply pumping_aperiodic
      intro u v w
      exact ⟨u, v, w, 0, fun n _ => by simp⟩
  | comp hf hg ihf ihg =>
      exact aperiodic_comp (isMealy_of_flipflop_composition hf)
        (isMealy_of_flipflop_composition hg) ihf ihg

/-- **Theorem `thm:aperiodic-mealy`.**  A function computed by a Mealy machine is aperiodic if and
only if it is computed by a composition of flip-flop Mealy machines.

*Divergence from the book.*  The theorem also asserts that "this property can be decided, given a
Mealy machine that computes `f`", and that part is **not** formalised.  What is formalised is the
characterisation that the book's decision procedure rests on, Lemma
`lem:aperiodicity-minimal-machine` above; the enumeration of the state transformations that arise
from input strings, and the resulting decision procedure, are not. -/
theorem aperiodic_iff_flipflop_composition {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔ CompClosure FlipFlopFam A B f := by
  constructor
  · intro ha
    obtain ⟨Q, hQ, M, heval, hM⟩ := (aperiodic_iff_transStabilises hf).mp ha
    haveI := hQ
    rw [← heval]
    exact krohn_rhodes_flipFlop M hM
  · exact flipflop_composition_aperiodic

end Lax765601Proofs.Transducers