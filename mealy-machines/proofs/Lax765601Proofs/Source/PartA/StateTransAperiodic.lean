/-
The aperiodic case of the Krohn-Rhodes construction: the implication
"aperiodic ⇒ composition of flip-flops" of Theorem `thm:aperiodic-mealy` of *Transducers*
(M. Bojańczyk, June 25, 2026).

The book proves this implication by going through the proof of the Krohn-Rhodes Theorem once more,
for a machine satisfying condition (*) of Lemma `lem:aperiodicity-minimal-machine` (the powers of
every state transformation stabilise), and observing that all the machines of the construction still
satisfy (*) -- because they only use state transformations of the original machine -- so that no
reversible machine with more than one state ever arises.

This file carries that out for the construction of `RequestProject/PartA/StateTrans.lean`.
The two smaller pre-automata used in the induction step inherit condition (*):

* `deltaFree`, in which the letter `a` acts as the identity, realises only state
  transformations of the original pre-automaton (`transAperiodic_deltaFree`);
* `deltaMid`, on the image of the state transformation of `a`, applies only
  *realisable* transformations, by the definition of `deltaMid`, so its state
  transformations are restrictions of state transformations of the original
  pre-automaton (`transAperiodic_deltaMid`).

In the induction basis, a pre-automaton all of whose letters are permutations
and which satisfies (*) has only identity letters, so its state transformation
transducer is a flip-flop machine.
-/
import Lax765601Proofs.Source.PartA.StateTrans
import Lax765601Proofs.Source.PartA.FlipFlopClosure

namespace Lax765601Proofs.Transducers

/-! ## The induction basis in the aperiodic case -/

/-- A bijective state transformation of an aperiodic pre-automaton is the
identity. -/
lemma letterTrans_eq_id_of_bijective {A Q : Type} {δ : Q → A → Q} (h : TransAperiodic δ)
    {y : A} (hb : Function.Bijective (fun q => δ q y)) : (fun q => δ q y) = id := by
  obtain ⟨N, hN⟩ := h [y]
  have hg : strTrans δ [y] = fun q => δ q y := by funext q; simp [strTrans]
  rw [hg] at hN
  set g : Q → Q := fun q => δ q y with hgdef
  have h1 : g^[N + 1] = g^[N] := hN (N + 1) (by omega)
  have hinj : Function.Injective g^[N] := Function.Injective.iterate hb.injective N
  funext q
  have h2 : g^[N] (g q) = g^[N] q := by
    have h3 := congrFun h1 q
    rwa [Function.iterate_succ_apply] at h3
  exact hinj h2

/-- The state transformation transducer of a pre-automaton all of whose letters
act as the identity is a flip-flop machine. -/
lemma stateTransTransducer_flipFlop {A Q : Type} {δ : Q → A → Q}
    (h : ∀ y : A, (fun q => δ q y) = id) : (stateTransTransducer δ).FlipFlop := by
  intro y
  left
  funext t
  funext q
  have hq := congrFun (h y) (t q)
  simpa [Mealy.letterTrans, stateTransTransducer] using hq

/-- Induction basis of the aperiodic case. -/
lemma stateTransTransducer_flipFlop_of_reversible {A Q : Type} [Finite A] [Finite Q]
    {δ : Q → A → Q} (h : TransAperiodic δ) (hb : ∀ y : A, Function.Bijective (fun q => δ q y)) :
    CompClosure FlipFlopFam A (Q → Q) (stateTransTransducer δ).eval :=
  CompClosure.base
    ⟨Q → Q, inferInstance, stateTransTransducer δ, rfl,
      stateTransTransducer_flipFlop (fun y => letterTrans_eq_id_of_bijective h (hb y))⟩

/-! ## Condition (*) is inherited by the two smaller pre-automata -/

section
variable {A Q : Type} [DecidableEq A] (δ : Q → A → Q) (a : A)

/-- Reading a word in the pre-automaton where `a` acts as the identity is the
same as reading the word with the letters `a` deleted. -/
lemma strTrans_deltaFree (w : List A) :
    strTrans (deltaFree δ a) w = strTrans δ (w.filter (fun y => decide (y ≠ a))) := by
  funext q
  induction w generalizing q with
  | nil => rfl
  | cons y w ih =>
      by_cases h : y = a
      · simp [strTrans, deltaFree, h] at *
        exact ih q
      · simp [strTrans, deltaFree, h] at *
        exact ih _

/-- Condition (*) is inherited by the pre-automaton in which `a` acts as the
identity. -/
lemma transAperiodic_deltaFree (h : TransAperiodic δ) : TransAperiodic (deltaFree δ a) := by
  intro w
  obtain ⟨N, hN⟩ := h (w.filter (fun y => decide (y ≠ a)))
  exact ⟨N, fun n hn => by rw [strTrans_deltaFree]; exact hN n hn⟩

/-- Every state transformation of the middle pre-automaton is the restriction of
a state transformation of the original one. -/
lemma strTrans_deltaMid (W : List (Enr δ a)) :
    ∃ v : List A, ∀ p : Img δ a,
      ((strTrans (deltaMid δ a) W p : Img δ a) : Q) = strTrans δ v (p : Q) := by
  induction W with
  | nil => exact ⟨[], fun p => rfl⟩
  | cons e W ih =>
      obtain ⟨v, hv⟩ := ih
      by_cases h : e.1 = a ∧ e.2.1 = true ∧ Realisable δ e.2.2.2.1
      · obtain ⟨u, hu⟩ := h.2.2
        refine ⟨(u ++ [a]) ++ v, fun p => ?_⟩
        have hstep : ((deltaMid δ a p e : Img δ a) : Q) = strTrans δ (u ++ [a]) (p : Q) := by
          rw [deltaMid, if_pos h]
          simp [hu, strTrans]
        show ((strTrans (deltaMid δ a) W (deltaMid δ a p e) : Img δ a) : Q) = _
        rw [hv (deltaMid δ a p e), hstep]
        simp [strTrans, List.foldl_append]
      · refine ⟨v, fun p => ?_⟩
        show ((strTrans (deltaMid δ a) W (deltaMid δ a p e) : Img δ a) : Q) = _
        rw [show deltaMid δ a p e = p by rw [deltaMid, if_neg h], hv p]

/-- Condition (*) is inherited by the middle pre-automaton. -/
lemma transAperiodic_deltaMid (h : TransAperiodic δ) : TransAperiodic (deltaMid δ a) := by
  intro W
  obtain ⟨v, hv⟩ := strTrans_deltaMid δ a W
  obtain ⟨N, hN⟩ := h v
  have key : ∀ (m : ℕ) (p : Img δ a),
      (((strTrans (deltaMid δ a) W)^[m] p : Img δ a) : Q) = (strTrans δ v)^[m] (p : Q) := by
    intro m
    induction m with
    | zero => intro p; rfl
    | succ m ih =>
        intro p
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hv]
  refine ⟨N, fun n hn => ?_⟩
  funext p
  apply Subtype.ext
  rw [key n p, key N p, hN n hn]

/-! ## The chain of stages consists of flip-flops -/

lemma tailFun_compClosure_flipFlop [Finite A] [Finite Q]
    (hfree : CompClosure FlipFlopFam A (Q → Q) (stateTransTransducer (deltaFree δ a)).eval) :
    CompClosure FlipFlopFam (Enr δ a) (Q → Q) (tailFun δ a) := by
  have h1 : CompClosure FlipFlopFam (Enr δ a) (Option A)
      (List.map (fun e : Enr δ a => if e.1 = a then none else some e.1)) :=
    CompClosure.base (flipFlop_map _)
  have h2 : CompClosure FlipFlopFam (Option A) (Option (Q → Q))
      (mapLift (stateTransTransducer (deltaFree δ a)).eval) :=
    mapLift_compClosure_flipFlop inferInstance hfree
  have h3 : CompClosure FlipFlopFam (Option (Q → Q)) (Q → Q)
      (List.map (fun o : Option (Q → Q) => o.getD id)) := CompClosure.base (flipFlop_map _)
  have h4 := CompClosure.comp h1 (CompClosure.comp h2 h3)
  exact h4

/-- The flip-flop version of `krStages_compClosure`: the chain of stages of the
induction step consists of flip-flop machines only. -/
theorem krStages_compClosure_flipFlop [Finite A] [Finite Q]
    (hfree : CompClosure FlipFlopFam A (Q → Q) (stateTransTransducer (deltaFree δ a)).eval)
    (hmid : CompClosure FlipFlopFam (Enr δ a) (Img δ a → Img δ a)
      (stateTransTransducer (deltaMid δ a)).eval) :
    CompClosure FlipFlopFam A (Q → Q) (krStages δ a) := by
  have htail := tailFun_compClosure_flipFlop δ a hfree
  have c0 : CompClosure FlipFlopFam A (Enr δ a) (List.map (init0 δ a)) :=
    CompClosure.base (flipFlop_map _)
  have g1 : CompClosure FlipFlopFam (Enr δ a) Bool (seenMealy δ a).eval :=
    CompClosure.base ⟨Bool, inferInstance, seenMealy δ a, rfl, seenMealy_flipFlop δ a⟩
  have g3 : CompClosure FlipFlopFam (Enr δ a) (Q → Q) (prevMealy δ a).eval :=
    CompClosure.base ⟨Q → Q, inferInstance, prevMealy δ a, rfl, prevMealy_flipFlop δ a⟩
  have g4 : CompClosure FlipFlopFam (Enr δ a) (Option (Q → Q)) (firstMealy δ a).eval :=
    CompClosure.base
      ⟨Option (Q → Q), inferInstance, firstMealy δ a, rfl, firstMealy_flipFlop δ a⟩
  have c1 := CompClosure.comp (compClosure_zipInput_flipFlop inferInstance g1)
    (CompClosure.base (flipFlop_map (pack1 δ a)))
  have c2 := CompClosure.comp (compClosure_zipInput_flipFlop inferInstance htail)
    (CompClosure.base (flipFlop_map (pack2 δ a)))
  have c3 := CompClosure.comp (compClosure_zipInput_flipFlop inferInstance g3)
    (CompClosure.base (flipFlop_map (pack3 δ a)))
  have c4 := CompClosure.comp (compClosure_zipInput_flipFlop inferInstance g4)
    (CompClosure.base (flipFlop_map (pack4 δ a)))
  have c5 := CompClosure.comp (compClosure_zipInput_flipFlop inferInstance hmid)
    (CompClosure.base (flipFlop_map (pack5 δ a)))
  have c6 : CompClosure FlipFlopFam (Enr δ a) (Q → Q) (List.map (combineEnr δ a)) :=
    CompClosure.base (flipFlop_map _)
  have h := CompClosure.comp c0 (CompClosure.comp c1 (CompClosure.comp c2
    (CompClosure.comp c3 (CompClosure.comp c4 (CompClosure.comp c5 c6)))))
  exact h

end

/-! ## The induction -/

/-- The double induction of Lemma `lem:Mealy-map-lifting`, in the aperiodic case. -/
theorem stateTrans_aux_flipFlop : ∀ (n : ℕ) (Q : Type) (_ : Finite Q), Nat.card Q ≤ n →
    ∀ (m : ℕ) (A : Type) (_ : Finite A) (δ : Q → A → Q), (nonBijSet δ).ncard ≤ m →
    TransAperiodic δ → CompClosure FlipFlopFam A (Q → Q) (stateTransTransducer δ).eval := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro Q hQ hQn m
    haveI := hQ
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro A hA δ hm hap
      haveI := hA
      classical
      by_cases hrev : ∀ y : A, Function.Bijective (fun q => δ q y)
      · exact stateTransTransducer_flipFlop_of_reversible hap hrev
      · push_neg at hrev
        obtain ⟨a, ha⟩ := hrev
        have hfree : CompClosure FlipFlopFam A (Q → Q)
            (stateTransTransducer (deltaFree δ a)).eval := by
          have hlt : (nonBijSet (deltaFree δ a)).ncard < (nonBijSet δ).ncard :=
            Set.ncard_lt_ncard (nonBijSet_deltaFree_ssubset δ ha) (Set.toFinite _)
          exact ihm _ (lt_of_lt_of_le hlt hm) A hA _ le_rfl (transAperiodic_deltaFree δ a hap)
        have hmid : CompClosure FlipFlopFam (Enr δ a) (Img δ a → Img δ a)
            (stateTransTransducer (deltaMid δ a)).eval :=
          ihn (Nat.card (Img δ a)) (lt_of_lt_of_le (card_img_lt δ ha) hQn) (Img δ a)
            inferInstance le_rfl _ (Enr δ a) inferInstance _ le_rfl
            (transAperiodic_deltaMid δ a hap)
        rw [← krStages_eq δ a]
        exact krStages_compClosure_flipFlop δ a hfree hmid

/-- The state transformation transducer of an aperiodic pre-automaton is a
composition of flip-flop Mealy machines. -/
theorem stateTransTransducer_flipFlop_decomposition {A Q : Type} [Finite A] [Finite Q]
    (δ : Q → A → Q) (h : TransAperiodic δ) :
    CompClosure FlipFlopFam A (Q → Q) (stateTransTransducer δ).eval :=
  stateTrans_aux_flipFlop (Nat.card Q) Q inferInstance le_rfl ((nonBijSet δ).ncard) A
    inferInstance δ le_rfl h

end Lax765601Proofs.Transducers