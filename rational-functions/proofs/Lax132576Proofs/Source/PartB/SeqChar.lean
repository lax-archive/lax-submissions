/-
The machine independent characterisation of sequential functions
(Theorem `thm:sequential-function-independent`) from *Transducers* (M. Bojanczyk).

Following the book, the transducer computing `f` outputs the *derivative*
`f(wa)` with `f(w)` removed, and its states are the Myhill-Nerode classes of two
families of regular languages:

* the length of the output modulo `K + 1`, where `K` bounds the length of the
  derivatives -- this determines the length of the next derivative;
* which short words are suffixes of the output -- together with the length this
  determines the next derivative itself.
-/
import Lax765601Proofs.Source.PartA.MealyBasic
import Lax132576Proofs.Source.Common.RegularAux
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-! ## Two families of regular languages -/

section RegularLang

variable {B : Type}

/-- The language of strings whose length is congruent to `r` modulo `m`. -/
def lengthModLang (m r : ℕ) : Language B := {v | v.length % m = r}

/-- The dfa counting the length of the input modulo `m`. -/
def lengthModDFA (m r : ℕ) : DFA B (ℕ × ℕ) where
  step := fun s _ => ((s.1 + 1) % m, s.2)
  start := (0, r)
  accept := {s | s.1 = s.2 % m}

lemma lengthModLang_isRegular (m r : ℕ) (hm : 0 < m) :
    (lengthModLang m r : Language B).IsRegular := by
  -- Define a finite-state DFA using Fin m
  let DFA' : DFA B (Fin m) := {
    step := fun q _ => ⟨(q.val + 1) % m, Nat.mod_lt _ hm⟩
    start := ⟨0, hm⟩
    accept := {q | q.val = r}
  }
  have eval_from : ∀ (q : Fin m) (w : List B), DFA'.evalFrom q w = ⟨(q.val + w.length) % m, Nat.mod_lt _ hm⟩ := by
    intro q w
    induction w generalizing q with
    | nil =>
      simp [DFA.evalFrom]
      exact Fin.ext (Nat.mod_eq_of_lt q.isLt).symm
    | cons a w ih =>
      simp only [DFA.evalFrom]
      simp only [List.foldl_cons, List.length_cons]
      have h : List.foldl DFA'.step (DFA'.step q a) w = DFA'.evalFrom (DFA'.step q a) w := rfl
      rw [h, ih]
      congr 1
      show ((q.val + 1) % m + w.length) % m = (q.val + (w.length + 1)) % m
      rw [Nat.add_mod, Nat.add_mod]
      simp [Nat.mod_mod_of_dvd _ (dvd_refl m)]
      ring_nf
  have key : DFA'.accepts = lengthModLang m r := by
    ext w
    simp [DFA.accepts, lengthModLang]
    simp [DFA.acceptsFrom, eval_from]
    have hs : DFA'.start = ⟨0, hm⟩ := rfl
    have ha : DFA'.accept = {q : Fin m | q.val = r} := rfl
    simp [hs, ha]
  exact ⟨Fin m, inferInstance, DFA', key⟩

/-- The language of strings having `u` as a suffix. -/
def suffixLang (u : List B) : Language B := {v | u <:+ v}

/-- The dfa remembering the last `n` letters of the input. -/
def suffixDFA [DecidableEq B] (u : List B) : DFA B (List B) where
  step := fun s c => (s ++ [c]).drop ((s ++ [c]).length - u.length)
  start := []
  accept := {s | s = u}

lemma suffixDFA_evalFrom_eq [DecidableEq B] (u : List B) (v : List B) :
    (suffixDFA u).evalFrom [] v = v.drop (v.length - u.length) := by
  have aux : ∀ (s : List B), s.length ≤ u.length → (suffixDFA u).evalFrom s v = (s ++ v).drop ((s ++ v).length - u.length) := by
    intro s hs
    induction v generalizing s with
    | nil =>
      simp [DFA.evalFrom]
      rw [show s.length - u.length = 0 by omega, List.drop_zero]
    | cons a w ih =>
      simp only [DFA.evalFrom_cons]
      have hs' : ((suffixDFA u).step s a).length ≤ u.length := by
        simp [suffixDFA, List.length_drop]
        omega
      rw [ih _ hs']
      -- step s a = (s ++ [a]).drop ((s ++ [a]).length - u.length)
      -- We need to show that drop (LHS_len - u.len) (step s a ++ w)
      --   = drop (RHS_len - u.len) (s ++ [a] ++ w)
      have h_step : (suffixDFA u).step s a = (s ++ [a]).drop ((s ++ [a]).length - u.length) := by
        rfl
      simp only [h_step]
      -- Now we case split on whether s.length < u.length or s.length = u.length
      by_cases h : s.length < u.length
      · -- Case: s.length < u.length, so (s ++ [a]).length ≤ u.length
        have h1 : (s ++ [a]).length - u.length = 0 := by simp [List.length_append]; omega
        rw [h1, List.drop_zero]
        simp [List.append_assoc]
      · -- Case: s.length = u.length
        have h2 : s.length = u.length := le_antisymm hs (by omega : u.length ≤ s.length)
        have h3 : (s ++ [a]).length - u.length = 1 := by simp [List.length_append]; omega
        rw [h3]
        -- (s ++ [a]).drop 1 = s.drop 1 ++ [a] when s ≠ [], and [] when s = []
        rcases s with _ | ⟨b, s'⟩
        · -- s = []
          simp_all
          rw [← h2]
          -- Need: drop w.length w = drop (w.length + 1) (a :: w)
          -- Both sides are [] since w.length >= w.length and w.length + 1 > w.length + 1 (false)
          -- Actually drop (w.length + 1) (a :: w) = drop w.length w = []
          induction w with
          | nil => simp
          | cons x xs ih => simp
        · -- s = b :: s'
          simp_all [List.append_assoc]
          rw [← h2]
          -- Goal: drop w.length (s' ++ [a] ++ w) = drop (w.length + 1) (b :: (s' ++ [a] ++ w))
          -- RHS = (b :: _).drop (w.length + 1) = _.drop w.length by List.drop_cons
          simp
          omega
  exact aux [] (by simp)

lemma suffixDFA_accepts [DecidableEq B] (u : List B) : (suffixDFA u).accepts = suffixLang u := by
  ext v
  rw [DFA.mem_accepts]
  show (suffixDFA u).evalFrom (suffixDFA u).start v ∈ (suffixDFA u).accept ↔ _
  rw [show (suffixDFA u).start = [] from rfl, suffixDFA_evalFrom_eq]
  simp only [suffixDFA, Set.mem_setOf_eq, suffixLang]
  exact ⟨fun h => List.suffix_iff_eq_drop.2 h.symm, fun h => (List.suffix_iff_eq_drop.1 h).symm⟩

/-- The same dfa, restricted to its finitely many reachable states. -/
def suffixDFAFin [DecidableEq B] (u : List B) : DFA B {s : List B // s.length ≤ u.length} where
  step := fun s c => ⟨(s.val ++ [c]).drop ((s.val ++ [c]).length - u.length), by
    simp only [List.length_drop, List.length_append, List.length_singleton]
    omega⟩
  start := ⟨[], by simp⟩
  accept := {s | s.val = u}

lemma suffixDFAFin_val [DecidableEq B] (u : List B) (v : List B)
    (s : {s : List B // s.length ≤ u.length}) :
    ((suffixDFAFin u).evalFrom s v).val = (suffixDFA u).evalFrom s.val v := by
  induction v generalizing s with
  | nil => rfl
  | cons c v ih => rw [DFA.evalFrom_cons, DFA.evalFrom_cons, ih]; rfl

lemma suffixLang_isRegular [Finite B] (u : List B) : (suffixLang u).IsRegular := by
  classical
  haveI : Finite {s : List B // s.length ≤ u.length} :=
    (List.finite_length_le B u.length).to_subtype
  haveI : Fintype {s : List B // s.length ≤ u.length} := Fintype.ofFinite _
  refine ⟨_, inferInstance, suffixDFAFin u, ?_⟩
  ext v
  rw [DFA.mem_accepts]
  show ((suffixDFAFin u).evalFrom (suffixDFAFin u).start v).val = u ↔ _
  rw [suffixDFAFin_val u v _, show ((suffixDFAFin u).start : List B) = [] from rfl,
    suffixDFA_evalFrom_eq]
  simp only [suffixLang]
  exact ⟨fun h => List.suffix_iff_eq_drop.2 h.symm, fun h => (List.suffix_iff_eq_drop.1 h).symm⟩

end RegularLang

/-! ## Sequential transducers -/

/-- A sequential transducer: like a Mealy machine, except that a transition
produces an output string of variable length. -/
structure Sequential (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Q → A → Q × List B

namespace Sequential

variable {A B Q : Type}

/-- The transition function of the underlying automaton. -/
def transFun (T : Sequential A B Q) : Q → A → Q := fun q a => (T.step q a).1

/-- Running the transducer from a given state. -/
def run (T : Sequential A B Q) : Q → List A → List B
  | _, [] => []
  | q, a :: w => (T.step q a).2 ++ T.run (T.step q a).1 w

/-- The semantics of a sequential transducer. -/
def eval (T : Sequential A B Q) (w : List A) : List B := T.run T.init w

@[simp] lemma run_nil (T : Sequential A B Q) (q : Q) : T.run q [] = [] := rfl

lemma run_append (T : Sequential A B Q) (q : Q) (u v : List A) :
    T.run q (u ++ v) = T.run q u ++ T.run (strTrans T.transFun u q) v := by
  induction u generalizing q with
  | nil => simp [strTrans]
  | cons a u ih =>
      simp only [List.cons_append, run, ih]
      simp [strTrans, transFun, List.append_assoc]

lemma eval_append (T : Sequential A B Q) (u v : List A) :
    T.eval (u ++ v) = T.eval u ++ T.run (strTrans T.transFun u T.init) v :=
  run_append T T.init u v

/-- The dfa obtained by feeding the output of a sequential transducer to a dfa
over the output alphabet. -/
def dfaComp (T : Sequential A B Q) {σ : Type} (D : DFA B σ) : DFA A (Q × σ) where
  step := fun qs a => ((T.step qs.1 a).1, D.evalFrom qs.2 (T.step qs.1 a).2)
  start := (T.init, D.start)
  accept := {qs | qs.2 ∈ D.accept}

lemma dfaComp_accepts (T : Sequential A B Q) {σ : Type} (D : DFA B σ) :
    (T.dfaComp D).accepts = {w : List A | T.eval w ∈ D.accepts} := by
  have key : ∀ (w : List A) (q : Q) (s : σ),
      (T.dfaComp D).evalFrom (q, s) w = (strTrans T.transFun w q, D.evalFrom s (T.run q w)) := by
    intro w
    induction w with
    | nil => intro q s; simp [DFA.evalFrom, strTrans]
    | cons a w ih =>
        intro q s
        rw [DFA.evalFrom_cons, ih]
        simp only [dfaComp, run, strTrans, transFun, List.foldl_cons]
        congr 1
        rw [DFA.evalFrom_of_append]
  ext w
  rw [DFA.mem_accepts]
  show (T.dfaComp D).evalFrom (T.dfaComp D).start w ∈ (T.dfaComp D).accept ↔ _
  rw [show (T.dfaComp D).start = (T.init, D.start) from rfl, key]
  simp only [dfaComp, DFA.mem_accepts, DFA.eval, eval, Set.mem_setOf_eq]
  exact Iff.rfl

end Sequential

/-- A function computed by a sequential transducer. -/
def IsSequential {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (T : Sequential A B Q), T.eval = f

/-! ## The easy implication -/

lemma IsSequential.nil {A B : Type} {f : List A → List B} (hf : IsSequential f) : f [] = [] := by
  obtain ⟨Q, hQ, T, rfl⟩ := hf
  rfl

lemma IsSequential.prefixPreserving {A B : Type} {f : List A → List B} (hf : IsSequential f) :
    PrefixPreserving f := by
  obtain ⟨Q, hQ, T, rfl⟩ := hf
  rintro w v ⟨t, rfl⟩
  rw [Sequential.eval_append]
  exact ⟨_, rfl⟩

lemma IsSequential.continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsSequential f) : Continuous f := by
  obtain ⟨Q, hQ, T, rfl⟩ := hf
  intro L hL
  obtain ⟨σ, hσ, D, rfl⟩ := hL
  haveI : Fintype Q := Fintype.ofFinite Q
  exact ⟨Q × σ, inferInstance, T.dfaComp D, T.dfaComp_accepts D⟩

lemma IsSequential.boundedIncrease {A B : Type} [Finite A] {f : List A → List B}
    (hf : IsSequential f) :
    ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K := by
  obtain ⟨Q, hQ, T, rfl⟩ := hf
  obtain ⟨K, hK⟩ := (Set.finite_range (fun p : Q × A => (T.step p.1 p.2).2.length)).bddAbove
  refine ⟨K, fun w a => ?_⟩
  rw [Sequential.eval_append]
  have hb : ((T.step (strTrans T.transFun w T.init) a).2).length ≤ K :=
    hK ⟨(strTrans T.transFun w T.init, a), rfl⟩
  simp only [List.length_append, Sequential.run, List.append_nil]
  omega

/-! ## The construction of the transducer -/

namespace SeqChar

/-- Short words over the output alphabet. -/
abbrev Short (B : Type) (K : ℕ) : Type := {u : List B // u.length ≤ K}

instance {B : Type} [Finite B] {K : ℕ} : Finite (Short B K) :=
  (List.finite_length_le B K).to_subtype

variable {A B : Type} (f : List A → List B) (K : ℕ)

/-- The derivative of `f`: the contribution of the last letter to the output. -/
def deriv (w : List A) (a : A) : List B := (f (w ++ [a])).drop (f w).length

lemma append_deriv (hpre : PrefixPreserving f) (w : List A) (a : A) :
    f w ++ deriv f w a = f (w ++ [a]) := by
  obtain ⟨t, ht⟩ := hpre w (w ++ [a]) ⟨[a], rfl⟩
  have hdt : deriv f w a = t := by rw [deriv, ← ht, List.drop_left]
  rw [hdt, ht]

lemma deriv_length (w : List A) (a : A) :
    (deriv f w a).length = (f (w ++ [a])).length - (f w).length := by
  simp [deriv]

/-- The inverse image of the length-modulo languages. -/
def modPre (r : ℕ) : Language A := {w | (f w).length % (K + 1) = r}

/-- The inverse image of the suffix languages. -/
def sufPre (u : List B) : Language A := {w | u <:+ f w}

lemma modPre_isRegular (hcont : Continuous f) (r : ℕ) :
    (modPre f K r).IsRegular := by
  have h := hcont (lengthModLang (K + 1) r) (lengthModLang_isRegular (K + 1) r (by omega))
  convert h using 1

lemma sufPre_isRegular [Finite B] (hcont : Continuous f) (u : List B) :
    (sufPre f u).IsRegular := by
  have h := hcont (suffixLang u) (suffixLang_isRegular u)
  convert h using 1

/-- The state of the canonical transducer after reading `w`. -/
def state (w : List A) : (Fin (K + 1) → Language A) × (Short B K → Language A) :=
  (fun r => (modPre f K r).leftQuotient w, fun u => (sufPre f u.val).leftQuotient w)

lemma state_append (w : List A) (a : A) :
    state f K (w ++ [a]) =
      (fun r => (state f K w).1 r |>.leftQuotient [a], fun u => (state f K w).2 u |>.leftQuotient [a]) := by
  simp [state, Language.leftQuotient_append]

lemma state_range_finite [Finite B] (hcont : Continuous f) :
    (Set.range (state f K)).Finite := by
  have h1 : ∀ r : Fin (K + 1), (Set.range (modPre f K (r : ℕ)).leftQuotient).Finite := fun r =>
    (modPre_isRegular f K hcont r).finite_range_leftQuotient
  have h2 : ∀ u : Short B K, (Set.range (sufPre f u.val).leftQuotient).Finite := fun u =>
    (sufPre_isRegular f hcont u.val).finite_range_leftQuotient
  refine Set.Finite.subset
    (Set.Finite.prod
      (Set.Finite.pi (t := fun r : Fin (K + 1) => Set.range (modPre f K (r : ℕ)).leftQuotient) h1)
      (Set.Finite.pi (t := fun u : Short B K => Set.range (sufPre f u.val).leftQuotient) h2)) ?_
  rintro s ⟨w, rfl⟩
  exact ⟨fun r _ => ⟨w, rfl⟩, fun u _ => ⟨w, rfl⟩⟩

/-- Two inputs with the same state have the same derivatives: this is where the
modulo counting and the suffix languages are used. -/
lemma deriv_eq_of_state_eq (hpre : PrefixPreserving f)
    (hK : ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K)
    {w w' : List A} (h : state f K w = state f K w') (a : A) :
    deriv f w a = deriv f w' a := by
  have hd : f w ++ deriv f w a = f (w ++ [a]) := append_deriv f hpre w a
  have hd' : f w' ++ deriv f w' a = f (w' ++ [a]) := append_deriv f hpre w' a
  have hlen : (f w).length + (deriv f w a).length = (f (w ++ [a])).length := by
    rw [← hd]; simp
  have hlen' : (f w').length + (deriv f w' a).length = (f (w' ++ [a])).length := by
    rw [← hd']; simp
  have hdK : (deriv f w a).length ≤ K := by have := hK w a; omega
  have hdK' : (deriv f w' a).length ≤ K := by have := hK w' a; omega
  have h1 : ∀ r : Fin (K + 1),
      (modPre f K (r : ℕ)).leftQuotient w = (modPre f K (r : ℕ)).leftQuotient w' :=
    fun r => congrFun (congrArg Prod.fst h) r
  have h2 : ∀ u : Short B K,
      (sufPre f u.val).leftQuotient w = (sufPre f u.val).leftQuotient w' :=
    fun u => congrFun (congrArg Prod.snd h) u
  have hmod : ∀ (v : List A) (r : Fin (K + 1)),
      (v ∈ (modPre f K (r : ℕ)).leftQuotient w ↔ (f (w ++ v)).length % (K + 1) = (r : ℕ)) := by
    intro v r; rw [Language.mem_leftQuotient]; rfl
  have hmod' : ∀ (v : List A) (r : Fin (K + 1)),
      (v ∈ (modPre f K (r : ℕ)).leftQuotient w' ↔ (f (w' ++ v)).length % (K + 1) = (r : ℕ)) := by
    intro v r; rw [Language.mem_leftQuotient]; rfl
  -- the lengths of the outputs agree modulo `K + 1`
  have key1 : (f (w ++ [a])).length % (K + 1) = (f (w' ++ [a])).length % (K + 1) := by
    set r : Fin (K + 1) := ⟨(f (w ++ [a])).length % (K + 1), Nat.mod_lt _ (by omega)⟩ with hr
    have hin : [a] ∈ (modPre f K (r : ℕ)).leftQuotient w := (hmod [a] r).2 (by rw [hr])
    rw [h1 r] at hin
    exact ((hmod' [a] r).1 hin).symm
  have key0 : (f w).length % (K + 1) = (f w').length % (K + 1) := by
    set r : Fin (K + 1) := ⟨(f w).length % (K + 1), Nat.mod_lt _ (by omega)⟩ with hr
    have hin : [] ∈ (modPre f K (r : ℕ)).leftQuotient w :=
      (hmod [] r).2 (by simp only [List.append_nil, hr])
    rw [h1 r] at hin
    have hval := (hmod' [] r).1 hin
    simpa [hr] using hval.symm
  -- hence the two derivatives have the same length
  have hlenEq : (deriv f w a).length = (deriv f w' a).length := by
    have hA : ((f w).length + (deriv f w a).length) % (K + 1)
        = ((f w').length + (deriv f w' a).length) % (K + 1) := by rw [hlen, hlen']; exact key1
    have hcancel : ((f w).length + (deriv f w a).length) ≡
        ((f w).length + (deriv f w' a).length) [MOD K + 1] := by
      calc ((f w).length + (deriv f w a).length) ≡
          ((f w').length + (deriv f w' a).length) [MOD K + 1] := hA
        _ ≡ ((f w).length + (deriv f w' a).length) [MOD K + 1] := Nat.ModEq.add_right _ key0.symm
    have hmodeq : (deriv f w a).length ≡ (deriv f w' a).length [MOD K + 1] :=
      Nat.ModEq.add_left_cancel' _ hcancel
    have e1 : (deriv f w a).length % (K + 1) = (deriv f w a).length :=
      Nat.mod_eq_of_lt (by omega)
    have e2 : (deriv f w' a).length % (K + 1) = (deriv f w' a).length :=
      Nat.mod_eq_of_lt (by omega)
    rw [← e1, ← e2]
    exact hmodeq
  -- and are equal, because they are suffixes of the same string
  have hsuf : deriv f w a <:+ f (w' ++ [a]) := by
    have hin : [a] ∈ (sufPre f (deriv f w a)).leftQuotient w := by
      rw [Language.mem_leftQuotient]
      exact ⟨f w, hd⟩
    rw [show (sufPre f (deriv f w a)) = (sufPre f (⟨deriv f w a, hdK⟩ : Short B K).val) from rfl,
      h2 ⟨deriv f w a, hdK⟩, Language.mem_leftQuotient] at hin
    exact hin
  rw [← hd'] at hsuf
  rw [List.suffix_iff_eq_drop.1 hsuf]
  simp [hlenEq]

open Classical in
/-- The canonical sequential transducer of `f`. -/
noncomputable def seqTransducer : Sequential A B (Set.range (state f K)) where
  init := ⟨state f K [], ⟨[], rfl⟩⟩
  step := fun s a =>
    (⟨(fun r => (s.val.1 r).leftQuotient [a], fun u => (s.val.2 u).leftQuotient [a]), by
        obtain ⟨w, hw⟩ := s.2
        exact ⟨w ++ [a], by rw [state_append, hw]⟩⟩,
      deriv f s.2.choose a)

lemma seqTransducer_state (w : List A) :
    (strTrans (seqTransducer f K).transFun w (seqTransducer f K).init).val = state f K w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      set s := strTrans (seqTransducer f K).transFun w (seqTransducer f K).init with hsdef
      have hs : strTrans (seqTransducer f K).transFun (w ++ [a]) (seqTransducer f K).init
          = (seqTransducer f K).transFun s a := by
        simp [hsdef, strTrans, List.foldl_append]
      have hval : ((seqTransducer f K).transFun s a).val
          = (fun r => ((s.val).1 r).leftQuotient [a],
              fun u => ((s.val).2 u).leftQuotient [a]) := rfl
      rw [hs, hval, ih, state_append]

lemma seqTransducer_eval (hpre : PrefixPreserving f) (hnil : f [] = [])
    (hK : ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K) :
    (seqTransducer f K).eval = f := by
  funext w
  induction w using List.reverseRecOn with
  | nil => simpa [Sequential.eval] using hnil.symm
  | append_singleton w a ih =>
      rw [Sequential.eval_append, ih]
      set s := strTrans (seqTransducer f K).transFun w (seqTransducer f K).init with hsdef
      have hrun : (seqTransducer f K).run s [a] = deriv f s.2.choose a := by
        simp [Sequential.run, seqTransducer]
      have hstate : state f K s.2.choose = state f K w := by
        rw [s.2.choose_spec, seqTransducer_state f K w]
      rw [hrun, deriv_eq_of_state_eq f K hpre hK hstate a, append_deriv f hpre w a]

end SeqChar

/-- **Theorem `thm:sequential-function-independent`.**  A function is sequential if and only if its
value on the empty input is empty and it is continuous, prefix preserving, and has the bounded
increase property.

The condition `f [] = []` is missing from the statement in the book; it is
necessary, since a sequential transducer produces no output before reading any
input. -/
theorem isSequential_iff_aux {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSequential f ↔
      (f [] = [] ∧ Continuous f ∧ PrefixPreserving f ∧
        ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K) := by
  constructor
  · intro hf
    exact ⟨hf.nil, hf.continuous, hf.prefixPreserving, hf.boundedIncrease⟩
  · rintro ⟨hnil, hcont, hpre, K, hK⟩
    exact ⟨Set.range (SeqChar.state f K), (SeqChar.state_range_finite f K hcont).to_subtype,
      SeqChar.seqTransducer f K, SeqChar.seqTransducer_eval f K hpre hnil hK⟩

end Lax132576Proofs.Transducers
