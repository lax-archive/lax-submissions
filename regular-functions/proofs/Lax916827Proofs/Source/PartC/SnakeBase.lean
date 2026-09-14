/-
The base of the induction on the width in the book's snake lemma (the lemma
"the output of a snake graph is regular", which is the missing half of
Theorem `thm:2dfa-decomposition-into-primes` of *Transducers*, M. Bojańczyk).

The snake lemma says that for every two-way transducer `M` and every `k`, the
function `TwoWay.widthOut M k` -- the output of the run of `M` on the inputs
whose run visits every column at most `k` times, and the empty string on all
other inputs -- is regular.  The book proves it by induction on `k`.  This file
proves the two base cases:

* `TwoWay.widthOut_zero_isRegular`: the width of a run is never `0`, because the
  initial configuration already visits the leftmost column, so the width-`0`
  output function is constantly empty.
* `TwoWay.widthOut_one_isRegular`: a halting run of width `1` never moves left,
  because a leftward step would revisit the column that the run has just come
  from.  A run that only moves right is simulated by a left-to-right pass over
  the input, and its output is therefore produced by a bimachine, hence by a
  rational function (Theorem `thm:bimachines`).  The inputs for which the run is such a
  pass form a regular language `TwoWay.PassLang M`, recognised by the automaton
  that performs the simulation, so the case distinction between them and the
  remaining inputs -- on which the width-`1` output is empty -- is available
  from `isRationalFun_ite_lang`.

The remaining case of the induction, `k ≥ 2`, is stated in
`RequestProject/PartC/SnakeReg.lean`.
-/
import Lax916827Proofs.Source.PartC.SnakeWidth
import Lax916827Proofs.Source.PartC.RatTools
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-! ## The left-to-right simulation of a run that only moves right -/

/-- The state of the left-to-right simulation of the run of a two-way
transducer: either the run is still going, and we remember the previous input
letter and the current state (`Sum.inl`), or the run has already halted
(`Sum.inr true`), or it has moved to the left or got stuck (`Sum.inr false`). -/
abbrev PassSt (A₀ Q₀ : Type) := (Option A₀ × Q₀) ⊕ Bool

/-- The output produced by one transition of a two-way transducer. -/
def stepOut : List B ⊕ (Q × List B × Bool) → List B
  | Sum.inl o => o
  | Sum.inr (_, o, _) => o

section Pass

variable (M : TwoWay A B Q)

/-- One step of the left-to-right simulation. -/
def passStep : PassSt A Q → A → PassSt A Q
  | Sum.inl (prev, q), a =>
      match M.step prev q (some a) with
      | Sum.inl _ => Sum.inr true
      | Sum.inr (q', _, true) => Sum.inl (some a, q')
      | Sum.inr (_, _, false) => Sum.inr false
  | Sum.inr b, _ => Sum.inr b

/-- The initial state of the left-to-right simulation. -/
def passInit : PassSt A Q := Sum.inl (none, M.init)

/-- The simulation succeeds: either the run has already halted, or it halts at
the right end of the input. -/
def passAccB : PassSt A Q → Bool
  | Sum.inl (prev, q) => (M.step prev q none).isLeft
  | Sum.inr b => b

@[simp] lemma passStep_inr (b : Bool) (a : A) : passStep M (Sum.inr b) a = Sum.inr b := rfl

lemma passStep_halt {prev : Option A} {q : Q} {a : A} {o : List B}
    (h : M.step prev q (some a) = Sum.inl o) :
    passStep M (Sum.inl (prev, q)) a = Sum.inr true := by
  simp [passStep, h]

lemma passStep_right {prev : Option A} {q q' : Q} {a : A} {o : List B}
    (h : M.step prev q (some a) = Sum.inr (q', o, true)) :
    passStep M (Sum.inl (prev, q)) a = Sum.inl (some a, q') := by
  simp [passStep, h]

lemma passStep_left {prev : Option A} {q q' : Q} {a : A} {o : List B}
    (h : M.step prev q (some a) = Sum.inr (q', o, false)) :
    passStep M (Sum.inl (prev, q)) a = Sum.inr false := by
  simp [passStep, h]

private lemma strTrans_app {S : Type} (δ : S → A → S) (x y : List A) (s : S) :
    strTrans δ (x ++ y) s = strTrans δ y (strTrans δ x s) := by
  simp [strTrans]

private lemma strTrans_getLast (v : List A) : ∀ s : Option A,
    strTrans (fun (_ : Option A) (a : A) => some a) v s = if v = [] then s else v.getLast? := by
  induction v with
  | nil => intro s; simp [strTrans]
  | cons a v ih =>
      intro s
      have h : strTrans (fun (_ : Option A) (a : A) => some a) (a :: v) s
          = strTrans (fun (_ : Option A) (a : A) => some a) v (some a) := by simp [strTrans]
      rw [h, ih]
      cases v with
      | nil => simp
      | cons b v => simp

variable (w : List A)

/-- The state of the left-to-right simulation after the first `i` letters. -/
def passAt (i : ℕ) : PassSt A Q := strTrans (passStep M) (w.take i) (passInit M)

@[simp] lemma passAt_zero : passAt M w 0 = Sum.inl (none, M.init) := by
  simp [passAt, strTrans, passInit]

lemma passAt_succ {i : ℕ} (hi : i < w.length) :
    passAt M w (i + 1) = passStep M (passAt M w i) (w[i]'hi) := by
  have h1 : w.take (i + 1) = w.take i ++ [w[i]'hi] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  unfold passAt
  rw [h1, strTrans_app]
  simp [strTrans]

private lemma strTrans_passStep_inr (b : Bool) (v : List A) :
    strTrans (passStep M) v (Sum.inr b) = Sum.inr b := by
  induction v with
  | nil => rfl
  | cons a v ih => simpa [strTrans] using ih

lemma passAt_inr_mono {i j : ℕ} (hij : i ≤ j) {b : Bool} (h : passAt M w i = Sum.inr b) :
    passAt M w j = Sum.inr b := by
  have htake : w.take j = w.take i ++ (w.drop i).take (j - i) := by
    conv_lhs => rw [show j = i + (j - i) by omega]
    exact List.take_add
  unfold passAt at h ⊢
  rw [htake, strTrans_app, h, strTrans_passStep_inr]

lemma passAt_length : passAt M w w.length = strTrans (passStep M) w (passInit M) := by
  simp [passAt]

/-- The language of the inputs on which the run of `M` is a left-to-right pass
that halts. -/
def PassLang : Language A := {w | passAccB M (strTrans (passStep M) w (passInit M)) = true}

/-- The deterministic automaton performing the left-to-right simulation. -/
def passDFA : DFA A (PassSt A Q) where
  step := passStep M
  start := passInit M
  accept := {s | passAccB M s = true}

lemma passLang_isRegular [Finite A] [Finite Q] : (PassLang M).IsRegular := by
  classical
  haveI : Fintype (PassSt A Q) := Fintype.ofFinite _
  refine ⟨PassSt A Q, inferInstance, passDFA M, ?_⟩
  ext v
  rw [DFA.mem_accepts]
  exact Iff.rfl

/-- The bimachine that computes the output of a left-to-right pass. -/
def passBim : Bimachine A B (PassSt A Q) (Option A) where
  prefixInit := passInit M
  prefixStep := passStep M
  suffixInit := none
  suffixStep := fun _ a => some a
  out := fun p s =>
    match p with
    | Sum.inl (prev, q) => stepOut (M.step prev q s)
    | Sum.inr _ => []

private lemma passBim_suffix (i : ℕ) :
    strTrans (passBim M).suffixStep ((w.drop i).reverse) (passBim M).suffixInit
      = (w.drop i).head? := by
  show strTrans (fun (_ : Option A) (a : A) => some a) ((w.drop i).reverse) none = _
  rw [strTrans_getLast]
  by_cases h : (w.drop i).reverse = []
  · have h' : w.drop i = [] := by simpa using h
    rw [if_pos h, h']
    rfl
  · rw [if_neg h]
    simp

lemma passBim_eval :
    (passBim M).eval w =
      ((List.range (w.length + 1)).map (fun i =>
        (passBim M).out (passAt M w i) ((w.drop i).head?))).flatten := by
  rw [Bimachine.eval]
  refine congrArg List.flatten (List.map_congr_left (fun i _ => ?_))
  exact congrArg _ (passBim_suffix M w i)

/-! ## The configurations of a left-to-right pass -/

lemma posAt_of_cfgAt_conf {t : ℕ} {u v : List A} {q : Q}
    (h : cfgAt M w t = some (Cfg.conf u q v)) : posAt M w t = some u.length := by
  simp [posAt, h]

/-- While the simulation is still going, it describes the run. -/
lemma cfgAt_of_passAt : ∀ i : ℕ, i ≤ w.length → ∀ {prev : Option A} {q : Q},
    passAt M w i = Sum.inl (prev, q) →
      prev = (w.take i).getLast? ∧ cfgAt M w i = some (Cfg.conf (w.take i) q (w.drop i)) := by
  intro i
  induction i with
  | zero =>
      intro _ prev q h
      rw [passAt_zero] at h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | succ i ih =>
      intro hi prev q h
      have hilt : i < w.length := by omega
      rw [passAt_succ M w hilt] at h
      rcases hp : passAt M w i with ⟨prev0, q0⟩ | b
      · rw [hp] at h
        obtain ⟨hprev0, hcfg0⟩ := ih (le_of_lt hilt) hp
        subst hprev0
        rcases hs : M.step (w.take i).getLast? q0 (some (w[i]'hilt)) with o | ⟨q', o, dir⟩
        · rw [passStep_halt M hs] at h; exact absurd h (by simp)
        · cases dir with
          | false => rw [passStep_left M hs] at h; exact absurd h (by simp)
          | true =>
              rw [passStep_right M hs] at h
              simp only [Sum.inl.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hdrop : w.drop i = (w[i]'hilt) :: w.drop (i + 1) :=
                List.drop_eq_getElem_cons hilt
              have htake : w.take (i + 1) = w.take i ++ [w[i]'hilt] := by
                rw [List.take_add_one, List.getElem?_eq_getElem hilt]; rfl
              have hs2 : M.step (w.take i).getLast? q0
                  (((w[i]'hilt) :: w.drop (i + 1)).head?) = Sum.inr (q', o, true) := hs
              have hstep := stepCfg_right_cons M hs2
              have hcfg1 : cfgAt M w (i + 1)
                  = some (Cfg.conf (w.take i ++ [w[i]'hilt]) q' (w.drop (i + 1))) := by
                refine cfgAt_succ_of_step M w ?_ hstep
                rw [hcfg0, hdrop]
              refine ⟨?_, ?_⟩
              · rw [htake, List.getLast?_concat]
              · rw [htake]; exact hcfg1
      · rw [hp] at h
        exact absurd h (by simp)

/-- The output of a step of the run, read off the transition function. -/
lemma outAt_eq_stepOut {t : ℕ} {u v : List A} {q : Q}
    (hc : cfgAt M w t = some (Cfg.conf u q v)) (hne : cfgAt M w (t + 1) ≠ none) :
    outAt M w t = stepOut (M.step u.getLast? q v.head?) := by
  rcases hstep : M.stepCfg (Cfg.conf u q v) with _ | ⟨o, c'⟩
  · exact absurd (by rw [cfgAt_succ, hc]; simp [hstep]) hne
  · rw [outAt_of_step M w hc hstep]
    rcases hs : M.step u.getLast? q v.head? with o' | ⟨q', o', dir⟩
    · rw [stepCfg_halt_eq M hs] at hstep
      simp only [Option.some.injEq, Prod.mk.injEq] at hstep
      exact hstep.1.symm
    · cases dir with
      | true =>
          rcases v with _ | ⟨a, v'⟩
          · rw [stepCfg_right_nil M hs] at hstep; exact absurd hstep (by simp)
          · rw [stepCfg_right_cons M hs] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            exact hstep.1.symm
      | false =>
          rcases hu : u.getLast? with _ | a
          · rw [stepCfg_left_none M hu hs] at hstep; exact absurd hstep (by simp)
          · rw [stepCfg_left_some M hu hs] at hstep
            simp only [Option.some.injEq, Prod.mk.injEq] at hstep
            exact hstep.1.symm

/-! ## The two directions of the case distinction -/

/-- If the simulation reaches the state `Sum.inr b`, it does so for the first
time after some letter, and until then it is still going. -/
lemma exists_first_inr {b : Bool} {n : ℕ} (h : ∃ i, i ≤ n ∧ passAt M w i = Sum.inr b) :
    ∃ j, j < n ∧ passAt M w (j + 1) = Sum.inr b ∧
      ∀ i ≤ j, ∃ prev q, passAt M w i = Sum.inl (prev, q) := by
  classical
  have hex : ∃ i, passAt M w i = Sum.inr b := by
    obtain ⟨i, _, hi⟩ := h; exact ⟨i, hi⟩
  obtain ⟨i0, hi0n, hi0⟩ := h
  have hfind : passAt M w (Nat.find hex) = Sum.inr b := Nat.find_spec hex
  have hle : Nat.find hex ≤ n := le_trans (Nat.find_le hi0) hi0n
  have hne0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, passAt_zero] at hfind
    exact absurd hfind (by simp)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨j, by omega, by rw [← hj]; exact hfind, ?_⟩
  intro i hij
  have hlt : i < Nat.find hex := by omega
  have hmin : ¬ passAt M w i = Sum.inr b := Nat.find_min hex hlt
  rcases hp : passAt M w i with ⟨prev, q⟩ | b'
  · exact ⟨prev, q, rfl⟩
  · exfalso
    have hmono := passAt_inr_mono M w (le_of_lt hlt) hp
    rw [hfind] at hmono
    simp only [Sum.inr.injEq] at hmono
    exact hmin (by rw [hp, hmono])

/-- On an input of `PassLang M`, the run of `M` is a left-to-right pass that
halts at some time `T ≤ |w| + 1`. -/
lemma pass_halt (h : w ∈ PassLang M) :
    ∃ T, T ≤ w.length + 1 ∧ cfgAt M w T = some Cfg.halt ∧
      (∀ i < T, ∃ prev q, passAt M w i = Sum.inl (prev, q)) ∧
      (∀ i, T ≤ i → i ≤ w.length → passAt M w i = Sum.inr true) := by
  classical
  by_cases hA : ∃ i, i ≤ w.length ∧ passAt M w i = Sum.inr true
  · obtain ⟨j, hjn, hj1, hj2⟩ := exists_first_inr M w hA
    obtain ⟨prev, q, hpq⟩ := hj2 j (le_refl j)
    obtain ⟨hprev, hcfg⟩ := cfgAt_of_passAt M w j (le_of_lt hjn) hpq
    have hj1' := hj1
    rw [passAt_succ M w hjn, hpq] at hj1'
    have hh : (w.drop j).head? = some (w[j]'hjn) := by
      rw [List.drop_eq_getElem_cons hjn]; rfl
    rcases hs : M.step prev q (some (w[j]'hjn)) with o | ⟨q', o, dir⟩
    · have hs2 : M.step (w.take j).getLast? q ((w.drop j).head?) = Sum.inl o := by
        rw [hh, ← hprev]; exact hs
      have hstep := stepCfg_halt_eq M hs2
      refine ⟨j + 1, by omega, cfgAt_succ_of_step M w hcfg hstep, ?_, ?_⟩
      · intro i hi; exact hj2 i (by omega)
      · intro i hi _; exact passAt_inr_mono M w hi hj1
    · exfalso
      cases dir with
      | true => rw [passStep_right M hs] at hj1'; exact absurd hj1' (by simp)
      | false => rw [passStep_left M hs] at hj1'; exact absurd hj1' (by simp)
  · push_neg at hA
    have hlast : ∃ prev q, passAt M w w.length = Sum.inl (prev, q) := by
      rcases hp : passAt M w w.length with ⟨prev, q⟩ | b'
      · exact ⟨prev, q, rfl⟩
      · exfalso
        cases b' with
        | true => exact absurd hp (hA w.length (le_refl _))
        | false =>
            change passAccB M (strTrans (passStep M) w (passInit M)) = true at h
            rw [← passAt_length, hp] at h
            exact absurd h (by simp [passAccB])
    obtain ⟨prev, q, hpq⟩ := hlast
    obtain ⟨hprev, hcfg⟩ := cfgAt_of_passAt M w w.length (le_refl _) hpq
    change passAccB M (strTrans (passStep M) w (passInit M)) = true at h
    rw [← passAt_length, hpq] at h
    simp only [passAccB] at h
    have hdrop : w.drop w.length = ([] : List A) := by simp
    rcases hs : M.step prev q none with o | ⟨q', o, dir⟩
    · have hs2 : M.step (w.take w.length).getLast? q ((w.drop w.length).head?) = Sum.inl o := by
        rw [hdrop, ← hprev]; exact hs
      have hstep := stepCfg_halt_eq M hs2
      refine ⟨w.length + 1, le_refl _, cfgAt_succ_of_step M w hcfg hstep, ?_, ?_⟩
      · intro i hi
        have hile : i ≤ w.length := by omega
        rcases hp : passAt M w i with ⟨prev', q''⟩ | b'
        · exact ⟨prev', q'', rfl⟩
        · exfalso
          have hmono := passAt_inr_mono M w hile hp
          rw [hpq] at hmono
          exact absurd hmono (by simp)
      · intro i hi _; omega
    · exfalso; rw [hs] at h; simp at h

/-- On an input of `PassLang M`, the run has width one. -/
lemma widthLe_one_of_pass (h : w ∈ PassLang M) : WidthLe M w 1 := by
  classical
  obtain ⟨T, hTle, hThalt, hinl, -⟩ := pass_halt M w h
  intro x s hs
  have hkey : ∀ t ∈ s, t = x := by
    intro t ht
    have hpos := hs t ht
    by_cases htT : t < T
    · obtain ⟨prev, q, hpq⟩ := hinl t htT
      obtain ⟨-, hcfg⟩ := cfgAt_of_passAt M w t (by omega) hpq
      rw [posAt_of_cfgAt_conf M w hcfg] at hpos
      simp only [Option.some.injEq] at hpos
      rw [← hpos, List.length_take]
      omega
    · exfalso
      have hnone : posAt M w t = none := by
        rcases Nat.lt_or_ge T t with hlt | hge
        · have h1 : cfgAt M w (T + 1) = none := cfgAt_halt_succ M w hThalt
          have h2 : cfgAt M w t = none := cfgAt_none_mono M w (by omega) h1
          simp [posAt, h2]
        · have hTt : t = T := by omega
          subst hTt
          simp [posAt, hThalt]
      rw [hnone] at hpos
      exact absurd hpos (by simp)
  have hsub : s ⊆ {x} := by
    intro t ht
    simp only [Finset.mem_singleton]
    exact hkey t ht
  simpa using Finset.card_le_card hsub

private lemma flatten_map_range_eq {C : Type} (g : ℕ → List C) (T : ℕ) :
    ∀ m : ℕ, T ≤ m → (∀ i, T ≤ i → i < m → g i = []) →
      ((List.range m).map g).flatten = ((List.range T).map g).flatten := by
  intro m
  induction m with
  | zero =>
      intro hTm _
      have hT : T = 0 := by omega
      rw [hT]
  | succ m ih =>
      intro hTm hz
      rcases Nat.lt_or_ge m T with hlt | hge
      · have hT : T = m + 1 := by omega
        rw [hT]
      · rw [List.range_succ, List.map_append, List.flatten_append]
        simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
          hz m hge (Nat.lt_succ_self m), List.append_nil]
        exact ih hge (fun i h1 h2 => hz i h1 (by omega))

lemma runOut_eq_outRange_of_halt {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) :
    runOut M w = outRange M w 0 T := by
  classical
  have hex : ∃ T, cfgAt M w T = some Cfg.halt := ⟨T, hT⟩
  rw [runOut, dif_pos hex, halt_time_unique M w hex.choose_spec hT]

/-- On an input of `PassLang M`, the output of the run is the output of the
bimachine. -/
lemma runOut_eq_passBim (h : w ∈ PassLang M) : runOut M w = (passBim M).eval w := by
  classical
  obtain ⟨T, hTle, hThalt, hinl, hinr⟩ := pass_halt M w h
  rw [runOut_eq_outRange_of_halt M w hThalt, passBim_eval M w, outRange]
  have hg : ∀ i, T ≤ i → i < w.length + 1 →
      (passBim M).out (passAt M w i) ((w.drop i).head?) = [] := by
    intro i h1 h2
    rw [hinr i h1 (by omega)]
    rfl
  rw [flatten_map_range_eq _ T (w.length + 1) (by omega) hg]
  simp only [Nat.sub_zero, ← List.range_eq_range']
  refine congrArg List.flatten (List.map_congr_left (fun i hi => ?_))
  rw [List.mem_range] at hi
  obtain ⟨prev, q, hpq⟩ := hinl i hi
  obtain ⟨hprev, hcfg⟩ := cfgAt_of_passAt M w i (by omega) hpq
  have hne : cfgAt M w (i + 1) ≠ none := by
    intro hnone
    have hn : cfgAt M w T = none := cfgAt_none_mono M w (by omega) hnone
    rw [hThalt] at hn
    exact absurd hn (by simp)
  rw [outAt_eq_stepOut M w hcfg hne, hpq, ← hprev]
  rfl

/-- Off `PassLang M`, the width-one output is empty. -/
lemma widthOut_one_of_not_pass (h : w ∉ PassLang M) : widthOut M 1 w = [] := by
  classical
  have hnowidth : ∀ {t t' x : ℕ}, t ≠ t' → posAt M w t = some x → posAt M w t' = some x →
      widthOut M 1 w = [] := by
    intro t t' x hne ht ht'
    have hW : ¬ WidthLe M w 1 := by
      intro hW
      have hcard := hW x {t, t'} (by
        intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu'
        · exact ht
        · rw [Finset.mem_singleton] at hu'; subst hu'; exact ht')
      rw [Finset.card_pair hne] at hcard
      omega
    rw [widthOut, if_neg hW]
  have hnohalt : (∀ T, cfgAt M w T ≠ some Cfg.halt) → widthOut M 1 w = [] := by
    intro hno
    have hr : runOut M w = [] := by
      rw [runOut, dif_neg]
      rintro ⟨T, hT⟩
      exact hno T hT
    rw [widthOut]
    split <;> simp [hr]
  by_cases hA : ∃ i, i ≤ w.length ∧ passAt M w i = Sum.inr false
  · obtain ⟨j, hjn, hj1, hj2⟩ := exists_first_inr M w hA
    obtain ⟨prev, q, hpq⟩ := hj2 j (le_refl j)
    obtain ⟨hprev, hcfg⟩ := cfgAt_of_passAt M w j (le_of_lt hjn) hpq
    have hj1' := hj1
    rw [passAt_succ M w hjn, hpq] at hj1'
    have hh : (w.drop j).head? = some (w[j]'hjn) := by
      rw [List.drop_eq_getElem_cons hjn]; rfl
    rcases hs : M.step prev q (some (w[j]'hjn)) with o | ⟨q', o, dir⟩
    · rw [passStep_halt M hs] at hj1'; exact absurd hj1' (by simp)
    · cases dir with
      | true => rw [passStep_right M hs] at hj1'; exact absurd hj1' (by simp)
      | false =>
          have hs' : M.step (w.take j).getLast? q ((w.drop j).head?) = Sum.inr (q', o, false) := by
            rw [hh, ← hprev]; exact hs
          rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · -- the run steps off the left end and gets stuck
            subst hj0
            refine hnohalt (fun T hT => ?_)
            have hu : (w.take 0).getLast? = none := by simp
            have hstuck : M.stepCfg (Cfg.conf ([] : List A) q w) = none := by
              simpa using stepCfg_left_none M hu hs'
            have h1 : cfgAt M w (0 + 1) = none := by
              rw [cfgAt_succ, hcfg]; simp [hstuck]
            rcases Nat.eq_zero_or_pos T with hT0 | hTpos
            · subst hT0
              rw [cfgAt_zero] at hT; exact absurd hT (by simp)
            · have hn := cfgAt_none_mono M w (show 0 + 1 ≤ T by omega) h1
              rw [hT] at hn; exact absurd hn (by simp)
          · -- the run steps back to a column that it has already visited
            have hnil : w.take j ≠ [] := by
              intro hc
              have hlen : (w.take j).length = 0 := by rw [hc]; rfl
              rw [List.length_take] at hlen
              omega
            obtain ⟨a, ha⟩ : ∃ a, (w.take j).getLast? = some a := by
              rcases hg : (w.take j).getLast? with _ | a
              · exact absurd (by simpa using hg) hnil
              · exact ⟨a, rfl⟩
            have hstep := stepCfg_left_some M ha hs'
            have hcfg1 : cfgAt M w (j + 1)
                = some (Cfg.conf (w.take j).dropLast q' (a :: w.drop j)) :=
              cfgAt_succ_of_step M w hcfg hstep
            obtain ⟨prev0, q0, hpq0⟩ := hj2 (j - 1) (by omega)
            obtain ⟨-, hcfg0⟩ := cfgAt_of_passAt M w (j - 1) (by omega) hpq0
            refine hnowidth (t := j - 1) (t' := j + 1) (x := j - 1) (by omega) ?_ ?_
            · rw [posAt_of_cfgAt_conf M w hcfg0, List.length_take]
              congr 1
              omega
            · rw [posAt_of_cfgAt_conf M w hcfg1, List.length_dropLast, List.length_take]
              congr 1
              omega
  · push_neg at hA
    have hlast : ∃ prev q, passAt M w w.length = Sum.inl (prev, q) := by
      rcases hp : passAt M w w.length with ⟨prev, q⟩ | b'
      · exact ⟨prev, q, rfl⟩
      · exfalso
        cases b' with
        | false => exact absurd hp (hA w.length (le_refl _))
        | true =>
            apply h
            change passAccB M (strTrans (passStep M) w (passInit M)) = true
            rw [← passAt_length, hp]
            rfl
    obtain ⟨prev, q, hpq⟩ := hlast
    obtain ⟨hprev, hcfg⟩ := cfgAt_of_passAt M w w.length (le_refl _) hpq
    have hnotacc : passAccB M (passAt M w w.length) ≠ true := by
      intro hc
      exact h (by change passAccB M (strTrans (passStep M) w (passInit M)) = true; rw [← passAt_length]; exact hc)
    rw [hpq] at hnotacc
    simp only [passAccB] at hnotacc
    have htake : w.take w.length = w := by simp
    have hdrop : w.drop w.length = ([] : List A) := by simp
    have hprev' : prev = w.getLast? := by rw [hprev, htake]
    rw [htake, hdrop] at hcfg
    rcases hs : M.step prev q none with o | ⟨q', o, dir⟩
    · rw [hs] at hnotacc; simp at hnotacc
    · have hs2 : M.step w.getLast? q (([] : List A).head?) = Sum.inr (q', o, dir) := by
        rw [← hprev']; exact hs
      cases dir with
      | true =>
          refine hnohalt (fun T hT => ?_)
          have hstuck : M.stepCfg (Cfg.conf w q []) = none := stepCfg_right_nil M hs2
          have h1 : cfgAt M w (w.length + 1) = none := by
            rw [cfgAt_succ, hcfg]; simp [hstuck]
          have hle : ∀ t ≤ w.length, cfgAt M w t ≠ some Cfg.halt := by
            intro t ht
            obtain ⟨prev', q'', hpq'⟩ : ∃ prev' q'', passAt M w t = Sum.inl (prev', q'') := by
              rcases hp : passAt M w t with ⟨prev', q''⟩ | b'
              · exact ⟨prev', q'', rfl⟩
              · exfalso
                have hmono := passAt_inr_mono M w ht hp
                rw [hpq] at hmono
                exact absurd hmono (by simp)
            obtain ⟨-, hc⟩ := cfgAt_of_passAt M w t ht hpq'
            rw [hc]
            simp
          rcases Nat.lt_or_ge w.length T with hlt | hge
          · have hn := cfgAt_none_mono M w (show w.length + 1 ≤ T by omega) h1
            rw [hT] at hn; exact absurd hn (by simp)
          · exact hle T hge hT
      | false =>
          rcases Nat.eq_zero_or_pos w.length with hz | hpos
          · refine hnohalt (fun T hT => ?_)
            have hwnil : w = [] := by simpa using hz
            have hu : w.getLast? = none := by rw [hwnil]; rfl
            have hstuck : M.stepCfg (Cfg.conf w q []) = none := stepCfg_left_none M hu hs2
            have h1 : cfgAt M w (w.length + 1) = none := by
              rw [cfgAt_succ, hcfg]; simp [hstuck]
            rcases Nat.lt_or_ge w.length T with hlt | hge
            · have hn := cfgAt_none_mono M w (show w.length + 1 ≤ T by omega) h1
              rw [hT] at hn; exact absurd hn (by simp)
            · have hT0 : T = 0 := by omega
              subst hT0
              rw [cfgAt_zero] at hT; exact absurd hT (by simp)
          · obtain ⟨a, ha⟩ : ∃ a, w.getLast? = some a := by
              rcases hg : w.getLast? with _ | a
              · exfalso
                have hwnil : w = [] := by simpa using hg
                rw [hwnil] at hpos
                simp at hpos
              · exact ⟨a, rfl⟩
            have hstep := stepCfg_left_some M ha hs2
            have hcfg1 : cfgAt M w (w.length + 1)
                = some (Cfg.conf w.dropLast q' (a :: [])) :=
              cfgAt_succ_of_step M w hcfg hstep
            obtain ⟨prev0, q0, hpq0⟩ : ∃ prev0 q0,
                passAt M w (w.length - 1) = Sum.inl (prev0, q0) := by
              rcases hp : passAt M w (w.length - 1) with ⟨prev0, q0⟩ | b'
              · exact ⟨prev0, q0, rfl⟩
              · exfalso
                have hmono := passAt_inr_mono M w (show w.length - 1 ≤ w.length by omega) hp
                rw [hpq] at hmono
                exact absurd hmono (by simp)
            obtain ⟨-, hcfg0⟩ := cfgAt_of_passAt M w (w.length - 1) (by omega) hpq0
            refine hnowidth (t := w.length - 1) (t' := w.length + 1) (x := w.length - 1)
              (by omega) ?_ ?_
            · rw [posAt_of_cfgAt_conf M w hcfg0, List.length_take]
              congr 1
              omega
            · rw [posAt_of_cfgAt_conf M w hcfg1, List.length_dropLast]

end Pass

/-! ## The base cases of the snake lemma -/

open scoped Classical in
/-- The width-one output function of a two-way transducer, as a case
distinction over `PassLang M`. -/
theorem widthOut_one_eq (M : TwoWay A B Q) (w : List A) :
    widthOut M 1 w = if w ∈ PassLang M then (passBim M).eval w else [] := by
  classical
  by_cases h : w ∈ PassLang M
  · rw [if_pos h, widthOut, if_pos (widthLe_one_of_pass M w h), runOut_eq_passBim M w h]
  · rw [if_neg h]
    exact widthOut_one_of_not_pass M w h

/-- **The base case of the snake lemma.**  The width-one output function of a
two-way transducer is rational, hence regular: a halting run of width one only
moves right, so it is a left-to-right pass over the input. -/
theorem widthOut_one_isRegular [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) :
    IsRegularFun (widthOut M 1) := by
  classical
  have hrat : IsRationalFun (fun w : List A =>
      if w ∈ PassLang M then (passBim M).eval w else []) :=
    isRationalFun_ite_lang (passLang_isRegular M)
      (isRationalFun_of_bimachine (passBim M) (fun _ => rfl))
      (isRationalFun_const [])
  exact (IsRegularFun.of_rational hrat).congr (fun w => (widthOut_one_eq M w).symm)

/-- The width of a run is never zero: the initial configuration already visits
the leftmost column. -/
theorem not_widthLe_zero (M : TwoWay A B Q) (w : List A) : ¬ WidthLe M w 0 := by
  intro h
  have h0 : posAt M w 0 = some 0 := by simp [posAt]
  have hc := h 0 {0} (by intro t ht; rw [Finset.mem_singleton] at ht; subst ht; exact h0)
  simp at hc

/-- The width-zero output function is constantly empty, hence regular. -/
theorem widthOut_zero_isRegular [Finite A] [Finite B] (M : TwoWay A B Q) :
    IsRegularFun (widthOut M 0) := by
  classical
  have h : ∀ w : List A, ((fun _ : List A => ([] : List B)) w) = widthOut M 0 w := by
    intro w
    rw [widthOut, if_neg (not_widthLe_zero M w)]
  exact (IsRegularFun.of_rational (isRationalFun_const [])).congr h

end TwoWay

end Lax916827Proofs.Transducers
