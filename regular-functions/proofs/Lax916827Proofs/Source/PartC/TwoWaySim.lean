/-
Simulating a coded two-way transducer with a fuel bound.

This file supplies the semantic half of what used to be the effectivity hypothesis
`Transducers.EffectiveTwoWayEvalEq` of `RequestProject/PartC/EffectiveReg.lean`: a *concrete*
procedure `Transducers.RegDec.simOut` which, given a code of a two-way transducer and an input
string, returns the output of the coded transducer on that string whenever there is one.  Its
computability is proved in `RequestProject/PartC/TwoWaySimPrimrec.lean`.

The procedure is the obvious one -- run the transducer -- with two points to settle.

* The run has to be carried out on a *first-order* datum, so that it can be shown primitive
  recursive later: a configuration `Cfg ℕ ℕ` is replaced here by an element of
  `Option (List ℕ × ℕ × List ℕ)` (`none` for the halting vertex), and one step of the run by
  `Transducers.RegDec.simStep`, which mirrors `Transducers.TwoWay.stepCfg` case by case.
* A `Computable` procedure is total, so the run must be given a bound in advance.  A halting run of
  a deterministic two-way transducer visits no configuration twice
  (`Transducers.TwoWay.run_inj`), and a configuration that lies on the run of a coded transducer is
  determined by the position of the head -- at most `|w| + 1` values -- and by a state occurring in
  the transition table of the code, or the initial state `0` (`Transducers.RegDec.codeStates`).  So
  a halting run is shorter than `Transducers.RegDec.fuel c w = (|w| + 1) * |codeStates c| + 1`, and
  running the simulation for that many steps is enough.
-/
import Lax916827Proofs.Source.PartC.RegCodeSan
import Lax916827Proofs.Source.PartC.TwoWayCompAux
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegDec

open TwoWay

/-! ## The states of a code -/

/-- The states that can occur on a run of the transducer described by a code: the initial state `0`
and the targets of the transitions of the table. -/
def codeStates (c : TwoWayCode) : List ℕ :=
  0 :: c.flatMap (fun t => match t.2 with | Sum.inl _ => [] | Sum.inr y => [y.1])

lemma zero_mem_codeStates (c : TwoWayCode) : 0 ∈ codeStates c := by
  simp [codeStates]

lemma codeStates_length_pos (c : TwoWayCode) : 0 < (codeStates c).length := by
  simp [codeStates]

lemma lookup_mem {c : TwoWayCode} {k : Option ℕ × ℕ × Option ℕ}
    {x : List ℕ ⊕ (ℕ × List ℕ × Bool)} (h : c.lookup k = some x) : (k, x) ∈ c := by
  induction c with
  | nil => simp [List.lookup] at h
  | cons t c ih =>
      obtain ⟨k', x'⟩ := t
      rw [List.lookup_cons] at h
      by_cases hk : k == k'
      · rw [hk] at h
        simp only at h
        have hkk : k = k' := by simpa using hk
        subst hkk
        simp at h
        subst h
        exact List.mem_cons_self
      · rw [Bool.not_eq_true] at hk
        rw [hk] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- A state that a transition of a code moves to occurs in `codeStates`. -/
lemma target_mem_codeStates {c : TwoWayCode} {l r : Option ℕ} {q q' : ℕ} {o : List ℕ} {d : Bool}
    (h : (twoWayCodeAut c).step l q r = Sum.inr (q', o, d)) : q' ∈ codeStates c := by
  rcases hl : c.lookup (l, q, r) with _ | x
  · simp [twoWayCodeAut, hl] at h
  · simp only [twoWayCodeAut, hl] at h
    subst h
    refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨((l, q, r), Sum.inr (q', o, d)),
      lookup_mem hl, ?_⟩)
    simp

/-! ## The states on a run -/

/-- Every state on the run of a coded transducer occurs in `codeStates`. -/
lemma state_mem_codeStates_of_stepCfg {c : TwoWayCode} {x : Cfg ℕ ℕ} {o : List ℕ}
    {u : List ℕ} {q : ℕ} {v : List ℕ}
    (h : (twoWayCodeAut c).stepCfg x = some (o, Cfg.conf u q v)) : q ∈ codeStates c := by
  cases x with
  | halt => simp [TwoWay.stepCfg] at h
  | conf u₀ q₀ v₀ =>
      rcases hM : (twoWayCodeAut c).step u₀.getLast? q₀ v₀.head? with o' | ⟨q', o', dir⟩
      · rw [stepCfg_halt_eq _ hM] at h
        exact absurd (congrArg Prod.snd (Option.some_injective _ h)) (by simp)
      · have hq' : q' ∈ codeStates c := target_mem_codeStates hM
        cases dir with
        | true =>
            cases v₀ with
            | nil => rw [stepCfg_right_nil _ hM] at h; simp at h
            | cons a v₁ =>
                rw [stepCfg_right_cons _ hM] at h
                have h2 : Cfg.conf (u₀ ++ [a]) q' v₁ = Cfg.conf u q v :=
                  congrArg Prod.snd (Option.some_injective _ h)
                simp only [Cfg.conf.injEq] at h2
                obtain ⟨-, rfl, -⟩ := h2
                exact hq'
        | false =>
            rcases hu : u₀.getLast? with _ | a
            · rw [stepCfg_left_none _ hu hM] at h; simp at h
            · rw [stepCfg_left_some _ hu hM] at h
              have h2 : Cfg.conf u₀.dropLast q' (a :: v₀) = Cfg.conf u q v :=
                congrArg Prod.snd (Option.some_injective _ h)
              simp only [Cfg.conf.injEq] at h2
              obtain ⟨-, rfl, -⟩ := h2
              exact hq'

lemma state_mem_codeStates {c : TwoWayCode} {w : List ℕ} :
    ∀ (t : ℕ) {u : List ℕ} {q : ℕ} {v : List ℕ},
      cfgAt (twoWayCodeAut c) w t = some (Cfg.conf u q v) → q ∈ codeStates c := by
  intro t
  induction t with
  | zero =>
      intro u q v h
      simp only [cfgAt_zero, Option.some.injEq, Cfg.conf.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact zero_mem_codeStates c
  | succ t _ =>
      intro u q v h
      obtain ⟨x, -, hs⟩ := exists_pred _ w h
      exact state_mem_codeStates_of_stepCfg hs

/-! ## The bound on the length of a halting run -/

/-- The number of steps a halting run of a coded transducer may take, plus one. -/
def fuel (c : TwoWayCode) (w : List ℕ) : ℕ := (w.length + 1) * (codeStates c).length + 1

/-- The code of a configuration on the run: the position of the head and the index of the state. -/
private def cfgCode (c : TwoWayCode) : Cfg ℕ ℕ → ℕ
  | Cfg.conf u q _ => u.length * (codeStates c).length + (codeStates c).idxOf q + 1
  | Cfg.halt => 0

private lemma cfgCode_lt {c : TwoWayCode} {w : List ℕ} {t : ℕ} {x : Cfg ℕ ℕ}
    (h : cfgAt (twoWayCodeAut c) w t = some x) : cfgCode c x < fuel c w := by
  cases x with
  | halt => simp [cfgCode, fuel]
  | conf u q v =>
      have hq : q ∈ codeStates c := state_mem_codeStates t h
      have hidx : (codeStates c).idxOf q < (codeStates c).length := List.idxOf_lt_length_of_mem hq
      have huv : u ++ v = w := cfgAt_append _ w t h
      have hlen : u.length ≤ w.length := by
        rw [← huv]; simp
      have : u.length * (codeStates c).length ≤ w.length * (codeStates c).length :=
        Nat.mul_le_mul_right _ hlen
      simp only [cfgCode, fuel]
      have hstep : (w.length + 1) * (codeStates c).length
          = w.length * (codeStates c).length + (codeStates c).length := by ring
      omega

private lemma cfgCode_inj {c : TwoWayCode} {w : List ℕ} {s t : ℕ} {x y : Cfg ℕ ℕ}
    (hx : cfgAt (twoWayCodeAut c) w s = some x) (hy : cfgAt (twoWayCodeAut c) w t = some y)
    (h : cfgCode c x = cfgCode c y) : x = y := by
  cases x with
  | halt =>
      cases y with
      | halt => rfl
      | conf u q v => simp only [cfgCode] at h; omega
  | conf u q v =>
      cases y with
      | halt => simp only [cfgCode] at h; omega
      | conf u' q' v' =>
          have hq : q ∈ codeStates c := state_mem_codeStates s hx
          have hq' : q' ∈ codeStates c := state_mem_codeStates t hy
          have hi : (codeStates c).idxOf q < (codeStates c).length :=
            List.idxOf_lt_length_of_mem hq
          have hi' : (codeStates c).idxOf q' < (codeStates c).length :=
            List.idxOf_lt_length_of_mem hq'
          simp only [cfgCode, add_left_inj] at h
          have hlen : u.length = u'.length ∧
              (codeStates c).idxOf q = (codeStates c).idxOf q' := by
            constructor
            · by_contra hne
              rcases Nat.lt_or_ge u.length u'.length with hlt | hge
              · have : u.length + 1 ≤ u'.length := hlt
                have := Nat.mul_le_mul_right (codeStates c).length this
                simp only [Nat.succ_mul] at this
                omega
              · have hlt : u'.length < u.length := by omega
                have : u'.length + 1 ≤ u.length := hlt
                have := Nat.mul_le_mul_right (codeStates c).length this
                simp only [Nat.succ_mul] at this
                omega
            · by_contra hne
              rcases Nat.lt_or_ge u.length u'.length with hlt | hge
              · have : u.length + 1 ≤ u'.length := hlt
                have := Nat.mul_le_mul_right (codeStates c).length this
                simp only [Nat.succ_mul] at this
                omega
              · rcases Nat.lt_or_ge u'.length u.length with hlt | hge'
                · have : u'.length + 1 ≤ u.length := hlt
                  have := Nat.mul_le_mul_right (codeStates c).length this
                  simp only [Nat.succ_mul] at this
                  omega
                · have : u.length = u'.length := by omega
                  rw [this] at h
                  omega
          obtain ⟨hul, hidx⟩ := hlen
          have hqq : q = q' := by
            have h1 : (codeStates c)[(codeStates c).idxOf q]? = some q :=
              List.getElem?_idxOf hq
            have h2 : (codeStates c)[(codeStates c).idxOf q']? = some q' :=
              List.getElem?_idxOf hq'
            rw [hidx, h2] at h1
            exact (Option.some_injective _ h1).symm
          have huv : u ++ v = w := cfgAt_append _ w s hx
          have huv' : u' ++ v' = w := cfgAt_append _ w t hy
          have huu : u = u' := by
            have := huv.trans huv'.symm
            exact (List.append_inj this hul).1
          have hvv : v = v' := by
            have := huv.trans huv'.symm
            exact (List.append_inj this hul).2
          rw [huu, hqq, hvv]

/-- **A halting run of a coded two-way transducer is short.**  A run that halts visits no
configuration twice, and there are fewer than `fuel c w` configurations available. -/
theorem halt_time_lt_fuel {c : TwoWayCode} {w : List ℕ} {T : ℕ}
    (hT : cfgAt (twoWayCodeAut c) w T = some Cfg.halt) : T < fuel c w := by
  classical
  set M := twoWayCodeAut c with hM
  -- every time `t ≤ T` carries a configuration
  have hsome : ∀ t ≤ T, ∃ x, cfgAt M w t = some x := by
    intro t ht
    rcases hx : cfgAt M w t with _ | x
    · have := cfgAt_none_mono M w ht hx
      rw [hT] at this; simp at this
    · exact ⟨x, rfl⟩
  -- the code of the configuration at time `t`
  set F : ℕ → ℕ := fun t => (cfgAt M w t).elim 0 (cfgCode c) with hF
  have hFval : ∀ t ≤ T, ∀ x, cfgAt M w t = some x → F t = cfgCode c x := by
    intro t _ x hx
    simp [hF, hx]
  have hinj : ∀ s ∈ Finset.range (T + 1), ∀ t ∈ Finset.range (T + 1), F s = F t → s = t := by
    intro s hs t ht hst
    simp only [Finset.mem_range] at hs ht
    obtain ⟨x, hx⟩ := hsome s (by omega)
    obtain ⟨y, hy⟩ := hsome t (by omega)
    rw [hFval s (by omega) x hx, hFval t (by omega) y hy] at hst
    have hxy : x = y := cfgCode_inj hx hy hst
    subst hxy
    exact run_inj M w hT hx hy
  have hmaps : Set.MapsTo F (Finset.range (T + 1)) (Finset.range (fuel c w)) := by
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio] at ht ⊢
    obtain ⟨x, hx⟩ := hsome t (by omega)
    rw [hFval t (by omega) x hx]
    exact cfgCode_lt hx
  have hinj' : Set.InjOn F (Finset.range (T + 1)) := by
    intro s hs t ht hst
    exact hinj s (by simpa using hs) t (by simpa using ht) hst
  have hcard := Finset.card_le_card_of_injOn F hmaps hinj'
  simp only [Finset.card_range] at hcard
  omega

/-! ## The simulation -/

/-- A configuration of a coded two-way transducer, as a first-order datum: `none` is the halting
vertex. -/
abbrev SimCfg := Option (List ℕ × ℕ × List ℕ)

/-- The state of the simulation: `none` means that the run got stuck; otherwise a configuration
together with the output produced so far. -/
abbrev SimState := Option (SimCfg × List ℕ)

/-- A configuration read as a first-order datum. -/
def encCfg : Cfg ℕ ℕ → SimCfg
  | Cfg.conf u q v => some (u, q, v)
  | Cfg.halt => none

/-- One step of the simulation; it mirrors `Transducers.TwoWay.stepCfg` for the transducer
described by the code, and leaves a halted or stuck state unchanged. -/
def simStep (c : TwoWayCode) : SimState → SimState
  | none => none
  | some (none, acc) => some (none, acc)
  | some (some (u, q, v), acc) =>
      match (twoWayCodeAut c).step u.getLast? q v.head? with
      | Sum.inl o => some (none, acc ++ o)
      | Sum.inr (q', o, true) =>
          match v with
          | [] => none
          | a :: v' => some (some (u ++ [a], q', v'), acc ++ o)
      | Sum.inr (q', o, false) =>
          match u.getLast? with
          | none => none
          | some a => some (some (u.dropLast, q', a :: v), acc ++ o)

/-- The simulation of the run of a coded transducer on an input, after `n` steps. -/
def sim (c : TwoWayCode) (w : List ℕ) (n : ℕ) : SimState :=
  (simStep c)^[n] (some (some ([], 0, w), []))

lemma simStep_halted (c : TwoWayCode) (acc : List ℕ) :
    simStep c (some (none, acc)) = some (none, acc) := rfl

lemma iterate_simStep_halted (c : TwoWayCode) (acc : List ℕ) :
    ∀ k, (simStep c)^[k] (some (none, acc)) = some (none, acc) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, simStep_halted, ih]

/-- One step of the simulation follows one step of the run. -/
lemma simStep_of_stepCfg {c : TwoWayCode} {x y : Cfg ℕ ℕ} {o acc : List ℕ}
    (h : (twoWayCodeAut c).stepCfg x = some (o, y)) :
    simStep c (some (encCfg x, acc)) = some (encCfg y, acc ++ o) := by
  cases x with
  | halt => simp [TwoWay.stepCfg] at h
  | conf u q v =>
      rcases hM : (twoWayCodeAut c).step u.getLast? q v.head? with o' | ⟨q', o', dir⟩
      · rw [stepCfg_halt_eq _ hM] at h
        have hpair := Option.some_injective _ h
        have h1 : o' = o := congrArg Prod.fst hpair
        have h2 : Cfg.halt = y := congrArg Prod.snd hpair
        subst h1; subst h2
        simp [simStep, encCfg, hM]
      · cases dir with
        | true =>
            cases v with
            | nil => rw [stepCfg_right_nil _ hM] at h; simp at h
            | cons a v' =>
                rw [stepCfg_right_cons _ hM] at h
                have hpair := Option.some_injective _ h
                have h1 : o' = o := congrArg Prod.fst hpair
                have h2 : Cfg.conf (u ++ [a]) q' v' = y := congrArg Prod.snd hpair
                subst h1; subst h2
                simp only [List.head?_cons] at hM
                simp [simStep, encCfg, hM]
        | false =>
            rcases hu : u.getLast? with _ | a
            · rw [stepCfg_left_none _ hu hM] at h; simp at h
            · rw [stepCfg_left_some _ hu hM] at h
              have hpair := Option.some_injective _ h
              have h1 : o' = o := congrArg Prod.fst hpair
              have h2 : Cfg.conf u.dropLast q' (a :: v) = y := congrArg Prod.snd hpair
              subst h1; subst h2
              rw [hu] at hM
              simp [simStep, encCfg, hM, hu]

/-- **The simulation computes the run.** -/
theorem sim_eq {c : TwoWayCode} {w : List ℕ} :
    ∀ (n : ℕ) {x : Cfg ℕ ℕ}, cfgAt (twoWayCodeAut c) w n = some x →
      sim c w n = some (encCfg x, outRange (twoWayCodeAut c) w 0 n) := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp only [cfgAt_zero, Option.some.injEq] at hx
      subst hx
      simp [sim, encCfg, twoWayCodeAut]
  | succ n ih =>
      intro x hx
      obtain ⟨x', hx', hs⟩ := exists_pred _ w hx
      have hstep := ih hx'
      rw [sim, Function.iterate_succ_apply', ← sim, hstep, simStep_of_stepCfg hs,
        outRange_succ _ w 0 n (Nat.zero_le _)]

/-- The output of the simulation, run with the fuel bound: `some v` if the run of the coded
transducer on `w` halts with output `v`. -/
def simOut (c : TwoWayCode) (w : List ℕ) : Option (List ℕ) :=
  match sim c w (fuel c w) with
  | some (none, acc) => some acc
  | _ => none

/-- **The simulation returns the output of a coded transducer.** -/
theorem simOut_eq_of_computes {c : TwoWayCode} {w v : List ℕ} (h : twoWayCodeRel c w v) :
    simOut c w = some v := by
  obtain ⟨T, hT, hout⟩ := exists_halt_time (twoWayCodeAut c) w h
  have hsim : sim c w T = some (none, v) := by
    have := sim_eq T hT
    rw [hout] at this
    simpa [encCfg] using this
  have hlt : T < fuel c w := halt_time_lt_fuel hT
  have hfuel : sim c w (fuel c w) = some (none, v) := by
    obtain ⟨k, hk⟩ : ∃ k, fuel c w = k + T := ⟨fuel c w - T, by omega⟩
    rw [sim, hk, Function.iterate_add_apply, ← sim, hsim, iterate_simStep_halted]
  rw [simOut, hfuel]

/-- For a code describing a total transducer, the simulation returns the output on every input. -/
theorem exists_simOut {c : TwoWayCode} (hc : TwoWayCodeTotal c) (w : List ℕ) :
    ∃ v, twoWayCodeRel c w v ∧ simOut c w = some v := by
  obtain ⟨v, hv⟩ := hc w
  exact ⟨v, hv, simOut_eq_of_computes hv⟩

end RegDec

end Lax916827Proofs.Transducers
