/-
Computability of the simulation of a coded two-way transducer, and with it the proof of what used
to be the effectivity hypothesis `Transducers.EffectiveTwoWayEvalEq` of
`RequestProject/PartC/EffectiveReg.lean`.

`RequestProject/PartC/TwoWaySim.lean` runs the transducer described by a code on an input string,
with the fuel bound `Transducers.RegDec.fuel` that a halting run of a deterministic two-way
transducer cannot exceed, and returns the output produced
(`Transducers.RegDec.simOut_eq_of_computes`).  What is proved here is that this procedure is
primitive recursive, hence computable, so that the equality test of two coded two-way transducers on
a given input is a `Computable` procedure.

The general-purpose `Primrec` lemmas that this needs -- lookup in an association list, the last
element of a list and its removal -- are in `RequestProject/Common/PrimrecList.lean`, next to the
ones the same development needed for weighted automata in
`RequestProject/PartB/WCodePrimrec.lean`.
-/
import Lax916827Proofs.Source.PartC.TwoWaySim
import Lax916827Proofs.Source.PartC.RegCodeBound
import Lax132576Proofs.Source.Common.PrimrecList
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegDec

open Primrec

/-! ## Comparing two coded transducers on one input -/

/-- **Comparing two coded two-way transducers on one input.**  For total codes, the two coded
transducers have the same behaviour on `w` exactly when the two simulations return the same
output. -/
theorem simOut_eq_iff {c₁ c₂ : TwoWayCode} (h₁ : TwoWayCodeTotal c₁) (h₂ : TwoWayCodeTotal c₂)
    (w : List ℕ) : simOut c₁ w = simOut c₂ w ↔ twoWayCodeRel c₁ w = twoWayCodeRel c₂ w := by
  obtain ⟨v₁, hv₁, hs₁⟩ := exists_simOut h₁ w
  obtain ⟨v₂, hv₂, hs₂⟩ := exists_simOut h₂ w
  rw [hs₁, hs₂]
  constructor
  · intro h
    have hvv : v₁ = v₂ := Option.some_injective _ h
    subst hvv
    funext v
    simp only [eq_iff_iff]
    constructor
    · intro hv
      have : v = v₁ := TwoWay.computes_unique hv hv₁
      subst this
      exact hv₂
    · intro hv
      have : v = v₁ := TwoWay.computes_unique hv hv₂
      subst this
      exact hv₁
  · intro h
    have hv₁' : twoWayCodeRel c₂ w v₁ := by rw [← h]; exact hv₁
    rw [TwoWay.computes_unique hv₁' hv₂]

/-! ## The transition function of a coded transducer -/

/-- The transition function of the transducer described by a code is a primitive recursive function
of the code and of the two letters adjacent to the head. -/
theorem primrec_codeStep :
    Primrec (fun z : TwoWayCode × (Option ℕ × ℕ × Option ℕ) =>
      (twoWayCodeAut z.1).step z.2.1 z.2.2.1 z.2.2.2) := by
  have h : Primrec fun z : TwoWayCode × (Option ℕ × ℕ × Option ℕ) =>
      (z.1.lookup z.2).getD (Sum.inl []) :=
    Primrec.option_getD.comp (Primrec.list_lookup.comp fst snd)
      (const (Sum.inl [] : List ℕ ⊕ (ℕ × List ℕ × Bool)))
  refine h.of_eq fun z => ?_
  show (z.1.lookup z.2).getD (Sum.inl []) = _
  rcases hl : z.1.lookup z.2 with _ | x <;> simp [twoWayCodeAut, hl]

/-! ## One step of the simulation -/

/-- The context of the body of one simulation step: the code, the current configuration, and the
output produced so far. -/
private abbrev Ctx := (TwoWayCode × (List ℕ × ℕ × List ℕ)) × List ℕ

/-- One step of the simulation is primitive recursive. -/
theorem primrec_simStep : Primrec₂ (fun (c : TwoWayCode) (s : SimState) => simStep c s) := by
  -- the components of the context
  have hc : Primrec fun z : Ctx => z.1.1 := fst.comp fst
  have hu : Primrec fun z : Ctx => z.1.2.1 := fst.comp (snd.comp fst)
  have hq : Primrec fun z : Ctx => z.1.2.2.1 := fst.comp (snd.comp (snd.comp fst))
  have hv : Primrec fun z : Ctx => z.1.2.2.2 := snd.comp (snd.comp (snd.comp fst))
  have hacc : Primrec fun z : Ctx => z.2 := snd
  have hlast : Primrec fun z : Ctx => z.1.2.1.getLast? := Primrec.list_getLast?.comp hu
  have hstep : Primrec fun z : Ctx =>
      (twoWayCodeAut z.1.1).step z.1.2.1.getLast? z.1.2.2.1 z.1.2.2.2.head? :=
    primrec_codeStep.comp
      (Primrec.pair hc (Primrec.pair hlast (Primrec.pair hq (list_head?.comp hv))))
  -- the body of the simulation step, for a running configuration
  have hbody : Primrec fun z : Ctx =>
      (Sum.casesOn ((twoWayCodeAut z.1.1).step z.1.2.1.getLast? z.1.2.2.1 z.1.2.2.2.head?)
        (fun o => some ((none : SimCfg), z.2 ++ o))
        (fun y : ℕ × List ℕ × Bool =>
          bif y.2.2 then
            ((List.casesOn z.1.2.2.2 (none : SimState)
              (fun a v' => some (some (z.1.2.1 ++ [a], y.1, v'), z.2 ++ y.2.1))) : SimState)
          else
            ((Option.casesOn z.1.2.1.getLast? (none : SimState)
              (fun a => some (some (z.1.2.1.dropLast, y.1, a :: z.1.2.2.2), z.2 ++ y.2.1))) :
              SimState)) : SimState) := by
    refine Primrec.sumCasesOn hstep ?_ ?_
    · exact (option_some.comp (Primrec.pair (const (none : SimCfg))
        (list_append.comp (hacc.comp fst) snd))).to₂
    · -- the components of the context of a moving transition
      have ku : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) => p.1.1.2.1 := hu.comp fst
      have kv : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) => p.1.1.2.2.2 := hv.comp fst
      have kacc : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) => p.1.2 := hacc.comp fst
      have klast : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) => p.1.1.2.1.getLast? :=
        hlast.comp fst
      have kq : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) => p.2.1 := fst.comp snd
      have ko : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) => p.2.2.1 := fst.comp (snd.comp snd)
      have kdir : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) => p.2.2.2 := snd.comp (snd.comp snd)
      have hright : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) =>
          ((List.casesOn p.1.1.2.2.2 (none : SimState)
            (fun a v' => some (some (p.1.1.2.1 ++ [a], p.2.1, v'), p.1.2 ++ p.2.2.1))) :
            SimState) := by
        refine Primrec.list_casesOn (f := fun p : Ctx × (ℕ × List ℕ × Bool) => p.1.1.2.2.2)
          (g := fun _ => (none : SimState))
          (h := fun (p : Ctx × (ℕ × List ℕ × Bool)) (x : ℕ × List ℕ) =>
            some (some (p.1.1.2.1 ++ [x.1], p.2.1, x.2), p.1.2 ++ p.2.2.1))
          kv (const (none : SimState)) ?_
        exact (option_some.comp (Primrec.pair
          (option_some.comp (Primrec.pair
            (list_append.comp (ku.comp fst) (list_cons.comp (fst.comp snd) (const [])))
            (Primrec.pair (kq.comp fst) (snd.comp snd))))
          (list_append.comp (kacc.comp fst) (ko.comp fst)))).to₂
      have hleft : Primrec fun p : Ctx × (ℕ × List ℕ × Bool) =>
          ((Option.casesOn p.1.1.2.1.getLast? (none : SimState)
            (fun a => some (some (p.1.1.2.1.dropLast, p.2.1, a :: p.1.1.2.2.2),
              p.1.2 ++ p.2.2.1))) : SimState) := by
        refine Primrec.option_casesOn klast (const (none : SimState)) ?_
        exact (option_some.comp (Primrec.pair
          (option_some.comp (Primrec.pair
            (Primrec.list_dropLast.comp (ku.comp fst))
            (Primrec.pair (kq.comp fst) (list_cons.comp snd (kv.comp fst)))))
          (list_append.comp (kacc.comp fst) (ko.comp fst)))).to₂
      exact (Primrec.cond kdir hright hleft).to₂
  -- assemble the two outer case distinctions
  have hinner : Primrec fun z : (TwoWayCode × SimCfg) × List ℕ =>
      (Option.casesOn z.1.2 (some ((none : SimCfg), z.2))
        (fun x => simStep z.1.1 (some (some x, z.2))) : SimState) := by
    refine Primrec.option_casesOn (snd.comp fst)
      (option_some.comp (Primrec.pair (const (none : SimCfg)) snd)) ?_
    refine (hbody.comp (Primrec.pair (Primrec.pair (fst.comp (fst.comp fst)) snd)
      (snd.comp fst))).to₂.of_eq ?_
    intro z x
    obtain ⟨u, q, v⟩ := x
    show _ = simStep z.1.1 (some (some (u, q, v), z.2))
    rw [simStep]
    rcases hM : (twoWayCodeAut z.1.1).step u.getLast? q v.head? with o | ⟨q', o, dir⟩
    · simp
    · cases dir with
      | true => cases v <;> simp
      | false => rcases hu : u.getLast? with _ | a <;> simp
  have houter : Primrec fun z : TwoWayCode × SimState =>
      (Option.casesOn z.2 (none : SimState) (fun p => simStep z.1 (some p)) : SimState) := by
    refine Primrec.option_casesOn snd (const (none : SimState)) ?_
    refine ((hinner.comp (Primrec.pair (Primrec.pair (fst.comp fst) (fst.comp snd))
      (snd.comp snd))).to₂).of_eq ?_
    intro z p
    obtain ⟨x, acc⟩ := p
    cases x with
    | none => rfl
    | some x => rfl
  refine houter.to₂.of_eq ?_
  intro c s
  cases s with
  | none => rfl
  | some p => rfl


/-! ## The simulation and its output -/

/-- The states occurring in a code form a primitive recursive function of the code. -/
theorem primrec_codeStates : Primrec codeStates := by
  have hflat : Primrec fun c : TwoWayCode =>
      c.flatMap (fun t => match t.2 with | Sum.inl _ => [] | Sum.inr y => [y.1]) := by
    refine Primrec.list_flatMap Primrec.id ?_
    refine (Primrec.sumCasesOn (snd.comp snd) (const ([] : List ℕ)).to₂
      (list_cons.comp (fst.comp snd) (const ([] : List ℕ))).to₂).to₂.of_eq ?_
    intro c t
    rcases t with ⟨k, x⟩
    cases x <;> rfl
  exact (list_cons.comp (const 0) hflat).of_eq fun c => rfl

/-- The fuel bound is a primitive recursive function of the code and the input. -/
theorem primrec_fuel : Primrec₂ fuel :=
  (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.succ.comp (list_length.comp snd))
    (list_length.comp (primrec_codeStates.comp fst)))).to₂

/-- The simulation is primitive recursive. -/
theorem primrec_sim : Primrec fun p : (TwoWayCode × List ℕ) × ℕ => sim p.1.1 p.1.2 p.2 := by
  have hinit : Primrec fun p : (TwoWayCode × List ℕ) × ℕ =>
      (some (some (([] : List ℕ), 0, p.1.2), ([] : List ℕ)) : SimState) :=
    option_some.comp (Primrec.pair
      (option_some.comp (Primrec.pair (const ([] : List ℕ))
        (Primrec.pair (const 0) (snd.comp fst)))) (const ([] : List ℕ)))
  exact Primrec.nat_iterate snd hinit
    (primrec_simStep.comp (fst.comp (fst.comp fst)) snd).to₂

/-- **The output of the simulation is primitive recursive.** -/
theorem primrec_simOut : Primrec₂ simOut := by
  have hsim : Primrec fun p : TwoWayCode × List ℕ => sim p.1 p.2 (fuel p.1 p.2) :=
    primrec_sim.comp (Primrec.pair Primrec.id (primrec_fuel.comp fst snd))
  have h : Primrec fun p : TwoWayCode × List ℕ =>
      (Option.casesOn (sim p.1 p.2 (fuel p.1 p.2)) (none : Option (List ℕ))
        (fun x => Option.casesOn x.1 (some x.2) (fun _ => none)) : Option (List ℕ)) := by
    refine Primrec.option_casesOn hsim (const (none : Option (List ℕ))) ?_
    refine (Primrec.option_casesOn (fst.comp snd)
      (option_some.comp (snd.comp snd))
      (const (none : Option (List ℕ))).to₂).to₂
  refine h.to₂.of_eq ?_
  intro c w
  show _ = simOut c w
  rw [simOut]
  rcases hs : sim c w (fuel c w) with _ | ⟨x, acc⟩
  · rfl
  · cases x <;> rfl

end RegDec

/-- **Comparing two coded two-way transducers on a given input.**

There is a computable procedure which, given two codes `c₁, c₂` of two-way transducers and an input
string `w`, decides whether the two transducers have the same outputs on `w` -- correctly at least
when both codes are *total*, i.e. when every input has at least one output (`TwoWayCodeTotal`).

This used to be an explicit hypothesis of Theorem `thm:decidable-equivalence-regular`.  The
procedure is the obvious one: a two-way transducer is deterministic, so its run on `w` is a uniquely
determined sequence of configurations, and one simulates it and compares the two outputs.  What was
missing was the bound that makes the simulation a *total* (as opposed to merely partial) computable
procedure, and the primitive recursive bookkeeping on codes.  Both are supplied in
`RequestProject/PartC/TwoWaySim.lean` and above: a halting run of a coded transducer visits no
configuration twice, so it is shorter than `Transducers.RegDec.fuel c w`, and running the
simulation for that many steps is primitive recursive in the code and the input. -/
theorem EffectiveTwoWayEvalEq :
    ∃ D : TwoWayCode × TwoWayCode × List ℕ → Bool, Computable D ∧
      ∀ c₁ c₂ (w : List ℕ), TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
        (D (c₁, c₂, w) = true ↔ twoWayCodeRel c₁ w = twoWayCodeRel c₂ w) := by
  refine ⟨fun p => decide (RegDec.simOut p.1 p.2.2 = RegDec.simOut p.2.1 p.2.2), ?_, ?_⟩
  · exact ((Primrec.eq (α := Option (List ℕ))).comp
      (RegDec.primrec_simOut.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
      (RegDec.primrec_simOut.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).decide.to_comp
  · intro c₁ c₂ w h₁ h₂
    rw [decide_eq_true_eq]
    exact RegDec.simOut_eq_iff h₁ h₂ w

end Lax916827Proofs.Transducers
