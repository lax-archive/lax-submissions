/-
**A configuration that really has a child.**

Lemma `lem:children-of-configuration-in-pebble-run` and Claim
`claim:from-configuration-to-child-configuration-graph`
(`RequestProject/PartD/CGFor.lean`) are statements about a configuration together with the list
`ch 0, …, ch m` of its children (`Transducers.CG.IsChildSeq`).  This file exhibits a machine and a
configuration for which that hypothesis holds, so that the two results are not vacuously true: the
one-pebble machine which pushes a pebble and then terminates has, from its initial configuration,
exactly one child, and the for-transducer of the lemma turns the string representation of the
initial configuration into the string representation of that child.
-/
import Lax194892Proofs.Source.PartD.CGFor
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers
open Lax314295Proofs Lax314295Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CG

/-- **The machine that pushes a pebble and then terminates.**  In the state `false` it pushes; in
the state `true`, which is where a push leaves it, it terminates. -/
def pushMach : Pebble Unit Unit Bool 1 where
  init := false
  step := fun q _ => if q then (true, PebbleAction.terminate) else (true, PebbleAction.push)

lemma stepCfg_pushMach_false (w : List Unit) :
    pushMach.stepCfg w (PebbleCfg.conf false []) = some ([], PebbleCfg.conf true [0]) := by
  simp [Pebble.stepCfg, pushMach]

lemma stepCfg_pushMach_true (w : List Unit) (st : List ℕ) :
    pushMach.stepCfg w (PebbleCfg.conf true st) = some ([], PebbleCfg.halt) := by
  simp [Pebble.stepCfg, pushMach]

/-- **The initial configuration of `pushMach` has exactly one child**, the configuration reached by
the push. -/
theorem isChildSeq_pushMach (w : List Unit) :
    IsChildSeq pushMach w false [] (fun _ => (true, 0)) 0 where
  first := Pebble.StrictAbove.one (stepCfg_pushMach_false w)
  next := by intro t ht; exact absurd ht (by omega)
  stop := by
    intro v hv
    rw [NextChild, show cfgOf ([] : List ℕ) ((true, 0) : Vtx Bool) = PebbleCfg.conf true [0] from
      rfl] at hv
    have hne : cfgOf ([] : List ℕ) v ≠ PebbleCfg.halt := by simp [cfgOf]
    cases hv with
    | one hs =>
        rw [stepCfg_pushMach_true w [0]] at hs
        exact hne ((Prod.ext_iff.1 (Option.some.inj hs)).2).symm
    | cons hs hh _ =>
        rw [stepCfg_pushMach_true w [0]] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rw [← hs.2] at hh
        exact Pebble.heightGe_halt hh

end CG

/-- **Lemma `lem:children-of-configuration-in-pebble-run` is not vacuous.**  For the machine
`Transducers.CG.pushMach` the hypothesis of the lemma is satisfied by the initial configuration,
and the for-transducer of the lemma maps the string representation of that configuration to the
string representation of its unique child. -/
theorem children_of_configuration_in_pebble_run_witness (w : List Unit) :
    ∃ f : List (CG.ConfLetter Unit Bool 1) → List (CG.ConfLetter Unit Bool 1),
      IsForTransducer f ∧
      f (CG.confEnc false [] w) = CG.confEnc true [0] w := by
  obtain ⟨f, hf, hspec⟩ := children_of_configuration_in_pebble_run CG.pushMach
  refine ⟨f, hf, ?_⟩
  have h := hspec false [] w (fun _ => (true, 0)) 0 (by simp) (by norm_num)
    (CG.isChildSeq_pushMach w)
  simpa using h

end Lax194892Proofs.Transducers
