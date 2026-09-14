/-
A big-step bisimulation principle.

Two deterministic systems that are related by a relation on "good" configurations, in such a way
that from related configurations both make at least one step and either stay related or already
decide acceptance in the same way, accept the same configurations.  This is used twice in the
proof of Theorem `thm:pebble-are-continuous`: once to relate a one-pebble automaton with a
two-way automaton, and once to relate a `(k+1)`-pebble automaton with a one-pebble automaton over
an annotated alphabet.
-/
import Lax194892Proofs.Source.PartD.PebbleAut
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

section Bisim

variable {X Y : Type}

private lemma iterate_absorb {Z : Type} {F : Z → Z} {acc : Z → Prop}
    (h : ∀ z, acc z → acc (F z)) : ∀ (n : ℕ) (z : Z), acc z → acc (F^[n] z) := by
  intro n
  induction n with
  | zero => exact fun z hz => hz
  | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply]
      exact ih _ (h z hz)

private theorem bisim_one_dir (F : X → X) (G : Y → Y) (accX : X → Prop) (accY : Y → Prop)
    (habsX : ∀ x, accX x → accX (F x)) (Rel : X → Y → Prop)
    (hnX : ∀ x y, Rel x y → ¬ accX x)
    (hstep : ∀ x y, Rel x y → ∃ j m, 1 ≤ j ∧ 1 ≤ m ∧
      (Rel (F^[j] x) (G^[m] y) ∨ ((∃ n, accX (F^[n] x)) ↔ (∃ n, accY (G^[n] y))))) :
    ∀ n x y, Rel x y → accX (F^[n] x) → ∃ n', accY (G^[n'] y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro x y hxy hn
      obtain ⟨j, m, hj, hm, hcase⟩ := hstep x y hxy
      rcases hcase with hR | hiff
      · rcases le_or_gt j n with hle | hlt
        · have h1 : accX (F^[n - j] (F^[j] x)) := by
            rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
            exact hn
          obtain ⟨n', hn'⟩ := ih (n - j) (by omega) _ _ hR h1
          exact ⟨n' + m, by rw [Function.iterate_add_apply]; exact hn'⟩
        · exfalso
          refine hnX _ _ hR ?_
          have : F^[j] x = F^[j - n] (F^[n] x) := by
            rw [← Function.iterate_add_apply]
            congr 1
            omega
          rw [this]
          exact iterate_absorb habsX _ _ hn
      · exact hiff.1 ⟨n, hn⟩

/-- Related configurations of two deterministic systems accept alike. -/
theorem bisim_acc_iff (F : X → X) (G : Y → Y) (accX : X → Prop) (accY : Y → Prop)
    (habsX : ∀ x, accX x → accX (F x)) (habsY : ∀ y, accY y → accY (G y))
    (Rel : X → Y → Prop)
    (hnX : ∀ x y, Rel x y → ¬ accX x) (hnY : ∀ x y, Rel x y → ¬ accY y)
    (hstep : ∀ x y, Rel x y → ∃ j m, 1 ≤ j ∧ 1 ≤ m ∧
      (Rel (F^[j] x) (G^[m] y) ∨ ((∃ n, accX (F^[n] x)) ↔ (∃ n, accY (G^[n] y)))))
    (x : X) (y : Y) (h : Rel x y) :
    (∃ n, accX (F^[n] x)) ↔ (∃ n, accY (G^[n] y)) := by
  constructor
  · rintro ⟨n, hn⟩
    exact bisim_one_dir F G accX accY habsX Rel hnX hstep n x y h hn
  · rintro ⟨n, hn⟩
    refine bisim_one_dir G F accY accX habsY (fun y x => Rel x y)
      (fun y x hr => hnY x y hr) ?_ n y x h hn
    intro y x hr
    obtain ⟨j, m, hj, hm, hc⟩ := hstep x y hr
    exact ⟨m, j, hm, hj, hc.imp id Iff.symm⟩

end Bisim

end Lax194892Proofs.Transducers
