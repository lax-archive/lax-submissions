/-
Pebble transducers compute polyregular functions.

The proof is by induction on the number of pebbles.  A one-pebble transducer is a two-way
transducer, hence computes a regular function (`RequestProject/PartD/PebbleTwoWay.lean`).  A
`(k+2)`-pebble transducer is simulated by a `(k+1)`-pebble transducer on the marked square of the
padded input (`RequestProject/PartD/PebbleSquareSim.lean`), and marked squaring and padding are
polyregular, so the composition is polyregular.

This is the reachability analysis of a pebble automaton of the book -- Lemma
`lem:reachability-pebble-automaton` and the claims inside its proof -- in the concrete form in
which it is used for Theorem `thm:pebble-are-for`.
-/
import Lax194892Proofs.Source.PartD.PebbleSquareSim
import Lax194892Proofs.Source.PartD.PebbleTwoWay
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers
open Lax314295Proofs Lax314295Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebSq

variable {A B Q : Type}

/-! ## Enlarging the stack bound -/

/-- The same transducer, with a larger bound on the height of the stack. -/
def liftK {k : ℕ} (M : Pebble A B Q k) (k' : ℕ) : Pebble A B Q k' where
  init := M.init
  step := M.step

lemma liftK_stepCfg {k k' : ℕ} (hk : k ≤ k') (M : Pebble A B Q k) {w : List A}
    {c : PebbleCfg Q} {x : List B × PebbleCfg Q} (h : M.stepCfg w c = some x) :
    (liftK M k').stepCfg w c = some x := by
  cases c with
  | halt => exact absurd h (by simp [Pebble.stepCfg])
  | conf q st =>
      cases hM : M.step q (viewOf w st) with
      | mk q' act =>
        have hMl : (liftK M k').step q (viewOf w st) = (q', act) := hM
        cases act with
        | out b =>
            simp only [Pebble.stepCfg, hM] at h
            simp only [Pebble.stepCfg, hMl]
            exact h
        | terminate =>
            simp only [Pebble.stepCfg, hM] at h
            simp only [Pebble.stepCfg, hMl]
            exact h
        | pop =>
            simp only [Pebble.stepCfg, hM] at h
            simp only [Pebble.stepCfg, hMl]
            exact h
        | move d =>
            simp only [Pebble.stepCfg, hM] at h
            simp only [Pebble.stepCfg, hMl]
            exact h
        | push =>
            simp only [Pebble.stepCfg, hM] at h
            by_cases hlt : st.length < k
            · rw [if_pos hlt] at h
              simp only [Pebble.stepCfg, hMl]
              rw [if_pos (by omega)]
              exact h
            · rw [if_neg hlt] at h
              exact absurd h (by simp)

lemma liftK_reaches {k k' : ℕ} (hk : k ≤ k') (M : Pebble A B Q k) {w : List A}
    {c c' : PebbleCfg Q} {v : List B} (h : M.Reaches w c v c') :
    (liftK M k').Reaches w c v c' := by
  induction h with
  | refl c => exact Pebble.Reaches.refl c
  | step hs _ ih => exact Pebble.Reaches.step (liftK_stepCfg hk M hs) ih

lemma liftK_computes {k k' : ℕ} (hk : k ≤ k') (M : Pebble A B Q k) {w : List A} {v : List B}
    (h : M.Computes w v) : (liftK M k').Computes w v :=
  liftK_reaches hk M h

/-! ## The induction on the number of pebbles -/

/-- **Every pebble transducer computes a polyregular function**, on the inputs on which it
halts. -/
theorem exists_polyregular_of_pebble (k : ℕ) :
    ∀ {A B Q : Type} [Finite A] [Finite B] [Finite Q] (M : Pebble A B Q k),
      ∃ F : List A → List B, IsPolyregular F ∧ ∀ w v, M.Computes w v → F w = v := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
        intro A B Q _ _ _ M
        obtain ⟨F, hF, hFs⟩ := PebOne.exists_regularFun_of_pebble_one (liftK M 1)
        exact ⟨F, IsPolyregular.of_regular hF,
          fun w v hv => hFs w v (liftK_computes (by omega) M hv)⟩
    | 1 =>
        intro A B Q _ _ _ M
        obtain ⟨F, hF, hFs⟩ := PebOne.exists_regularFun_of_pebble_one M
        exact ⟨F, IsPolyregular.of_regular hF, hFs⟩
    | (j + 2) =>
        intro A B Q _ _ _ M
        obtain ⟨F, hF, hFs⟩ := ih (j + 1) (by omega) (sim M)
        refine ⟨fun w => F (sqOf w), ?_, ?_⟩
        · exact IsPolyregular.comp'
            (isPolyregular_pad.comp (isPolyregular_markedSquare (Option A))) hF
            (fun w => rfl)
        · intro w v hv
          exact hFs (sqOf w) v (sim_computes hv)

end PebSq

/-- **A function computed by a pebble transducer is polyregular.** -/
theorem isPolyregular_of_isPebbleTransducer {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (h : IsPebbleTransducer f) : IsPolyregular f := by
  obtain ⟨k, Q, hQ, M, hM⟩ := h
  obtain ⟨F, hF, hFs⟩ := PebSq.exists_polyregular_of_pebble k M
  exact hF.congr (fun w => hFs w (f w) (hM w))

end Lax194892Proofs.Transducers
