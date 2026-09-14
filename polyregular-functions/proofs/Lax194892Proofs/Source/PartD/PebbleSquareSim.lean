/-
The simulation theorem: a `(k+2)`-pebble transducer on `w` is simulated by a `(k+1)`-pebble
transducer on the marked square of the padded input.

The step-by-step lemmas of `RequestProject/PartD/PebbleSquareRun.lean` are put together here: the
dispatcher `PebSq.sim_step` chooses the right one according to the action of the simulated machine
and the shape of its stack, and `PebSq.sim_computes` follows a whole halting run.
-/
import Lax194892Proofs.Source.PartD.PebbleSquareRun
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebSq

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q (k + 1)} {w : List A}

/-! ## Stacks that the encoding can handle -/

/-- Every pebble of the stack is a gap of the input. -/
def StValid (w : List A) (st : List ℕ) : Prop := ∀ p ∈ st, p ≤ w.length

/-- A configuration whose stack the encoding can handle. -/
def CfgValid (w : List A) : PebbleCfg Q → Prop
  | PebbleCfg.halt => True
  | PebbleCfg.conf _ st => StValid w st

/-- The three shapes of a stack that the encoding distinguishes. -/
lemma stack_shape (st : List ℕ) :
    st = [] ∨ (∃ p, st = [p]) ∨ ∃ p₁ mid ptop, st = p₁ :: (mid ++ [ptop]) := by
  match st with
  | [] => exact Or.inl rfl
  | [p] => exact Or.inr (Or.inl ⟨p, rfl⟩)
  | p₁ :: p₂ :: rest =>
      refine Or.inr (Or.inr ?_)
      rcases List.eq_nil_or_concat (p₂ :: rest) with h | ⟨L, b, h⟩
      · exact absurd h (by simp)
      · exact ⟨p₁, L, b, by rw [h, List.concat_eq_append]⟩

lemma dropLast_cons_concat (p₁ ptop : ℕ) (mid : List ℕ) :
    (p₁ :: (mid ++ [ptop])).dropLast = p₁ :: mid := by
  show ((p₁ :: mid) ++ [ptop]).dropLast = p₁ :: mid
  rw [List.dropLast_concat]

lemma getLast?_cons_concat (p₁ ptop : ℕ) (mid : List ℕ) :
    (p₁ :: (mid ++ [ptop])).getLast? = some ptop := by
  show ((p₁ :: mid) ++ [ptop]).getLast? = some ptop
  rw [List.getLast?_concat]

/-- The step of a pebble transducer that moves the topmost pebble to the right. -/
lemma stepCfg_move_right_eq {kk : ℕ} {M : Pebble A B Q kk} {q q' : Q} {st : List ℕ} {p : ℕ}
    (hM : M.step q (viewOf w st) = (q', PebbleAction.move true))
    (hlast : st.getLast? = some p) :
    M.stepCfg w (PebbleCfg.conf q st)
      = if p < w.length then some ([], PebbleCfg.conf q' (st.dropLast ++ [p + 1])) else none := by
  simp only [Pebble.stepCfg, hM, hlast, if_pos]

/-- The step of a pebble transducer that moves the topmost pebble to the left. -/
lemma stepCfg_move_left_eq {kk : ℕ} {M : Pebble A B Q kk} {q q' : Q} {st : List ℕ} {p : ℕ}
    (hM : M.step q (viewOf w st) = (q', PebbleAction.move false))
    (hlast : st.getLast? = some p) :
    M.stepCfg w (PebbleCfg.conf q st)
      = if 0 < p then some ([], PebbleCfg.conf q' (st.dropLast ++ [p - 1])) else none := by
  simp only [Pebble.stepCfg, hM, hlast, if_neg (show ¬((false : Bool) = true) by simp)]

lemma some_pair_eq {α β : Type} {a a' : α} {b b' : β} (h : some (a, b) = some (a', b')) :
    a = a' ∧ b = b' := by
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h

/-! ## Validity is preserved by a step -/

lemma stValid_step {q : Q} {st : List ℕ} {o : List B} {c' : PebbleCfg Q}
    (hval : StValid w st) (hs : M.stepCfg w (PebbleCfg.conf q st) = some (o, c')) :
    CfgValid w c' := by
  cases hM : M.step q (viewOf w st) with
  | mk q' act =>
    cases act with
    | out b =>
        simp only [Pebble.stepCfg, hM] at hs
        obtain ⟨-, rfl⟩ := some_pair_eq hs
        exact hval
    | terminate =>
        simp only [Pebble.stepCfg, hM] at hs
        obtain ⟨-, rfl⟩ := some_pair_eq hs
        trivial
    | push =>
        simp only [Pebble.stepCfg, hM] at hs
        by_cases hlt : st.length < k + 1
        · rw [if_pos hlt] at hs
          obtain ⟨-, rfl⟩ := some_pair_eq hs
          intro p hp
          rcases List.mem_append.mp hp with h | h
          · exact hval p h
          · simp only [List.mem_singleton] at h
            omega
        · rw [if_neg hlt] at hs
          exact absurd hs (by simp)
    | pop =>
        simp only [Pebble.stepCfg, hM] at hs
        by_cases hnil : st = []
        · rw [if_pos hnil] at hs
          exact absurd hs (by simp)
        · rw [if_neg hnil] at hs
          obtain ⟨-, rfl⟩ := some_pair_eq hs
          intro p hp
          exact hval p (List.dropLast_subset st hp)
    | move dir =>
        cases hlast : st.getLast? with
        | none =>
            rw [show M.stepCfg w (PebbleCfg.conf q st) = none by
              simp only [Pebble.stepCfg, hM, hlast]] at hs
            exact absurd hs (by simp)
        | some p =>
            have hpmem : p ∈ st := List.mem_of_getLast? hlast
            have hsub : ∀ x ∈ st.dropLast, x ≤ w.length := fun x hx =>
              hval x (List.dropLast_subset st hx)
            cases dir with
            | true =>
                rw [stepCfg_move_right_eq hM hlast] at hs
                by_cases hp : p < w.length
                · rw [if_pos hp] at hs
                  obtain ⟨-, rfl⟩ := some_pair_eq hs
                  intro x hx
                  rcases List.mem_append.mp hx with h | h
                  · exact hsub x h
                  · simp only [List.mem_singleton] at h; omega
                · rw [if_neg hp] at hs
                  exact absurd hs (by simp)
            | false =>
                rw [stepCfg_move_left_eq hM hlast] at hs
                by_cases hp : 0 < p
                · rw [if_pos hp] at hs
                  obtain ⟨-, rfl⟩ := some_pair_eq hs
                  intro x hx
                  rcases List.mem_append.mp hx with h | h
                  · exact hsub x h
                  · simp only [List.mem_singleton] at h
                    have := hval p hpmem
                    omega
                · rw [if_neg hp] at hs
                  exact absurd hs (by simp)

/-! ## The dispatcher -/

lemma sim_step {q : Q} {st : List ℕ} {o v : List B} {c' : PebbleCfg Q}
    (hk : 1 ≤ k) (hval : StValid w st)
    (hs : M.stepCfg w (PebbleCfg.conf q st) = some (o, c'))
    (hcont : (sim M).Reaches (sqOf w) (encCfg w c') v PebbleCfg.halt) :
    (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf q st)) (o ++ v) PebbleCfg.halt := by
  cases hM : M.step q (viewOf w st) with
  | mk q' act =>
    cases act with
    | out b =>
        simp only [Pebble.stepCfg, hM] at hs
        obtain ⟨rfl, rfl⟩ := some_pair_eq hs
        exact sim_out hval hM hcont
    | terminate =>
        simp only [Pebble.stepCfg, hM] at hs
        obtain ⟨rfl, rfl⟩ := some_pair_eq hs
        exact sim_terminate hval hM hcont
    | push =>
        simp only [Pebble.stepCfg, hM] at hs
        by_cases hlt : st.length < k + 1
        · rw [if_pos hlt] at hs
          obtain ⟨rfl, rfl⟩ := some_pair_eq hs
          rcases stack_shape st with rfl | ⟨p, rfl⟩ | ⟨p₁, mid, ptop, rfl⟩
          · have h := sim_push_nil (M := M) (w := w) hk hM (v := v) (by simpa using hcont)
            simpa using h
          · have h := sim_push_one (M := M) (w := w) (hval p (by simp)) hM (v := v)
              (by simpa using hcont)
            simpa using h
          · have h := sim_push_deep (M := M) (w := w) hval hlt hM (v := v) hcont
            simpa using h
        · rw [if_neg hlt] at hs
          exact absurd hs (by simp)
    | pop =>
        simp only [Pebble.stepCfg, hM] at hs
        by_cases hnil : st = []
        · rw [if_pos hnil] at hs
          exact absurd hs (by simp)
        · rw [if_neg hnil] at hs
          obtain ⟨rfl, rfl⟩ := some_pair_eq hs
          rcases stack_shape st with rfl | ⟨p, rfl⟩ | ⟨p₁, mid, ptop, rfl⟩
          · exact absurd rfl hnil
          · have h := sim_pop_one (M := M) (w := w) (hval p (by simp)) hM (v := v)
              (by simpa using hcont)
            simpa using h
          · rcases eq_or_ne mid [] with rfl | hmid
            · have h := sim_pop_two (M := M) (w := w) (hval p₁ (by simp))
                (hval ptop (by simp)) (by simpa using hM) (v := v) (by simpa using hcont)
              simpa using h
            · have h := sim_pop_deep (M := M) (w := w) hmid hval hM (v := v)
                (by rw [dropLast_cons_concat] at hcont; exact hcont)
              simpa using h
    | move dir =>
        rcases stack_shape st with rfl | ⟨p, rfl⟩ | ⟨p₁, mid, ptop, rfl⟩
        · rw [show M.stepCfg w (PebbleCfg.conf q ([] : List ℕ)) = none by
            simp only [Pebble.stepCfg, hM]; rfl] at hs
          exact absurd hs (by simp)
        · cases dir with
          | true =>
              rw [stepCfg_move_right_eq hM List.getLast?_singleton] at hs
              by_cases hp : p < w.length
              · rw [if_pos hp] at hs
                obtain ⟨rfl, rfl⟩ := some_pair_eq hs
                have h := sim_move_one_right (M := M) (w := w) hp hM (v := v)
                  (by simpa using hcont)
                simpa using h
              · rw [if_neg hp] at hs
                exact absurd hs (by simp)
          | false =>
              rw [stepCfg_move_left_eq hM List.getLast?_singleton] at hs
              by_cases hp : 0 < p
              · rw [if_pos hp] at hs
                obtain ⟨rfl, rfl⟩ := some_pair_eq hs
                have h := sim_move_one_left (M := M) (w := w) hp (hval p (by simp)) hM (v := v)
                  (by simpa using hcont)
                simpa using h
              · rw [if_neg hp] at hs
                exact absurd hs (by simp)
        · cases dir with
          | true =>
              rw [stepCfg_move_right_eq hM (getLast?_cons_concat p₁ ptop mid),
                dropLast_cons_concat] at hs
              by_cases hp : ptop < w.length
              · rw [if_pos hp] at hs
                obtain ⟨rfl, rfl⟩ := some_pair_eq hs
                have h := sim_move_deep_right (M := M) (w := w) hval hp hM (v := v)
                  (by simpa using hcont)
                simpa using h
              · rw [if_neg hp] at hs
                exact absurd hs (by simp)
          | false =>
              rw [stepCfg_move_left_eq hM (getLast?_cons_concat p₁ ptop mid),
                dropLast_cons_concat] at hs
              by_cases hp : 0 < ptop
              · rw [if_pos hp] at hs
                obtain ⟨rfl, rfl⟩ := some_pair_eq hs
                have h := sim_move_deep_left (M := M) (w := w) hval hp hM (v := v)
                  (by simpa using hcont)
                simpa using h
              · rw [if_neg hp] at hs
                exact absurd hs (by simp)

/-! ## The whole run -/

lemma sim_run_aux (hk : 1 ≤ k) {c c'' : PebbleCfg Q} {v : List B}
    (h : M.Reaches w c v c'') :
    c'' = PebbleCfg.halt → CfgValid w c →
      (sim M).Reaches (sqOf w) (encCfg w c) v PebbleCfg.halt := by
  induction h with
  | refl c => rintro rfl -; exact Pebble.Reaches.refl _
  | @step c c' c'' o o' hs hr ih =>
      rintro rfl hv
      cases c with
      | halt => simp [Pebble.stepCfg] at hs
      | conf q st => exact sim_step hk hv hs (ih rfl (stValid_step hv hs))

/-- **The simulation theorem**: the `(k+1)`-pebble transducer `sim M` on the marked square of the
padded input produces the same output as the `(k+2)`-pebble transducer `M` on the input. -/
theorem sim_computes {k : ℕ} {M : Pebble A B Q (k + 2)} {w : List A} {v : List B}
    (h : M.Computes w v) : (sim M).Computes (sqOf w) v := by
  have h0 : (sim M).Reaches (sqOf w) (encCfg w (PebbleCfg.conf M.init [])) v PebbleCfg.halt :=
    sim_run_aux (k := k + 1) (by omega) h rfl (by intro p hp; simp at hp)
  exact h0

end PebSq

end Lax194892Proofs.Transducers
