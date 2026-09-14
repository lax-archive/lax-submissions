/-
Theorem `thm:composition-of-two-way-transducers`: two-way transducers are closed under composition.

The construction of `TwoWayComp.lean` assumes that all the transitions of the
first transducer produce an output of the same length, ending with a fixed
letter.  This is arranged here by *padding*: the output alphabet is extended
with a blank letter `none`, and every output is padded with blanks to the length
`m+1`, where `m` bounds the length of all the outputs.  Since the padded output
is the original output up to erasing blanks, and since two-way transducers are
closed under pre-composition with erasing homomorphisms
(`isTwoWay_comp_filterMap`), the general case follows from the padded one.
-/
import Lax916827Proofs.Source.PartC.TwoWayComp
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open scoped Classical

variable {A B C Q : Type}

/-- An output string, padded with blanks to the length `m+1`. -/
def padOut (m : ℕ) (o : List B) : List (Option B) :=
  o.map some ++ List.replicate (m + 1 - o.length) none

/-- The transducer `M` with all its outputs padded with blanks. -/
def padAut (M : TwoWay A B Q) (m : ℕ) : TwoWay A (Option B) Q where
  init := M.init
  step := fun l q r =>
    match M.step l q r with
    | Sum.inl o => Sum.inl (padOut m o)
    | Sum.inr (q', o, d) => Sum.inr (q', padOut m o, d)

lemma padOut_length {m : ℕ} {o : List B} (h : o.length ≤ m) : (padOut m o).length = m + 1 := by
  simp [padOut]
  omega

lemma padOut_getLast? {m : ℕ} {o : List B} (h : o.length ≤ m) :
    (padOut m o).getLast? = some none := by
  rw [padOut, List.getLast?_append]
  have hrep : (List.replicate (m + 1 - o.length) (none : Option B)).getLast? = some none := by
    rw [List.getLast?_replicate, if_neg (by omega)]
  rw [hrep]
  rfl

@[simp] lemma padOut_filterMap (m : ℕ) (o : List B) : (padOut m o).filterMap id = o := by
  simp [padOut, List.filterMap_append]

lemma padAut_outWord (M : TwoWay A B Q) (m : ℕ) (l : Option A) (q : Q) (r : Option A) :
    outWord ((padAut M m).step l q r) = padOut m (outWord (M.step l q r)) := by
  rcases h : M.step l q r with o | ⟨q', o, d⟩ <;> simp [padAut, outWord, h]

lemma padAut_step (M : TwoWay A B Q) (m : ℕ) {l : Option A} {q : Q} {r : Option A} {o : List B}
    (h : M.step l q r = Sum.inl o) : (padAut M m).step l q r = Sum.inl (padOut m o) := by
  simp [padAut, h]

lemma padAut_step' (M : TwoWay A B Q) (m : ℕ) {l : Option A} {q q' : Q} {r : Option A} {o : List B}
    {d : Bool} (h : M.step l q r = Sum.inr (q', o, d)) :
    (padAut M m).step l q r = Sum.inr (q', padOut m o, d) := by
  simp [padAut, h]

lemma padAut_stepCfg (M : TwoWay A B Q) (m : ℕ) (c : Cfg A Q) :
    (padAut M m).stepCfg c = (M.stepCfg c).map (fun x => (padOut m x.1, x.2)) := by
  cases c with
  | halt => rfl
  | conf u q v =>
      rcases h : M.step u.getLast? q v.head? with o | ⟨q', o, d⟩
      · rw [stepCfg_halt_eq M h, stepCfg_halt_eq (padAut M m) (padAut_step M m h)]
        rfl
      · cases d with
        | true =>
            cases v with
            | nil =>
                rw [stepCfg_right_nil M h, stepCfg_right_nil (padAut M m) (padAut_step' M m h)]
                rfl
            | cons a v' =>
                rw [stepCfg_right_cons M h, stepCfg_right_cons (padAut M m) (padAut_step' M m h)]
                rfl
        | false =>
            rcases hu : u.getLast? with _ | a
            · rw [stepCfg_left_none M hu h,
                stepCfg_left_none (padAut M m) hu (padAut_step' M m h)]
              rfl
            · rw [stepCfg_left_some M hu h,
                stepCfg_left_some (padAut M m) hu (padAut_step' M m h)]
              rfl

/-- A run of `M` is a run of the padded transducer, with a padded output. -/
lemma padAut_reaches (M : TwoWay A B Q) (m : ℕ) {c c' : Cfg A Q} {o : List B}
    (h : M.Reaches c o c') :
    ∃ o', (padAut M m).Reaches c o' c' ∧ o'.filterMap id = o := by
  induction h with
  | refl c => exact ⟨[], Reaches.refl c, rfl⟩
  | @step c c₁ c₂ o o' hs _ ih =>
      obtain ⟨v, hv, hvf⟩ := ih
      refine ⟨padOut m o ++ v, Reaches.step ?_ hv, ?_⟩
      · rw [padAut_stepCfg, hs]; rfl
      · rw [List.filterMap_append, padOut_filterMap, hvf]

lemma padAut_exists (M : TwoWay A B Q) (m : ℕ) {f : List A → List B}
    (hf : ∀ w, M.Computes w (f w)) (w : List A) :
    ∃ v, (padAut M m).Computes w v ∧ v.filterMap id = f w := by
  obtain ⟨v, hv, hvf⟩ := padAut_reaches M m (hf w)
  exact ⟨v, hv, hvf⟩

/-- The function computed by the padded transducer. -/
noncomputable def padFun (M : TwoWay A B Q) (m : ℕ) (f : List A → List B)
    (hf : ∀ w, M.Computes w (f w)) (w : List A) : List (Option B) :=
  (padAut_exists M m hf w).choose

lemma padFun_computes (M : TwoWay A B Q) (m : ℕ) {f : List A → List B}
    (hf : ∀ w, M.Computes w (f w)) (w : List A) :
    (padAut M m).Computes w (padFun M m f hf w) :=
  (padAut_exists M m hf w).choose_spec.1

lemma padFun_filterMap (M : TwoWay A B Q) (m : ℕ) {f : List A → List B}
    (hf : ∀ w, M.Computes w (f w)) (w : List A) :
    (padFun M m f hf w).filterMap id = f w :=
  (padAut_exists M m hf w).choose_spec.2

end TwoWay

/-- **Theorem `thm:composition-of-two-way-transducers`.**  Functions computed by two-way transducers
are closed under composition. -/
theorem isTwoWay_comp_twoWay {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C} (hf : IsTwoWay f) (hg : IsTwoWay g) :
    IsTwoWay (g ∘ f) := by
  classical
  obtain ⟨Q, hQ, M, hM⟩ := hf
  haveI : Finite Q := hQ
  -- the outer transducer, run on the padded output
  have hg' : IsTwoWay (fun v : List (Option B) => g (v.filterMap id)) :=
    isTwoWay_comp_filterMap hg id
  obtain ⟨P, hP, N, hN⟩ := hg'
  haveI : Finite P := hP
  -- a bound on the length of the outputs of `M`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ x : Option A × Q × Option A,
      (TwoWay.outWord (M.step x.1 x.2.1 x.2.2)).length ≤ m :=
    exists_block_bound (fun x : Option A × Q × Option A => TwoWay.outWord (M.step x.1 x.2.1 x.2.2))
  have houtlen : ∀ l q r,
      (TwoWay.outWord ((TwoWay.padAut M m).step l q r)).length = m + 1 := by
    intro l q r
    rw [TwoWay.padAut_outWord]
    exact TwoWay.padOut_length (hm (l, q, r))
  have houtlast : ∀ l q r,
      (TwoWay.outWord ((TwoWay.padAut M m).step l q r)).getLast? = some (none : Option B) := by
    intro l q r
    rw [TwoWay.padAut_outWord]
    exact TwoWay.padOut_getLast? (hm (l, q, r))
  have hcomp := TwoWay.isTwoWay_comp_uniform (M := TwoWay.padAut M m) (N := N)
    houtlen houtlast (TwoWay.padFun_computes M m hM) hN
  have hfun : (fun w => (fun v : List (Option B) => g (v.filterMap id))
      (TwoWay.padFun M m f hM w)) = g ∘ f := by
    funext w
    simp only [Function.comp_apply, TwoWay.padFun_filterMap M m hM w]
  exact hfun ▸ hcomp

end Lax916827Proofs.Transducers
