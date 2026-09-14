/-
The marked disjoint sum of two functions, used in the proof of Claim `claim:conditional` of
*Transducers* (M. Bojańczyk).

The claim asks for a regular function on `(A₁ + A₂)*` that applies `f₁` to the
strings using only letters of `A₁` and `f₂` to the strings using only letters of
`A₂`.  The proof is by induction on the decomposition of `f₁` and `f₂` into
prime functions, and for the induction to go through one has to be able to tell
the two cases apart even when the string is empty (see the note in
`RequestProject/PartC/RegSum.lean`).  This is achieved by working with *marked*
strings: the input is `m₁ u` with `u` over `A₁`, or `m₂ u` with `u` over `A₂`,
where `m₁` and `m₂` are two marker letters, and the output is marked in the same
way.  With this convention the construction is literally compatible with
composition.

This file develops the general theory of the marked sum: the shape of a marked
string, the specification `MSumSpec`, closure under composition, the swap of the
two summands, the base case where both functions are the identity, the base case
where the first function is rational, and the passage from the marked sum to the
statement of Claim `claim:conditional`.  The two remaining base cases, where one of the
functions is map reverse or map duplicate, are in
`RequestProject/PartC/SumPrime.lean`.
-/
import Lax916827Proofs.Source.PartC.RatTools
import Lax916827Proofs.Source.PartC.RegularDef
import Lax132576Proofs.Source.PartB.PrimeRat
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A₁ A₂ B₁ B₂ : Type}

/-! ## Marked strings and their shapes -/

/-- The marked string `m₁ u` for a string `u` over the first alphabet. -/
def mkL {A₁ : Type} (A₂ : Type) (u : List A₁) : List (Bool ⊕ A₁ ⊕ A₂) :=
  Sum.inl false :: u.map (fun a => Sum.inr (Sum.inl a))

/-- The marked string `m₂ u` for a string `u` over the second alphabet. -/
def mkR (A₁ : Type) {A₂ : Type} (u : List A₂) : List (Bool ⊕ A₁ ⊕ A₂) :=
  Sum.inl true :: u.map (fun a => Sum.inr (Sum.inr a))

/-- The string used as the value `⊥` on inputs that are not marked strings. -/
def botStr (B₁ B₂ : Type) : List (Bool ⊕ B₁ ⊕ B₂) := [Sum.inl false, Sum.inl false]

@[simp] lemma mkL_nil (A₂ : Type) : mkL A₂ ([] : List A₁) = [Sum.inl false] := rfl

@[simp] lemma mkR_nil (A₁ : Type) : mkR A₁ ([] : List A₂) = [Sum.inl true] := rfl

lemma mkL_injective {u v : List A₁} (h : mkL A₂ u = mkL A₂ v) : u = v := by
  simp only [mkL, List.cons.injEq, true_and] at h
  exact List.map_injective_iff.2 (by intro x y hxy; simpa using hxy) h

lemma mkR_injective {u v : List A₂} (h : mkR A₁ u = mkR A₁ v) : u = v := by
  simp only [mkR, List.cons.injEq, true_and] at h
  exact List.map_injective_iff.2 (by intro x y hxy; simpa using hxy) h

lemma botStr_ne_mkL (u : List B₁) : botStr B₁ B₂ ≠ mkL B₂ u := by
  intro h
  cases u with
  | nil => simp [botStr, mkL] at h
  | cons b u => simp [botStr, mkL] at h

lemma botStr_ne_mkR (u : List B₂) : botStr B₁ B₂ ≠ mkR B₁ u := by
  intro h
  simp [botStr, mkR] at h

/-- The states of the automaton recognising the marked strings. -/
inductive Shp | start | inL | inR | bad
  deriving DecidableEq, Fintype

/-- The transition function of the automaton recognising the marked strings. -/
def shpStep {A₁ A₂ : Type} : Shp → (Bool ⊕ A₁ ⊕ A₂) → Shp
  | Shp.start, Sum.inl false => Shp.inL
  | Shp.start, Sum.inl true => Shp.inR
  | Shp.inL, Sum.inr (Sum.inl _) => Shp.inL
  | Shp.inR, Sum.inr (Sum.inr _) => Shp.inR
  | _, _ => Shp.bad

/-- The shape of a string over the marked alphabet. -/
def shp (w : List (Bool ⊕ A₁ ⊕ A₂)) : Shp := strTrans shpStep w Shp.start

lemma strTrans_shpStep_bad (w : List (Bool ⊕ A₁ ⊕ A₂)) :
    strTrans shpStep w Shp.bad = Shp.bad := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simpa [strTrans, shpStep] using ih

lemma strTrans_shpStep_inL_ne_inR (w : List (Bool ⊕ A₁ ⊕ A₂)) :
    strTrans shpStep w Shp.inL ≠ Shp.inR := by
  induction w with
  | nil => simp [strTrans]
  | cons x w ih =>
      match x with
      | Sum.inl b =>
          rw [show strTrans shpStep (Sum.inl b :: w) Shp.inL
            = strTrans shpStep w Shp.bad from rfl, strTrans_shpStep_bad]
          simp
      | Sum.inr (Sum.inl a) =>
          rw [show strTrans shpStep (Sum.inr (Sum.inl a) :: w) Shp.inL
            = strTrans shpStep w Shp.inL from rfl]
          exact ih
      | Sum.inr (Sum.inr a) =>
          rw [show strTrans shpStep (Sum.inr (Sum.inr a) :: w) Shp.inL
            = strTrans shpStep w Shp.bad from rfl, strTrans_shpStep_bad]
          simp

lemma strTrans_shpStep_inR_ne_inL (w : List (Bool ⊕ A₁ ⊕ A₂)) :
    strTrans shpStep w Shp.inR ≠ Shp.inL := by
  induction w with
  | nil => simp [strTrans]
  | cons x w ih =>
      match x with
      | Sum.inl b =>
          rw [show strTrans shpStep (Sum.inl b :: w) Shp.inR
            = strTrans shpStep w Shp.bad from rfl, strTrans_shpStep_bad]
          simp
      | Sum.inr (Sum.inr a) =>
          rw [show strTrans shpStep (Sum.inr (Sum.inr a) :: w) Shp.inR
            = strTrans shpStep w Shp.inR from rfl]
          exact ih
      | Sum.inr (Sum.inl a) =>
          rw [show strTrans shpStep (Sum.inr (Sum.inl a) :: w) Shp.inR
            = strTrans shpStep w Shp.bad from rfl, strTrans_shpStep_bad]
          simp

lemma strTrans_shpStep_inL (w : List (Bool ⊕ A₁ ⊕ A₂)) :
    strTrans shpStep w Shp.inL = Shp.inL ↔
      ∃ u : List A₁, w = u.map (fun a => Sum.inr (Sum.inl a)) := by
  induction w with
  | nil => exact ⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩
  | cons x w ih =>
      match x with
      | Sum.inl b =>
          constructor
          · intro h
            rw [show strTrans shpStep (Sum.inl b :: w) Shp.inL
              = strTrans shpStep w Shp.bad from rfl, strTrans_shpStep_bad] at h
            simp at h
          · rintro ⟨u, hu⟩
            cases u with
            | nil => simp at hu
            | cons a u => simp at hu
      | Sum.inr (Sum.inl a) =>
          rw [show strTrans shpStep (Sum.inr (Sum.inl a) :: w) Shp.inL
            = strTrans shpStep w Shp.inL from rfl, ih]
          constructor
          · rintro ⟨u, rfl⟩
            exact ⟨a :: u, rfl⟩
          · rintro ⟨u, hu⟩
            cases u with
            | nil => simp at hu
            | cons a' u =>
                simp only [List.map_cons, List.cons.injEq] at hu
                exact ⟨u, hu.2⟩
      | Sum.inr (Sum.inr a) =>
          constructor
          · intro h
            rw [show strTrans shpStep (Sum.inr (Sum.inr a) :: w) Shp.inL
              = strTrans shpStep w Shp.bad from rfl, strTrans_shpStep_bad] at h
            simp at h
          · rintro ⟨u, hu⟩
            cases u with
            | nil => simp at hu
            | cons a' u => simp at hu

lemma strTrans_shpStep_inR (w : List (Bool ⊕ A₁ ⊕ A₂)) :
    strTrans shpStep w Shp.inR = Shp.inR ↔
      ∃ u : List A₂, w = u.map (fun a => Sum.inr (Sum.inr a)) := by
  induction w with
  | nil => exact ⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩
  | cons x w ih =>
      match x with
      | Sum.inl b =>
          constructor
          · intro h
            rw [show strTrans shpStep (Sum.inl b :: w) Shp.inR
              = strTrans shpStep w Shp.bad from rfl, strTrans_shpStep_bad] at h
            simp at h
          · rintro ⟨u, hu⟩
            cases u with
            | nil => simp at hu
            | cons a u => simp at hu
      | Sum.inr (Sum.inr a) =>
          rw [show strTrans shpStep (Sum.inr (Sum.inr a) :: w) Shp.inR
            = strTrans shpStep w Shp.inR from rfl, ih]
          constructor
          · rintro ⟨u, rfl⟩
            exact ⟨a :: u, rfl⟩
          · rintro ⟨u, hu⟩
            cases u with
            | nil => simp at hu
            | cons a' u =>
                simp only [List.map_cons, List.cons.injEq] at hu
                exact ⟨u, hu.2⟩
      | Sum.inr (Sum.inl a) =>
          constructor
          · intro h
            rw [show strTrans shpStep (Sum.inr (Sum.inl a) :: w) Shp.inR
              = strTrans shpStep w Shp.bad from rfl, strTrans_shpStep_bad] at h
            simp at h
          · rintro ⟨u, hu⟩
            cases u with
            | nil => simp at hu
            | cons a' u => simp at hu

lemma shp_eq_inL_iff (w : List (Bool ⊕ A₁ ⊕ A₂)) :
    shp w = Shp.inL ↔ ∃ u : List A₁, w = mkL A₂ u := by
  cases w with
  | nil =>
      constructor
      · intro h; simp [shp, strTrans] at h
      · rintro ⟨u, hu⟩; simp [mkL] at hu
  | cons x w =>
      match x with
      | Sum.inl false =>
          rw [show shp (Sum.inl false :: w) = strTrans shpStep w Shp.inL from rfl,
            strTrans_shpStep_inL]
          constructor
          · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
          · rintro ⟨u, hu⟩
            simp only [mkL, List.cons.injEq, true_and] at hu
            exact ⟨u, hu⟩
      | Sum.inl true =>
          rw [show shp (Sum.inl true :: w) = strTrans shpStep w Shp.inR from rfl]
          constructor
          · intro h; exact absurd h (strTrans_shpStep_inR_ne_inL w)
          · rintro ⟨u, hu⟩; simp [mkL] at hu
      | Sum.inr y =>
          constructor
          · intro h
            rw [show shp (Sum.inr y :: w) = strTrans shpStep w Shp.bad from rfl,
              strTrans_shpStep_bad] at h
            simp at h
          · rintro ⟨u, hu⟩; simp [mkL] at hu

lemma shp_eq_inR_iff (w : List (Bool ⊕ A₁ ⊕ A₂)) :
    shp w = Shp.inR ↔ ∃ u : List A₂, w = mkR A₁ u := by
  cases w with
  | nil =>
      constructor
      · intro h; simp [shp, strTrans] at h
      · rintro ⟨u, hu⟩; simp [mkR] at hu
  | cons x w =>
      match x with
      | Sum.inl true =>
          rw [show shp (Sum.inl true :: w) = strTrans shpStep w Shp.inR from rfl,
            strTrans_shpStep_inR]
          constructor
          · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
          · rintro ⟨u, hu⟩
            simp only [mkR, List.cons.injEq, true_and] at hu
            exact ⟨u, hu⟩
      | Sum.inl false =>
          rw [show shp (Sum.inl false :: w) = strTrans shpStep w Shp.inL from rfl]
          constructor
          · intro h; exact absurd h (strTrans_shpStep_inL_ne_inR w)
          · rintro ⟨u, hu⟩; simp [mkR] at hu
      | Sum.inr y =>
          constructor
          · intro h
            rw [show shp (Sum.inr y :: w) = strTrans shpStep w Shp.bad from rfl,
              strTrans_shpStep_bad] at h
            simp at h
          · rintro ⟨u, hu⟩; simp [mkR] at hu

@[simp] lemma shp_mkL (u : List A₁) : shp (mkL A₂ u) = Shp.inL :=
  (shp_eq_inL_iff _).2 ⟨u, rfl⟩

@[simp] lemma shp_mkR (u : List A₂) : shp (mkR A₁ u) = Shp.inR :=
  (shp_eq_inR_iff _).2 ⟨u, rfl⟩

/-! ## The specification of the marked sum -/

/-- The specification of the marked sum of `f₁` and `f₂`: marked strings are
mapped to marked strings, and everything else to a fixed string which is not a
marked string. -/
def MSumSpec (f₁ : List A₁ → List B₁) (f₂ : List A₂ → List B₂)
    (F : List (Bool ⊕ A₁ ⊕ A₂) → List (Bool ⊕ B₁ ⊕ B₂)) : Prop :=
  (∀ u, F (mkL A₂ u) = mkL B₂ (f₁ u)) ∧
  (∀ u, F (mkR A₁ u) = mkR B₁ (f₂ u)) ∧
  ∃ bot : List (Bool ⊕ B₁ ⊕ B₂),
    (∀ v : List B₁, bot ≠ mkL B₂ v) ∧ (∀ v : List B₂, bot ≠ mkR B₁ v) ∧
      ∀ w, (∀ u : List A₁, w ≠ mkL A₂ u) → (∀ u : List A₂, w ≠ mkR A₁ u) → F w = bot

/-- The marked sum of `f₁` and `f₂` is regular. -/
def MSum (f₁ : List A₁ → List B₁) (f₂ : List A₂ → List B₂) : Prop :=
  ∃ F : List (Bool ⊕ A₁ ⊕ A₂) → List (Bool ⊕ B₁ ⊕ B₂), IsRegularFun F ∧ MSumSpec f₁ f₂ F

/-- The marked sum only depends on the values of the two functions. -/
lemma MSum.congr {f₁ f₁' : List A₁ → List B₁} {f₂ f₂' : List A₂ → List B₂}
    (h : MSum f₁ f₂) (e₁ : ∀ u, f₁ u = f₁' u) (e₂ : ∀ u, f₂ u = f₂' u) : MSum f₁' f₂' := by
  have h₁ : f₁ = f₁' := funext e₁
  have h₂ : f₂ = f₂' := funext e₂
  exact h₁ ▸ h₂ ▸ h

/-! ## Closure under composition -/

theorem msum_comp {M₁ M₂ : Type} [Finite M₁] [Finite M₂]
    {f₁ : List A₁ → List M₁} {f₂ : List A₂ → List M₂}
    {g₁ : List M₁ → List B₁} {g₂ : List M₂ → List B₂}
    (h : MSum f₁ f₂) (h' : MSum g₁ g₂) :
    MSum (fun w => g₁ (f₁ w)) (fun w => g₂ (f₂ w)) := by
  obtain ⟨F, hFreg, hFL, hFR, bot, hbotL, hbotR, hbot⟩ := h
  obtain ⟨G, hGreg, hGL, hGR, bot', hbot'L, hbot'R, hbot'⟩ := h'
  refine ⟨fun w => G (F w), hFreg.comp' hGreg (fun _ => rfl), fun u => ?_, fun u => ?_,
    bot', hbot'L, hbot'R, fun w hw₁ hw₂ => ?_⟩
  · show G (F (mkL A₂ u)) = _
    rw [hFL u, hGL]
  · show G (F (mkR A₁ u)) = _
    rw [hFR u, hGR]
  · show G (F w) = _
    rw [hbot w hw₁ hw₂]
    exact hbot' bot hbotL hbotR

/-! ## Swapping the two summands -/

/-- The letter map exchanging the two summands (and the two markers). -/
def swapAlph {X Y : Type} : (Bool ⊕ X ⊕ Y) → (Bool ⊕ Y ⊕ X)
  | Sum.inl b => Sum.inl (!b)
  | Sum.inr (Sum.inl a) => Sum.inr (Sum.inr a)
  | Sum.inr (Sum.inr a) => Sum.inr (Sum.inl a)

@[simp] lemma swapAlph_swapAlph {X Y : Type} (x : Bool ⊕ X ⊕ Y) :
    swapAlph (swapAlph x) = x := by
  match x with
  | Sum.inl b => simp [swapAlph]
  | Sum.inr (Sum.inl a) => rfl
  | Sum.inr (Sum.inr a) => rfl

@[simp] lemma map_swapAlph_swapAlph {X Y : Type} (w : List (Bool ⊕ X ⊕ Y)) :
    (w.map swapAlph).map swapAlph = w := by
  simp [List.map_map, Function.comp_def]

lemma map_swapAlph_mkL {X Y : Type} (u : List X) :
    (mkL Y u).map swapAlph = mkR Y u := by
  simp [mkL, mkR, swapAlph, List.map_map, Function.comp_def]

lemma map_swapAlph_mkR {X Y : Type} (u : List Y) :
    (mkR X u).map swapAlph = mkL X u := by
  simp [mkL, mkR, swapAlph, List.map_map, Function.comp_def]

theorem msum_swap [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂} (h : MSum f₁ f₂) : MSum f₂ f₁ := by
  obtain ⟨F, hFreg, hFL, hFR, bot, hbotL, hbotR, hbot⟩ := h
  have hreg : IsRegularFun (fun w : List (Bool ⊕ A₂ ⊕ A₁) => (F (w.map swapAlph)).map swapAlph) :=
    ((isRegularFun_map (swapAlph : (Bool ⊕ A₂ ⊕ A₁) → _)).comp hFreg).comp'
      (isRegularFun_map (swapAlph : (Bool ⊕ B₁ ⊕ B₂) → _)) (fun _ => rfl)
  refine ⟨fun w => (F (w.map swapAlph)).map swapAlph, hreg, fun u => ?_, fun u => ?_,
    bot.map swapAlph, fun v hv => ?_, fun v hv => ?_, fun w hw₁ hw₂ => ?_⟩
  · show (F ((mkL A₁ u).map swapAlph)).map swapAlph = _
    rw [map_swapAlph_mkL, hFR u, map_swapAlph_mkR]
  · show (F ((mkR A₂ u).map swapAlph)).map swapAlph = _
    rw [map_swapAlph_mkR, hFL u, map_swapAlph_mkL]
  · exact hbotR v (by
      have := congrArg (fun z : List (Bool ⊕ B₂ ⊕ B₁) => z.map swapAlph) hv
      simpa [map_swapAlph_mkL, Function.comp_def] using this)
  · exact hbotL v (by
      have := congrArg (fun z : List (Bool ⊕ B₂ ⊕ B₁) => z.map swapAlph) hv
      simpa [map_swapAlph_mkR, Function.comp_def] using this)
  · show (F (w.map swapAlph)).map swapAlph = _
    rw [hbot (w.map swapAlph) (fun u hu => ?_) (fun u hu => ?_)]
    · have := congrArg (fun z : List (Bool ⊕ A₁ ⊕ A₂) => z.map swapAlph) hu
      simp only [map_swapAlph_swapAlph, map_swapAlph_mkL] at this
      exact hw₂ u this
    · have := congrArg (fun z : List (Bool ⊕ A₁ ⊕ A₂) => z.map swapAlph) hu
      simp only [map_swapAlph_swapAlph, map_swapAlph_mkR] at this
      exact hw₁ u this

/-! ## The base case: both functions are the identity -/

open scoped Classical in
theorem msum_id_id [Finite A₁] [Finite A₂] :
    MSum (id : List A₁ → List A₁) (id : List A₂ → List A₂) := by
  classical
  have hrat : IsRationalFun (fun w : List (Bool ⊕ A₁ ⊕ A₂) =>
      if (shp w = Shp.inL ∨ shp w = Shp.inR) then id w else botStr A₁ A₂) :=
    isRationalFun_ite shpStep Shp.start (fun s => s = Shp.inL ∨ s = Shp.inR)
      PrimeRat.rationalFun_id (isRationalFun_const _)
  refine ⟨_, IsRegularFun.of_rational hrat, fun u => ?_, fun u => ?_,
    botStr A₁ A₂, botStr_ne_mkL, botStr_ne_mkR, fun w hw₁ hw₂ => ?_⟩
  · simp
  · simp
  · have h1 : shp w ≠ Shp.inL := fun h => by
      obtain ⟨u, hu⟩ := (shp_eq_inL_iff w).1 h
      exact hw₁ u hu
    have h2 : shp w ≠ Shp.inR := fun h => by
      obtain ⟨u, hu⟩ := (shp_eq_inR_iff w).1 h
      exact hw₂ u hu
    show (if (shp w = Shp.inL ∨ shp w = Shp.inR) then id w else botStr A₁ A₂) = _
    rw [if_neg (by tauto)]

/-! ## The base case: the first function is rational -/

/-- The homomorphism that keeps the letters of the first alphabet. -/
def decL (A₂ : Type) {A₁ : Type} : List (Bool ⊕ A₁ ⊕ A₂) → List A₁ :=
  homOf (fun x => match x with | Sum.inr (Sum.inl a) => [a] | _ => [])

lemma decL_mkL (u : List A₁) : decL A₂ (mkL A₂ u) = u := by
  have key : ∀ u : List A₁,
      homOf (fun x : Bool ⊕ A₁ ⊕ A₂ => match x with | Sum.inr (Sum.inl a) => [a] | _ => [])
        (u.map (fun a => Sum.inr (Sum.inl a))) = u := by
    intro u
    induction u with
    | nil => rfl
    | cons a u ih => simpa [homOf] using ih
  simpa [decL, mkL, homOf] using key u

/-- The homomorphism that keeps the marker and the letters of the second
alphabet. -/
def keepR (B₁ : Type) {A₁ A₂ : Type} : List (Bool ⊕ A₁ ⊕ A₂) → List (Bool ⊕ B₁ ⊕ A₂) :=
  homOf (fun x => match x with
    | Sum.inl b => [Sum.inl b]
    | Sum.inr (Sum.inl _) => []
    | Sum.inr (Sum.inr a) => [Sum.inr (Sum.inr a)])

lemma keepR_mkR (u : List A₂) : keepR B₁ (mkR A₁ u) = mkR B₁ u := by
  have key : ∀ u : List A₂,
      homOf (fun x : Bool ⊕ A₁ ⊕ A₂ => match x with
        | Sum.inl b => [Sum.inl b]
        | Sum.inr (Sum.inl _) => []
        | Sum.inr (Sum.inr a) => [(Sum.inr (Sum.inr a) : Bool ⊕ B₁ ⊕ A₂)])
        (u.map (fun a => Sum.inr (Sum.inr a))) = u.map (fun a => Sum.inr (Sum.inr a)) := by
    intro u
    induction u with
    | nil => rfl
    | cons a u ih => simpa [homOf] using ih
  simpa [keepR, mkR, homOf] using key u

lemma isRationalFun_mkL_fun [Finite A₁] [Finite A₂] :
    IsRationalFun (fun u : List A₁ => mkL A₂ u) := by
  have h := isRationalFun_comp
    (isRationalFun_map (fun a : A₁ => (Sum.inr (Sum.inl a) : Bool ⊕ A₁ ⊕ A₂)))
    (isRationalFun_cons (Sum.inl false : Bool ⊕ A₁ ⊕ A₂))
  exact h

open scoped Classical in
theorem msum_rat_id [Finite A₁] [Finite A₂] [Finite B₁] {f : List A₁ → List B₁}
    (hf : IsRationalFun f) : MSum f (id : List A₂ → List A₂) := by
  classical
  have hinner : IsRationalFun (fun w : List (Bool ⊕ A₁ ⊕ A₂) =>
      if shp w = Shp.inR then keepR B₁ w else botStr B₁ A₂) :=
    isRationalFun_ite shpStep Shp.start (fun s => s = Shp.inR)
      (isRationalFun_homOf _) (isRationalFun_const _)
  have hbranch : IsRationalFun (fun w : List (Bool ⊕ A₁ ⊕ A₂) => mkL A₂ (f (decL A₂ w))) :=
    isRationalFun_comp (isRationalFun_comp (isRationalFun_homOf _) hf) isRationalFun_mkL_fun
  have hrat : IsRationalFun (fun w : List (Bool ⊕ A₁ ⊕ A₂) =>
      if shp w = Shp.inL then mkL A₂ (f (decL A₂ w))
      else if shp w = Shp.inR then keepR B₁ w else botStr B₁ A₂) :=
    isRationalFun_ite shpStep Shp.start (fun s => s = Shp.inL) hbranch hinner
  refine ⟨_, IsRegularFun.of_rational hrat, fun u => ?_, fun u => ?_,
    botStr B₁ A₂, botStr_ne_mkL, botStr_ne_mkR, fun w hw₁ hw₂ => ?_⟩
  · show (if shp (mkL A₂ u) = Shp.inL then mkL A₂ (f (decL A₂ (mkL A₂ u)))
      else if shp (mkL A₂ u) = Shp.inR then keepR B₁ (mkL A₂ u) else botStr B₁ A₂) = _
    rw [shp_mkL, if_pos rfl, decL_mkL]
  · show (if shp (mkR A₁ u) = Shp.inL then mkL A₂ (f (decL A₂ (mkR A₁ u)))
      else if shp (mkR A₁ u) = Shp.inR then keepR B₁ (mkR A₁ u) else botStr B₁ A₂) = _
    rw [shp_mkR, if_neg (by simp), if_pos rfl, keepR_mkR]
    rfl
  · have h1 : shp w ≠ Shp.inL := fun h => by
      obtain ⟨u, hu⟩ := (shp_eq_inL_iff w).1 h
      exact hw₁ u hu
    have h2 : shp w ≠ Shp.inR := fun h => by
      obtain ⟨u, hu⟩ := (shp_eq_inR_iff w).1 h
      exact hw₂ u hu
    show (if shp w = Shp.inL then mkL A₂ (f (decL A₂ w))
      else if shp w = Shp.inR then keepR B₁ w else botStr B₁ A₂) = _
    rw [if_neg h1, if_neg h2]

theorem msum_id_rat [Finite A₁] [Finite A₂] [Finite B₂] {f : List A₂ → List B₂}
    (hf : IsRationalFun f) : MSum (id : List A₁ → List A₁) f :=
  msum_swap (msum_rat_id hf)

end Lax916827Proofs.Transducers
