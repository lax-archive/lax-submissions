/-
Explicit two-way transducers for the identity, for post-composition with a
letter-to-letter map, and for the *block sweeping* functions.

This file provides the constructions that are missing for the corrected form of Corollary
`cor:2dfa-computes-all-regular-functions` of *Transducers* (M. Bojańczyk): the prime regular functions
`map reverse` and `map duplicate` are computed by two-way transducers.

Both of them are instances of one construction: on each block of the input
(a maximal factor that contains no separator) the transducer performs three
sweeps -- left to right, right to left, and left to right again -- emitting a
string for each letter it passes.  For `map reverse` only the middle sweep
produces output, for `map duplicate` only the two outer ones.
-/
import Lax916827Proofs.Source.PartC.TwoWayRat
import Lax916827Proofs.Source.PartC.ContAux
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

open TwoWay

/-! ## The identity function -/

section Ident

variable {A : Type}

/-- The two-way transducer that copies its input. -/
def idAut (A : Type) : TwoWay A A Unit where
  init := ()
  step := fun _ _ r =>
    match r with
    | some a => Sum.inr ((), [a], true)
    | none => Sum.inl []

lemma idAut_reaches (u v : List A) : (idAut A).Reaches (Cfg.conf u () v) v Cfg.halt := by
  induction v generalizing u with
  | nil => exact reaches_one (stepCfg_halt_eq (idAut A) rfl)
  | cons a v ih =>
      have h : (idAut A).step u.getLast? () ((a :: v).head?) = Sum.inr ((), [a], true) := rfl
      simpa using (reaches_one (stepCfg_right_cons (idAut A) h)).trans (ih (u ++ [a]))

/-- The identity is computed by a two-way transducer. -/
theorem isTwoWay_id : IsTwoWay (id : List A → List A) :=
  ⟨Unit, inferInstance, idAut A, fun w => idAut_reaches [] w⟩

end Ident

/-! ## Post-composition with a letter-to-letter map -/

section PostMap

variable {A B C Q : Type}

/-- The transducer `M` with every output letter renamed by `ρ`. -/
def postMapAut (M : TwoWay A B Q) (ρ : B → C) : TwoWay A C Q where
  init := M.init
  step := fun l q r =>
    match M.step l q r with
    | Sum.inl o => Sum.inl (o.map ρ)
    | Sum.inr (q', o, d) => Sum.inr (q', o.map ρ, d)

lemma postMapAut_stepCfg (M : TwoWay A B Q) (ρ : B → C) {c c' : Cfg A Q} {o : List B}
    (h : M.stepCfg c = some (o, c')) :
    (postMapAut M ρ).stepCfg c = some (o.map ρ, c') := by
  obtain ⟨u, q, v, rfl⟩ := exists_conf_of_stepCfg M h
  rcases hM : M.step u.getLast? q v.head? with o' | ⟨q', o', d⟩
  · rw [stepCfg_halt_eq M hM] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact stepCfg_halt_eq (postMapAut M ρ) (by simp only [postMapAut, hM])
  · cases d with
    | true =>
        cases v with
        | nil =>
            rw [stepCfg_right_nil M hM] at h
            exact absurd h (by simp)
        | cons a v' =>
            rw [stepCfg_right_cons M hM] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact stepCfg_right_cons (postMapAut M ρ) (by simp only [postMapAut, hM])
    | false =>
        rcases hu : u.getLast? with _ | a
        · rw [stepCfg_left_none M hu hM] at h
          exact absurd h (by simp)
        · rw [stepCfg_left_some M hu hM] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact stepCfg_left_some (postMapAut M ρ) hu (by simp only [postMapAut, hM])

lemma postMap_reaches (M : TwoWay A B Q) (ρ : B → C) {c c' : Cfg A Q} {o : List B}
    (h : M.Reaches c o c') : (postMapAut M ρ).Reaches c (o.map ρ) c' := by
  induction h with
  | refl c => simpa using Reaches.refl c
  | step hs _ ih =>
      rw [List.map_append]
      exact Reaches.step (postMapAut_stepCfg M ρ hs) ih

/-- Two-way transducers are closed under post-composition with a
letter-to-letter map. -/
theorem isTwoWay_postMap {f : List A → List B} (hf : IsTwoWay f) (ρ : B → C) :
    IsTwoWay (fun w => (f w).map ρ) := by
  obtain ⟨Q, hQ, M, hM⟩ := hf
  exact ⟨Q, hQ, postMapAut M ρ, fun w => postMap_reaches M ρ (hM w)⟩

end PostMap

/-! ## Rational functions -/

/-- Every rational function is computed by a two-way transducer (the case of
Corollary `cor:2dfa-closure-under-composition` in which the second function is the identity). -/
theorem isTwoWay_of_rational {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) : IsTwoWay f := by
  simpa using isTwoWay_comp_rational hf (isTwoWay_id (A := B))

/-! ## Three sweeps over each block -/

section Sweep

variable {A C : Type}

/-- The letter adjacent to the head, provided it is not the separator. -/
def realLet : Option (Option A) → Option A
  | some (some a) => some a
  | _ => none

@[simp] lemma realLet_none : realLet (none : Option (Option A)) = none := rfl
@[simp] lemma realLet_sep : realLet (some none : Option (Option A)) = none := rfl
@[simp] lemma realLet_some (a : A) : realLet (some (some a)) = some a := rfl

/-- The three sweeps that the transducer performs on each block. -/
inductive SwSt
  | s1
  | s2
  | s3
  deriving DecidableEq

instance : Fintype SwSt := ⟨{SwSt.s1, SwSt.s2, SwSt.s3}, fun x => by cases x <;> decide⟩

/-- Crossing the separator that ends a block, or halting at the end of the
input. -/
def sepStep : Option (Option A) → List (Option C) ⊕ (SwSt × List (Option C) × Bool)
  | some none => Sum.inr (SwSt.s1, [none], true)
  | _ => Sum.inl []

/-- The transition function of the sweeping transducer. -/
def sweepStep (o₁ o₂ o₃ : A → List C) (l : Option (Option A)) (st : SwSt)
    (r : Option (Option A)) : List (Option C) ⊕ (SwSt × List (Option C) × Bool) :=
  match st with
  | SwSt.s1 =>
      match realLet r with
      | some a => Sum.inr (SwSt.s1, (o₁ a).map some, true)
      | none =>
          match realLet l with
          | some a => Sum.inr (SwSt.s2, (o₂ a).map some, false)
          | none => sepStep r
  | SwSt.s2 =>
      match realLet l with
      | some a => Sum.inr (SwSt.s2, (o₂ a).map some, false)
      | none =>
          match realLet r with
          | some a => Sum.inr (SwSt.s3, (o₃ a).map some, true)
          | none => sepStep r
  | SwSt.s3 =>
      match realLet r with
      | some a => Sum.inr (SwSt.s3, (o₃ a).map some, true)
      | none => sepStep r

/-- The sweeping transducer. -/
def sweepAut (o₁ o₂ o₃ : A → List C) : TwoWay (Option A) (Option C) SwSt where
  init := SwSt.s1
  step := sweepStep o₁ o₂ o₃

variable (o₁ o₂ o₃ : A → List C) {l r : Option (Option A)} {a : A}

lemma sweepStep_s1_right (hr : realLet r = some a) :
    (sweepAut o₁ o₂ o₃).step l SwSt.s1 r = Sum.inr (SwSt.s1, (o₁ a).map some, true) := by
  simp only [sweepAut, sweepStep, hr]

lemma sweepStep_s1_left (hr : realLet r = none) (hl : realLet l = some a) :
    (sweepAut o₁ o₂ o₃).step l SwSt.s1 r = Sum.inr (SwSt.s2, (o₂ a).map some, false) := by
  simp only [sweepAut, sweepStep, hr, hl]

lemma sweepStep_s1_sep (hr : realLet r = none) (hl : realLet l = none) :
    (sweepAut o₁ o₂ o₃).step l SwSt.s1 r = sepStep r := by
  simp only [sweepAut, sweepStep, hr, hl]

lemma sweepStep_s2_left (hl : realLet l = some a) :
    (sweepAut o₁ o₂ o₃).step l SwSt.s2 r = Sum.inr (SwSt.s2, (o₂ a).map some, false) := by
  simp only [sweepAut, sweepStep, hl]

lemma sweepStep_s2_right (hl : realLet l = none) (hr : realLet r = some a) :
    (sweepAut o₁ o₂ o₃).step l SwSt.s2 r = Sum.inr (SwSt.s3, (o₃ a).map some, true) := by
  simp only [sweepAut, sweepStep, hl, hr]

lemma sweepStep_s3_right (hr : realLet r = some a) :
    (sweepAut o₁ o₂ o₃).step l SwSt.s3 r = Sum.inr (SwSt.s3, (o₃ a).map some, true) := by
  simp only [sweepAut, sweepStep, hr]

lemma sweepStep_s3_sep (hr : realLet r = none) :
    (sweepAut o₁ o₂ o₃).step l SwSt.s3 r = sepStep r := by
  simp only [sweepAut, sweepStep, hr]

/-- The output produced on one block: the three sweeps, the middle one from
right to left. -/
def blockF (o₁ o₂ o₃ : A → List C) (x : List A) : List C :=
  homOf o₁ x ++ homOf o₂ x.reverse ++ homOf o₃ x

/-! ### The three sweeps -/

/-- The first sweep: left to right across a block. -/
lemma sweep1 (x : List A) (rest : List (Option A)) (u : List (Option A)) :
    (sweepAut o₁ o₂ o₃).Reaches (Cfg.conf u SwSt.s1 (x.map some ++ rest))
      ((homOf o₁ x).map some) (Cfg.conf (u ++ x.map some) SwSt.s1 rest) := by
  induction x generalizing u with
  | nil => simpa [homOf] using Reaches.refl (Cfg.conf u SwSt.s1 rest)
  | cons a x ih =>
      have hstep : (sweepAut o₁ o₂ o₃).step u.getLast? SwSt.s1
          ((some a :: (x.map some ++ rest)).head?)
          = Sum.inr (SwSt.s1, (o₁ a).map some, true) :=
        sweepStep_s1_right o₁ o₂ o₃ rfl
      have h1 := reaches_one (stepCfg_right_cons (sweepAut o₁ o₂ o₃) hstep)
      have h2 := ih (u ++ [some a])
      have := h1.trans h2
      simpa [homOf_cons, List.append_assoc] using this

/-- The third sweep: left to right across a block. -/
lemma sweep3 (x : List A) (rest : List (Option A)) (u : List (Option A)) :
    (sweepAut o₁ o₂ o₃).Reaches (Cfg.conf u SwSt.s3 (x.map some ++ rest))
      ((homOf o₃ x).map some) (Cfg.conf (u ++ x.map some) SwSt.s3 rest) := by
  induction x generalizing u with
  | nil => simpa [homOf] using Reaches.refl (Cfg.conf u SwSt.s3 rest)
  | cons a x ih =>
      have hstep : (sweepAut o₁ o₂ o₃).step u.getLast? SwSt.s3
          ((some a :: (x.map some ++ rest)).head?)
          = Sum.inr (SwSt.s3, (o₃ a).map some, true) :=
        sweepStep_s3_right o₁ o₂ o₃ rfl
      have h1 := reaches_one (stepCfg_right_cons (sweepAut o₁ o₂ o₃) hstep)
      have h2 := ih (u ++ [some a])
      have := h1.trans h2
      simpa [homOf_cons, List.append_assoc] using this

/-- The second sweep: right to left across a block. -/
lemma sweep2 (x : List A) (u : List (Option A)) (rest : List (Option A)) :
    (sweepAut o₁ o₂ o₃).Reaches (Cfg.conf (u ++ x.map some) SwSt.s2 rest)
      ((homOf o₂ x.reverse).map some) (Cfg.conf u SwSt.s2 (x.map some ++ rest)) := by
  induction x using List.reverseRecOn generalizing rest with
  | nil => simpa [homOf] using Reaches.refl (Cfg.conf u SwSt.s2 rest)
  | append_singleton y a ih =>
      have hlast : (u ++ (y ++ [a]).map some).getLast? = some (some a) := by
        simp
      have hstep : (sweepAut o₁ o₂ o₃).step ((u ++ (y ++ [a]).map some).getLast?) SwSt.s2
          rest.head? = Sum.inr (SwSt.s2, (o₂ a).map some, false) :=
        sweepStep_s2_left o₁ o₂ o₃ (by rw [hlast]; rfl)
      have h1 := reaches_one (stepCfg_left_some (sweepAut o₁ o₂ o₃) hlast hstep)
      have hdl : (u ++ (y ++ [a]).map some).dropLast = u ++ y.map some := by
        simp [List.map_append]
      rw [hdl] at h1
      have h2 := ih (some a :: rest)
      have := h1.trans h2
      simpa [homOf_cons, List.map_append] using this

/-! ### Turning at the two ends of a block -/

/-- Turning at the right end of a nonempty block: the first sweep is finished,
the second one carries the head back to the left end. -/
lemma sweep12 (y : List A) (a : A) (rest : List (Option A)) (u : List (Option A))
    (hrest : realLet rest.head? = none) :
    (sweepAut o₁ o₂ o₃).Reaches (Cfg.conf (u ++ (y ++ [a]).map some) SwSt.s1 rest)
      ((homOf o₂ (y ++ [a]).reverse).map some)
      (Cfg.conf u SwSt.s2 ((y ++ [a]).map some ++ rest)) := by
  have hlast : (u ++ (y ++ [a]).map some).getLast? = some (some a) := by simp
  have hstep : (sweepAut o₁ o₂ o₃).step ((u ++ (y ++ [a]).map some).getLast?) SwSt.s1
      rest.head? = Sum.inr (SwSt.s2, (o₂ a).map some, false) :=
    sweepStep_s1_left o₁ o₂ o₃ hrest (by rw [hlast]; rfl)
  have h1 := reaches_one (stepCfg_left_some (sweepAut o₁ o₂ o₃) hlast hstep)
  have hdl : (u ++ (y ++ [a]).map some).dropLast = u ++ y.map some := by
    simp [List.map_append]
  rw [hdl] at h1
  have h2 := sweep2 o₁ o₂ o₃ y u (some a :: rest)
  have := h1.trans h2
  simpa [homOf_cons, List.map_append] using this

/-- Turning at the left end of a nonempty block: the second sweep is finished,
the third one carries the head back to the right end. -/
lemma sweep23 (a : A) (x : List A) (rest : List (Option A)) (u : List (Option A))
    (hu : realLet u.getLast? = none) :
    (sweepAut o₁ o₂ o₃).Reaches (Cfg.conf u SwSt.s2 ((a :: x).map some ++ rest))
      ((homOf o₃ (a :: x)).map some)
      (Cfg.conf (u ++ (a :: x).map some) SwSt.s3 rest) := by
  have hstep : (sweepAut o₁ o₂ o₃).step u.getLast? SwSt.s2
      ((some a :: (x.map some ++ rest)).head?)
      = Sum.inr (SwSt.s3, (o₃ a).map some, true) :=
    sweepStep_s2_right o₁ o₂ o₃ hu rfl
  have h1 := reaches_one (stepCfg_right_cons (sweepAut o₁ o₂ o₃) hstep)
  have h2 := sweep3 o₁ o₂ o₃ x rest (u ++ [some a])
  have := h1.trans h2
  simpa [homOf_cons, List.append_assoc] using this

/-! ### The whole run -/

/-- Every string splits as a block followed by the rest. -/
lemma block_split (v : List (Option A)) :
    ∃ (x : List A) (rest : List (Option A)), v = x.map some ++ rest ∧
      (rest = [] ∨ ∃ r', rest = none :: r') := by
  induction v with
  | nil => exact ⟨[], [], rfl, Or.inl rfl⟩
  | cons c v ih =>
      cases c with
      | none => exact ⟨[], none :: v, rfl, Or.inr ⟨v, rfl⟩⟩
      | some a =>
          obtain ⟨x, rest, hv, hr⟩ := ih
          exact ⟨a :: x, rest, by rw [List.map_cons, List.cons_append, ← hv], hr⟩

/-- The output of the three sweeps over a whole block, followed by the crossing
of the separator. -/
lemma sweep_reaches (n : ℕ) : ∀ (v : List (Option A)), v.length ≤ n →
    ∀ u : List (Option A), realLet u.getLast? = none →
      (sweepAut o₁ o₂ o₃).Reaches (Cfg.conf u SwSt.s1 v)
        (mapLift (blockF o₁ o₂ o₃) v) Cfg.halt := by
  induction n with
  | zero =>
      intro v hv u hu
      have hvnil : v = [] := by
        simpa using List.length_eq_zero_iff.mp (Nat.le_zero.mp hv)
      subst hvnil
      have hstep : (sweepAut o₁ o₂ o₃).step u.getLast? SwSt.s1 (([] : List (Option A)).head?)
          = Sum.inl [] := sweepStep_s1_sep o₁ o₂ o₃ rfl hu
      have hout : mapLift (blockF o₁ o₂ o₃) ([] : List (Option A)) = [] := by
        have := mapLift_map_some (blockF o₁ o₂ o₃) ([] : List A)
        simpa [blockF, homOf] using this
      rw [hout]
      exact reaches_one (stepCfg_halt_eq (sweepAut o₁ o₂ o₃) hstep)
  | succ n ih =>
      intro v hv u hu
      obtain ⟨x, rest, rfl, hrest⟩ := block_split v
      have hrhead : realLet rest.head? = none := by
        rcases hrest with rfl | ⟨r', rfl⟩ <;> simp
      -- the three sweeps over the block
      have hblock : (sweepAut o₁ o₂ o₃).Reaches (Cfg.conf u SwSt.s1 (x.map some ++ rest))
          ((blockF o₁ o₂ o₃ x).map some) (Cfg.conf (u ++ x.map some) SwSt.s3 rest) ∨
          (x = [] ∧ (blockF o₁ o₂ o₃ x).map some = ([] : List (Option C))) := by
        rcases x.eq_nil_or_concat with rfl | ⟨y, a, rfl⟩
        · exact Or.inr ⟨rfl, by simp [blockF, homOf]⟩
        · refine Or.inl ?_
          have h1 := sweep1 o₁ o₂ o₃ (y ++ [a]) rest u
          have h2 := sweep12 o₁ o₂ o₃ y a rest u hrhead
          have h3 : (sweepAut o₁ o₂ o₃).Reaches
              (Cfg.conf u SwSt.s2 ((y ++ [a]).map some ++ rest))
              ((homOf o₃ (y ++ [a])).map some)
              (Cfg.conf (u ++ (y ++ [a]).map some) SwSt.s3 rest) := by
            rcases y with _ | ⟨b, y'⟩
            · simpa using sweep23 o₁ o₂ o₃ a [] rest u hu
            · simpa using sweep23 o₁ o₂ o₃ b (y' ++ [a]) rest u hu
          have := (h1.trans h2).trans h3
          simpa [blockF, List.map_append, List.append_assoc] using this
      -- crossing the separator, or halting
      rcases hrest with rfl | ⟨r', rfl⟩
      · -- the last block
        have hout : mapLift (blockF o₁ o₂ o₃) (x.map some ++ [])
            = (blockF o₁ o₂ o₃ x).map some := by
          simpa using mapLift_map_some (blockF o₁ o₂ o₃) x
        rw [hout]
        rcases hblock with h | ⟨rfl, hnil⟩
        · have hstep : (sweepAut o₁ o₂ o₃).step (u ++ x.map some).getLast? SwSt.s3
              (([] : List (Option A)).head?) = Sum.inl [] :=
            sweepStep_s3_sep o₁ o₂ o₃ rfl
          simpa using h.trans (reaches_one (stepCfg_halt_eq (sweepAut o₁ o₂ o₃) hstep))
        · rw [hnil]
          have hstep : (sweepAut o₁ o₂ o₃).step u.getLast? SwSt.s1
              (([] : List (Option A)).head?) = Sum.inl [] :=
            sweepStep_s1_sep o₁ o₂ o₃ rfl hu
          simpa using reaches_one (stepCfg_halt_eq (sweepAut o₁ o₂ o₃) hstep)
      · -- one more separator
        have hlen : r'.length ≤ n := by
          simp only [List.length_append, List.length_map, List.length_cons] at hv
          omega
        have hout : mapLift (blockF o₁ o₂ o₃) (x.map some ++ none :: r')
            = (blockF o₁ o₂ o₃ x).map some ++ none :: mapLift (blockF o₁ o₂ o₃) r' :=
          mapLift_map_some_cons_none _ _ _
        rw [hout]
        rcases hblock with h | ⟨rfl, hnil⟩
        · have hstep : (sweepAut o₁ o₂ o₃).step (u ++ x.map some).getLast? SwSt.s3
              ((none :: r').head?) = Sum.inr (SwSt.s1, [none], true) := by
            rw [sweepStep_s3_sep o₁ o₂ o₃ (by simp)]
            rfl
          have h1 := reaches_one (stepCfg_right_cons (sweepAut o₁ o₂ o₃) hstep)
          have hu' : realLet ((u ++ x.map some) ++ [none]).getLast? = none := by simp
          have h2 := ih r' hlen ((u ++ x.map some) ++ [none]) hu'
          have := (h.trans h1).trans h2
          simpa using this
        · rw [hnil]
          have hstep : (sweepAut o₁ o₂ o₃).step u.getLast? SwSt.s1 ((none :: r').head?)
              = Sum.inr (SwSt.s1, [none], true) :=
            sweepStep_s1_sep o₁ o₂ o₃ rfl hu
          have h1 := reaches_one (stepCfg_right_cons (sweepAut o₁ o₂ o₃) hstep)
          have hu' : realLet (u ++ [none]).getLast? = none := by simp
          have h2 := ih r' hlen (u ++ [none]) hu'
          have := h1.trans h2
          simpa using this

/-- The sweeping transducer computes the map lifting of the block function. -/
theorem isTwoWay_mapLift_sweep (o₁ o₂ o₃ : A → List C) :
    IsTwoWay (mapLift (blockF o₁ o₂ o₃)) :=
  ⟨SwSt, inferInstance, sweepAut o₁ o₂ o₃,
    fun v => sweep_reaches o₁ o₂ o₃ v.length v (le_refl _) [] rfl⟩

/-! ### The two block functions we need -/

lemma homOf_nil_fun (x : List A) : homOf (fun _ : A => ([] : List C)) x = [] := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [homOf_cons, ih]; rfl

lemma homOf_single (x : List A) : homOf (fun a : A => [a]) x = x := by
  induction x with
  | nil => rfl
  | cons a x ih => rw [homOf_cons, ih]; rfl

lemma blockF_reverse :
    blockF (fun _ : A => ([] : List A)) (fun a => [a]) (fun _ => []) = List.reverse := by
  funext x
  rw [blockF, homOf_nil_fun, homOf_single]
  simp

lemma blockF_dup :
    blockF (fun a : A => [a]) (fun _ => ([] : List A)) (fun a => [a]) = fun x => x ++ x := by
  funext x
  rw [blockF, homOf_single, homOf_nil_fun]
  simp

end Sweep

end Lax916827Proofs.Transducers
