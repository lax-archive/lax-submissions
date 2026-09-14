/-
Part D: the map liftings of the "reverse and repeat" functions are computed by for-transducers.

The prime regular functions that are not rational are map reverse and map duplicate
(`RequestProject/PartC/RegularDef.lean`).  Both are map liftings of a function of the shape
`u ↦ u.reverse ++ ⋯ ++ u.reverse`: map reverse is the map lifting of `List.reverse`, and map
duplicate is the map lifting of `List.reverse` composed with the map lifting of
`u ↦ u.reverse ++ u.reverse`, because `(u.reverse ++ u.reverse).reverse = u ++ u`.

This file first develops the decomposition of a string over `A + 1` into its last block and the
blocks before it, then builds a machine program (`RequestProject/PartD/ForMachine.lean`) computing
the map lifting of `u ↦ u.reverse ++ ⋯ ++ u.reverse`, and finally deduces that map reverse and
map duplicate are computed by for-transducers.
-/
import Lax194892Proofs.Source.PartD.ForMachine
import Lax765601Proofs.Source.PartA.MapLift
import Lax916827Proofs.Source.PartC.MapLiftAux
import Lax194892Proofs.Source.PartD.ForCompTop
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

variable {A B : Type}

/-! ## The last block of a string over `A + 1` -/

/-- The last block of a string over `A + 1`, that is, the part after the last separator. -/
def lastBlk (w : List (Option A)) : List A := (splitSep w).getLast (splitSep_ne_nil w)

/-- The blocks of a string over `A + 1` other than the last one. -/
def initBlks (w : List (Option A)) : List (List A) := (splitSep w).dropLast

lemma splitSep_eq_initBlks (w : List (Option A)) :
    splitSep w = initBlks w ++ [lastBlk w] :=
  (List.dropLast_append_getLast (splitSep_ne_nil w)).symm

lemma splitSep_append_none (w : List (Option A)) :
    splitSep (w ++ [none]) = splitSep w ++ [[]] := by
  induction w with
  | nil => rfl
  | cons x w ih =>
      cases x with
      | none =>
          show [] :: splitSep (w ++ [none]) = ([] :: splitSep w) ++ [[]]
          rw [ih]; rfl
      | some a =>
          show (match splitSep (w ++ [none]) with
                | [] => [[a]]
                | u :: us => (a :: u) :: us)
              = (match splitSep w with
                | [] => [[a]]
                | u :: us => (a :: u) :: us) ++ [[]]
          rw [ih]
          cases h : splitSep w with
          | nil => exact absurd h (splitSep_ne_nil w)
          | cons u us => rfl

/-- Appending a letter to a string extends its last block. -/
lemma splitSep_append_some_aux : ∀ (w : List (Option A)) (a : A) (us : List (List A))
    (u : List A), splitSep w = us ++ [u] → splitSep (w ++ [some a]) = us ++ [u ++ [a]] := by
  intro w
  induction w with
  | nil =>
      intro a us u h
      have hus : us = [] := by
        have hlen : us.length + 1 = 1 := by
          have := congrArg List.length h
          simpa [splitSep] using this.symm
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hus
      have hu : u = [] := by simpa [splitSep] using h.symm
      subst hu
      rfl
  | cons x w ih =>
      intro a us u h
      cases x with
      | none =>
          have h' : ([] : List A) :: splitSep w = us ++ [u] := h
          cases us with
          | nil =>
              exfalso
              have : splitSep w = [] := by simpa using congrArg List.tail h'
              exact splitSep_ne_nil w this
          | cons c us' =>
              have hc : c = [] := ((List.cons.injEq _ _ _ _ ▸ h').1).symm
              have hrest : splitSep w = us' ++ [u] := (List.cons.injEq _ _ _ _ ▸ h').2
              show ([] : List A) :: splitSep (w ++ [some a]) = (c :: us') ++ [u ++ [a]]
              rw [ih a us' u hrest, hc]
              rfl
      | some b =>
          cases hw : splitSep w with
          | nil => exact absurd hw (splitSep_ne_nil w)
          | cons v vs =>
              have hbw : splitSep (some b :: w) = (b :: v) :: vs := by
                show (match splitSep w with
                      | [] => [[b]]
                      | u :: us => (b :: u) :: us) = _
                rw [hw]
              rw [hbw] at h
              cases us with
              | nil =>
                  have h1 : b :: v = u := (List.cons.injEq _ _ _ _ ▸ h).1
                  have h2 : vs = [] := by simpa using (List.cons.injEq _ _ _ _ ▸ h).2
                  have hrest : splitSep w = [] ++ [v] := by rw [hw, h2]; rfl
                  show (match splitSep (w ++ [some a]) with
                        | [] => [[b]]
                        | u :: us => (b :: u) :: us) = [] ++ [u ++ [a]]
                  rw [ih a [] v hrest, ← h1]
                  rfl
              | cons c us' =>
                  have h1 : b :: v = c := (List.cons.injEq _ _ _ _ ▸ h).1
                  have h2 : vs = us' ++ [u] := (List.cons.injEq _ _ _ _ ▸ h).2
                  have hrest : splitSep w = (v :: us') ++ [u] := by rw [hw, h2]; rfl
                  show (match splitSep (w ++ [some a]) with
                        | [] => [[b]]
                        | u :: us => (b :: u) :: us) = (c :: us') ++ [u ++ [a]]
                  rw [ih a (v :: us') u hrest, ← h1]
                  rfl

lemma splitSep_append_some (w : List (Option A)) (a : A) :
    splitSep (w ++ [some a]) = initBlks w ++ [lastBlk w ++ [a]] :=
  splitSep_append_some_aux w a (initBlks w) (lastBlk w) (splitSep_eq_initBlks w)

@[simp] lemma lastBlk_nil : lastBlk ([] : List (Option A)) = [] := by
  simp [lastBlk, splitSep]

@[simp] lemma initBlks_nil : initBlks ([] : List (Option A)) = [] := by
  simp [initBlks, splitSep]

@[simp] lemma lastBlk_append_none (w : List (Option A)) : lastBlk (w ++ [none]) = [] := by
  simp [lastBlk, splitSep_append_none]

@[simp] lemma initBlks_append_none (w : List (Option A)) : initBlks (w ++ [none]) = splitSep w := by
  simp [initBlks, splitSep_append_none]

@[simp] lemma lastBlk_append_some (w : List (Option A)) (a : A) :
    lastBlk (w ++ [some a]) = lastBlk w ++ [a] := by
  simp [lastBlk, splitSep_append_some]

@[simp] lemma initBlks_append_some (w : List (Option A)) (a : A) :
    initBlks (w ++ [some a]) = initBlks w := by
  simp [initBlks, splitSep_append_some]

/-! ## The map lifting split at the last block -/

lemma intercalate_append_singleton (sep : List B) (ls : List (List B)) (x : List B) :
    List.intercalate sep (ls ++ [x]) = (ls.map (fun u => u ++ sep)).flatten ++ x := by
  induction ls with
  | nil => simp [List.intercalate]
  | cons u ls ih =>
      rw [List.cons_append, intercalate_cons_cons _ _ _ (by simp), ih]
      simp

/-- The map lifting, split into the blocks before the last one and the last block. -/
lemma mapLift_eq_initBlks (f : List A → List B) (w : List (Option A)) :
    mapLift f w = ((initBlks w).map (fun u => (f u).map some ++ [none])).flatten
      ++ (f (lastBlk w)).map some := by
  rw [mapLift, splitSep_eq_initBlks w, List.map_append, List.map_cons, List.map_nil,
    intercalate_append_singleton, List.map_map]
  rfl


/-! ## The machine program -/

/-- `revRep m u` is the reverse of `u`, repeated `m` times. -/
def revRep (A : Type) : ℕ → List A → List A
  | 0, _ => []
  | m + 1, u => u.reverse ++ revRep A m u

@[simp] lemma revRep_one (u : List A) : revRep A 1 u = u.reverse := by
  simp [revRep]

lemma revRep_two_reverse (u : List A) : (revRep A 2 u).reverse = u ++ u := by
  simp [revRep]

/-- Emit the letter under the inner position while the current block has not been left. -/
def revEmit (q : Bool × Bool) (oa : Option (Option A)) : (Bool × Bool) × List (Option A) :=
  if q.2 then
    match oa with
    | some (some a) => ((q.1, true), [some a])
    | _ => ((q.1, false), [])
  else (q, [])

@[simp] lemma revEmit_off (b : Bool) (oa : Option (Option A)) :
    revEmit (b, false) oa = ((b, false), []) := rfl

@[simp] lemma revEmit_on_sep (b : Bool) :
    revEmit (b, true) (some (none : Option A)) = ((b, false), []) := rfl

@[simp] lemma revEmit_on_letter (b : Bool) (a : A) :
    revEmit (b, true) (some (some a)) = ((b, true), [some a]) := rfl

/-- The step of the inner loop of the outer body: the scan is switched on at the position of the
outer loop, and then emits the letters of the block until the previous separator. -/
def revStepF (q : Bool × Bool) (oa _ob : Option (Option A)) (c₁ c₂ : Bool) :
    (Bool × Bool) × List (Option A) :=
  if q.1 && c₁ && c₂ then ((true, true), []) else revEmit q oa

lemma revStepF_trigger (oa ob : Option (Option A)) :
    revStepF (true, false) oa ob true true = ((true, true), []) := rfl

lemma revStepF_no_trigger (q : Bool × Bool) (oa ob : Option (Option A)) (c₁ : Bool) :
    revStepF q oa ob c₁ false = revEmit q oa := by simp [revStepF]

/-- Two folds with the same steps on the list at hand agree. -/
lemma runList_congr_step {S α B : Type} (step₁ step₂ : S → α → S × List B) (as : List α)
    (h : ∀ a ∈ as, ∀ s, step₁ s a = step₂ s a) (s : S) :
    runList step₁ as s = runList step₂ as s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      rw [runList_cons, runList_cons, h a (by simp) s,
        ih (fun b hb => h b (by simp [hb])) (step₂ s a).1]

/-- If every step produces the same output whatever the state, the fold produces their
concatenation. -/
lemma runList_snd_of_indep {S α B : Type} (step : S → α → S × List B) (out : α → List B)
    (as : List α) (h : ∀ a ∈ as, ∀ s : S, (step s a).2 = out a) (s : S) :
    (runList step as s).2 = (as.map out).flatten := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      rw [runList_cons]
      simp only [List.map_cons, List.flatten_cons, h a (by simp),
        ih (fun b hb => h b (by simp [hb]))]

variable (w : List (Option A))

/-- Once the scan is off it stays off and emits nothing. -/
lemma runList_revEmit_off (ys : List ℕ) (b : Bool) :
    runList (fun (q : Bool × Bool) (y : ℕ) => revEmit q (w[y]?)) ys (b, false)
      = ((b, false), []) :=
  runList_noop _ _ _ (fun _ _ => revEmit_off b _)

/-- The scan of a switched-on backward loop emits the reverse of the last block. -/
lemma runList_revEmit_on : ∀ n, n ≤ w.length → ∀ b : Bool, ∃ c : Bool,
    runList (fun (q : Bool × Bool) (y : ℕ) => revEmit q (w[y]?)) (List.range n).reverse (b, true)
      = ((b, c), ((lastBlk (w.take n)).reverse.map some)) := by
  intro n
  induction n with
  | zero => intro _ b; exact ⟨true, by simp⟩
  | succ n ih =>
      intro hn b
      have hnw : n < w.length := by omega
      have hsucc : w.take (n + 1) = w.take n ++ [w[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hnw]; rfl
      have hrev : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
        rw [List.range_succ, List.reverse_append]; rfl
      have hget : w[n]? = some w[n] := List.getElem?_eq_getElem hnw
      rw [hrev, runList_cons]
      cases hw : w[n] with
      | none =>
          refine ⟨false, ?_⟩
          simp only [hget, hw, revEmit_on_sep, runList_revEmit_off]
          simp [hsucc, hw]
      | some a =>
          obtain ⟨c, hc⟩ := ih (by omega) b
          refine ⟨c, ?_⟩
          simp only [hget, hw, revEmit_on_letter, hc]
          simp [hsucc, hw]

/-- An inactive outer iteration does nothing. -/
lemma runList_revStep_off (x : ℕ) (ys : List ℕ) :
    runList (fun (q : Bool × Bool) (y : ℕ) =>
        revStepF q (w[y]?) (w[x]?) (decide (y ≤ x)) (decide (x ≤ y))) ys (false, false)
      = ((false, false), []) :=
  runList_noop _ _ _ (fun _ _ => by simp [revStepF])

/-- An active outer iteration at the position `x` emits the reverse of the block that ends
just before `x`. -/
lemma runList_revStep_on (x : ℕ) : ∀ n, x < n → n ≤ w.length → ∃ c : Bool,
    runList (fun (q : Bool × Bool) (y : ℕ) =>
        revStepF q (w[y]?) (w[x]?) (decide (y ≤ x)) (decide (x ≤ y))) (List.range n).reverse
      (true, false)
      = ((true, c), ((lastBlk (w.take x)).reverse.map some)) := by
  intro n hxn
  induction n, hxn using Nat.le_induction with
  | base =>
      intro hn
      have hrev : (List.range (x + 1)).reverse = x :: (List.range x).reverse := by
        rw [List.range_succ, List.reverse_append]; rfl
      obtain ⟨c, hc⟩ := runList_revEmit_on w x (by omega) true
      refine ⟨c, ?_⟩
      have hcong : runList (fun (q : Bool × Bool) (y : ℕ) =>
            revStepF q (w[y]?) (w[x]?) (decide (y ≤ x)) (decide (x ≤ y))) (List.range x).reverse
          = runList (fun (q : Bool × Bool) (y : ℕ) => revEmit q (w[y]?))
              (List.range x).reverse := by
        funext s
        refine runList_congr_step _ _ _ (fun y hy q => ?_) s
        have hyx : y < x := List.mem_range.mp (List.mem_reverse.mp hy)
        rw [show decide (x ≤ y) = false from decide_eq_false (by omega), revStepF_no_trigger]
      rw [hrev, runList_cons]
      simp only [le_refl, decide_true, revStepF_trigger, hcong]
      simp [hc]
  | succ n hxn ih =>
      intro hn
      obtain ⟨c, hc⟩ := ih (by omega)
      refine ⟨c, ?_⟩
      have hrev : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
        rw [List.range_succ, List.reverse_append]; rfl
      have hstep : revStepF (true, false) (w[n]?) (w[x]?) (decide (n ≤ x)) (decide (x ≤ n))
          = ((true, false), []) := by
        rw [show decide (n ≤ x) = false from decide_eq_false (by omega)]
        simp [revStepF]
      rw [hrev, runList_cons]
      simp only [hstep]
      simp [hc]

/-! ### The program -/

/-- The inner loop of the outer body. -/
def revInner : MProg (Option A) (Option A) (Bool × Bool) :=
  MProg.loop false 1 (MProg.act2 1 0 revStepF)

/-- The inner loop of the epilogue. -/
def epiInner : MProg (Option A) (Option A) (Bool × Bool) :=
  MProg.loop false 1 (MProg.act2 1 1 (fun q oa _ _ _ => revEmit q oa))

/-- The `m` copies of the block emitted at an active outer iteration, followed by a separator. -/
def revCopies (A : Type) : ℕ → MProg (Option A) (Option A) (Bool × Bool)
  | 0 => MProg.act (fun q => (q, if q.1 then [none] else []))
  | m + 1 => MProg.seq (MProg.act (fun q => ((q.1, false), [])))
      (MProg.seq revInner (revCopies A m))

/-- The `m` copies of the last block, emitted after the outer loop. -/
def epiCopies (A : Type) : ℕ → MProg (Option A) (Option A) (Bool × Bool)
  | 0 => MProg.act (fun q => (q, []))
  | m + 1 => MProg.seq (MProg.act (fun q => ((q.1, true), [])))
      (MProg.seq epiInner (epiCopies A m))

/-- Whether the letter under a position variable is the separator. -/
def isSepAt : Option (Option A) → Bool
  | some none => true
  | _ => false

/-- The machine program computing the map lifting of `revRep A m`. -/
def revProg (A : Type) (m : ℕ) : MProg (Option A) (Option A) (Bool × Bool) :=
  MProg.seq
    (MProg.loop true 0 (MProg.seq
      (MProg.act2 0 0 (fun _ oa _ _ _ => ((isSepAt oa, false), [])))
      (revCopies A m)))
    (epiCopies A m)

lemma sem_revInner (pos : ℕ → ℕ) (q : Bool × Bool) :
    MProg.sem w revInner pos q
      = runList (fun (q' : Bool × Bool) (y : ℕ) =>
          revStepF q' (w[y]?) (w[pos 0]?) (decide (y ≤ pos 0)) (decide (pos 0 ≤ y)))
        (List.range w.length).reverse q := by
  rw [revInner]
  simp only [MProg.sem_loop, MProg.sem_act2, loopRange_false]
  refine runList_congr_step _ _ _ (fun y _ q' => ?_) q
  rw [Function.update_self, Function.update_of_ne (by decide)]

lemma sem_epiInner (pos : ℕ → ℕ) (q : Bool × Bool) :
    MProg.sem w epiInner pos q
      = runList (fun (q' : Bool × Bool) (y : ℕ) => revEmit q' (w[y]?))
        (List.range w.length).reverse q := by
  rw [epiInner]
  simp only [MProg.sem_loop, MProg.sem_act2, loopRange_false]
  refine runList_congr_step _ _ _ (fun y _ q' => ?_) q
  rw [Function.update_self]

lemma sem_revCopies (x : ℕ) (hx : x < w.length) (pos : ℕ → ℕ) (hpos : pos 0 = x) :
    ∀ (m : ℕ) (q : Bool × Bool), ∃ c : Bool,
      MProg.sem w (revCopies A m) pos q
        = ((q.1, c),
            if q.1 then (revRep A m (lastBlk (w.take x))).map some ++ [none] else []) := by
  intro m
  induction m with
  | zero => intro q; exact ⟨q.2, by cases q with | mk b e => cases b <;> simp [revCopies, revRep]⟩
  | succ m ih =>
      intro q
      rw [revCopies]
      simp only [MProg.sem_seq, MProg.sem_act]
      rw [sem_revInner, hpos]
      cases hq : q.1 with
      | false =>
          rw [runList_revStep_off]
          obtain ⟨c, hc⟩ := ih (false, false)
          refine ⟨c, ?_⟩
          rw [hc]
          simp
      | true =>
          obtain ⟨c₀, hc₀⟩ := runList_revStep_on w x w.length hx le_rfl
          rw [hc₀]
          obtain ⟨c, hc⟩ := ih (true, c₀)
          refine ⟨c, ?_⟩
          rw [hc]
          simp [revRep, List.map_append]

lemma sem_epiCopies (pos : ℕ → ℕ) :
    ∀ (m : ℕ) (q : Bool × Bool), ∃ c : Bool,
      MProg.sem w (epiCopies A m) pos q = ((q.1, c), (revRep A m (lastBlk w)).map some) := by
  intro m
  induction m with
  | zero => intro q; exact ⟨q.2, by simp [epiCopies, revRep]⟩
  | succ m ih =>
      intro q
      rw [epiCopies]
      simp only [MProg.sem_seq, MProg.sem_act]
      rw [sem_epiInner]
      obtain ⟨c₀, hc₀⟩ := runList_revEmit_on w w.length le_rfl q.1
      rw [List.take_length] at hc₀
      rw [hc₀]
      obtain ⟨c, hc⟩ := ih (q.1, c₀)
      refine ⟨c, ?_⟩
      rw [hc]
      simp [revRep, List.map_append]

/-- The output of one iteration of the outer loop. -/
def revOutAt (A : Type) (m : ℕ) (w : List (Option A)) (i : ℕ) : List (Option A) :=
  if isSepAt (w[i]?) then (revRep A m (lastBlk (w.take i))).map some ++ [none] else []

lemma sem_outerBody (m : ℕ) (pos : ℕ → ℕ) (i : ℕ) (hi : i < w.length) (q : Bool × Bool) :
    (MProg.sem w (MProg.seq
        (MProg.act2 0 0 (fun _ oa _ _ _ => ((isSepAt oa, false), ([] : List (Option A)))))
        (revCopies A m)) (Function.update pos 0 i) q).2 = revOutAt A m w i := by
  have hpos : (Function.update pos 0 i) 0 = i := Function.update_self _ _ _
  simp only [MProg.sem_seq, MProg.sem_act2, hpos]
  obtain ⟨c, hc⟩ := sem_revCopies w i hi (Function.update pos 0 i) hpos m
    (isSepAt (w[i]?), false)
  rw [hc]
  cases h : isSepAt (w[i]?) <;> simp [revOutAt, h]

lemma outer_flatten (m : ℕ) : ∀ w : List (Option A),
    ((List.range w.length).map (revOutAt A m w)).flatten
      = ((initBlks w).map (fun u => (revRep A m u).map some ++ [none])).flatten := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton v a ih =>
      have hlen : (v ++ [a]).length = v.length + 1 := by simp
      have hsame : ∀ i ∈ List.range v.length, revOutAt A m (v ++ [a]) i = revOutAt A m v i := by
        intro i hi
        have hi' : i < v.length := List.mem_range.mp hi
        rw [revOutAt, revOutAt, List.getElem?_append_left hi',
          List.take_append_of_le_length (le_of_lt hi')]
      rw [hlen, List.range_succ, List.map_append, List.flatten_append,
        List.map_congr_left hsame, ih]
      have hlast : (v ++ [a])[v.length]? = some a := by simp
      cases a with
      | none =>
          have htake : (v ++ [none]).take v.length = v := by simp
          rw [initBlks_append_none, splitSep_eq_initBlks v, List.map_append, List.flatten_append]
          simp [revOutAt, isSepAt, htake]
      | some b =>
          rw [initBlks_append_some]
          simp [revOutAt, isSepAt]

lemma sem_revProg (m : ℕ) (pos : ℕ → ℕ) (q : Bool × Bool) :
    (MProg.sem w (revProg A m) pos q).2 = mapLift (revRep A m) w := by
  rw [revProg, MProg.sem_seq, MProg.sem_loop, loopRange_true]
  rw [runList_snd_of_indep _ (revOutAt A m w) _
    (fun i hi s => sem_outerBody w m pos i (List.mem_range.mp hi) s)]
  obtain ⟨c, hc⟩ := sem_epiCopies w pos m _
  rw [hc, outer_flatten, mapLift_eq_initBlks]

/-- **The map lifting of `revRep A m` is computed by a for-transducer.** -/
theorem isForTransducer_mapLift_revRep (A : Type) [Finite A] (m : ℕ) :
    IsForTransducer (mapLift (revRep A m)) :=
  isForTransducer_of_mprog (revProg A m) (false, false) _
    (fun w => sem_revProg w m (fun _ => 0) (false, false))

/-- **Map reverse is computed by a for-transducer.** -/
theorem isForTransducer_mapReverse (A : Type) [Finite A] :
    IsForTransducer (mapReverse A) := by
  have h : revRep A 1 = (List.reverse : List A → List A) := by funext u; simp
  rw [mapReverse, ← h]
  exact isForTransducer_mapLift_revRep A 1

/-- **Map duplicate is computed by a for-transducer.** -/
theorem isForTransducer_mapDuplicate (A : Type) [Finite A] :
    IsForTransducer (mapDuplicate A) := by
  have hcomp : (List.reverse : List A → List A) ∘ revRep A 2 = fun u => u ++ u := by
    funext u; exact revRep_two_reverse u
  obtain ⟨P, hP⟩ := forTransducer_comp_aux (isForTransducer_mapLift_revRep A 2)
    (isForTransducer_mapReverse A)
  refine ⟨P, fun v => (hP v).trans ?_⟩
  show mapReverse A (mapLift (revRep A 2) v) = mapDuplicate A v
  rw [mapReverse, ← Function.comp_apply (f := mapLift (List.reverse : List A → List A)),
    ← mapLift_comp' (revRep A 2) List.reverse, hcomp, mapDuplicate]

end Lax194892Proofs.Transducers
