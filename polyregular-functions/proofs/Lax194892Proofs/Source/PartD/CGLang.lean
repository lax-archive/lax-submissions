/-
**The string representation of a configuration, with one marked position.**

Section D.2 of *Transducers* (M. Bojańczyk) computes the child configuration graph of a
configuration of a pebble transducer by an automaton that reads the string representation of the
configuration.  In order to build that automaton from the reachability language of
`RequestProject/PartD/PebReach.lean`, one has to turn a *marked* string representation of a
configuration -- a string over `Transducers.CG.ConfLetter` with one or two distinguished positions
-- into the string representation of a *pair* of configurations, over
`Transducers.PebEnc.PairLetter`.

This file does exactly that.  A `Transducers.CGL.Spot` names a position of the input relative to
the two marks: the first gap, the mark, its two neighbours, the second mark, or no position at all.
`Transducers.CGL.pairMap` reads a *window* of three consecutive letters of the marked string and
produces the corresponding pair letter, adding a pebble in the named position on top of the stack;
the key lemma `Transducers.CGL.pairMap_confEnc` says that on a genuine marked string representation
of a configuration the result is the genuine string representation of the corresponding pair of
configurations.  Since the map is letter-to-letter on windows, inverse images of regular languages
under it are regular (`Transducers.RegAut.isRegular_comapWin`), and this is what makes the atoms of
`RequestProject/PartD/CGAtom.lean` regular.
-/
import Lax194892Proofs.Source.PartC.RegWin
import Lax916827Proofs.Source.PartC.MarkStr
import Lax194892Proofs.Source.PartD.ChildGraphOfRun
import Lax194892Proofs.Source.PartD.PebStepMach
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CGL

open MarkStr RegAut

variable {A Q Q' : Type} {k : ℕ}

/-- A letter of the marked string representation of a configuration. -/
abbrev MLetter (A Q : Type) (k : ℕ) : Type := Mark2 (CG.ConfLetter A Q k)

/-- **A position of the input, named relative to the two marks.**  `nop` names no position at all,
`zero` the first gap, `mark` the position of the first mark, `markL` and `markR` its two
neighbours, and `extra` the position of the second mark. -/
inductive Spot
  | nop
  | zero
  | mark
  | markL
  | markR
  | extra
  deriving DecidableEq

/-- Whether the position of the window carries the spot, read off the window. -/
def spotBit : Spot → Win (MLetter A Q k) → Bool
  | Spot.nop, _ => false
  | Spot.zero, t => t.1.isNone
  | Spot.mark, t => t.2.1.2.1
  | Spot.markL, t => (t.2.2.map fun c => c.2.1).getD false
  | Spot.markR, t => (t.1.map fun c => c.2.1).getD false
  | Spot.extra, t => t.2.1.2.2

/-- The position that the spot names, for the marks `x` and `r`. -/
def spotPos : Spot → ℕ → ℕ → Option ℕ
  | Spot.nop, _, _ => none
  | Spot.zero, _, _ => some 0
  | Spot.mark, x, _ => some x
  | Spot.markL, x, _ => some (x - 1)
  | Spot.markR, x, _ => some (x + 1)
  | Spot.extra, _, r => some r

/-- The pebble that the spot adds on top of the stack. -/
def spotStack (sp : Spot) (x r : ℕ) : List ℕ := (spotPos sp x r).toList

/-- The side condition under which the spot names a genuine gap of an input of length `n`. -/
def SpotOk : Spot → ℕ → ℕ → Prop
  | Spot.markL, x, _ => 1 ≤ x
  | Spot.markR, x, n => x + 1 ≤ n
  | _, _, _ => True

lemma spotStack_le {sp : Spot} {x r n : ℕ} (hx : x ≤ n) (hr : r ≤ n) (h : SpotOk sp x n) :
    ∀ p ∈ spotStack sp x r, p ≤ n := by
  intro p hp
  cases sp <;>
    simp only [spotStack, spotPos, Option.toList_none, Option.toList_some,
      List.mem_singleton, List.not_mem_nil] at hp <;>
    subst hp <;> simp only [SpotOk] at h <;> omega

lemma spotStack_length_le (sp : Spot) (x r : ℕ) : (spotStack sp x r).length ≤ 1 := by
  cases sp <;> simp [spotStack, spotPos]

/-- **The pair letter produced from a window of the marked string representation of a
configuration**: the two states are fixed, the input letter is the one of the window, and the two
stacks are the stack of the configuration with the pebble `nid` added in the position named by the
spot. -/
def pairMap (nid : Fin k) (q₁ q₂ : Q') (sp₁ sp₂ : Spot) (t : Win (MLetter A Q k)) :
    PebEnc.PairLetter A Q' k :=
  (q₁, q₂, t.2.1.1.2.1,
    (fun i => t.2.1.1.2.2 i || (decide (i = nid) && spotBit sp₁ t)),
    (fun i => t.2.1.1.2.2 i || (decide (i = nid) && spotBit sp₂ t)))

/-! ## The marked string representation of a configuration -/

variable {q₀ : Q} {st : List ℕ} {w : List A}

@[simp] lemma confEnc_length (q₀ : Q) (st : List ℕ) (w : List A) :
    (CG.confEnc (k := k) q₀ st w).length = w.length + 1 := by
  simp [CG.confEnc]

lemma confEnc_getElem? {j : ℕ} (hj : j ≤ w.length) :
    (CG.confEnc (k := k) q₀ st w)[j]? = some (q₀, w[j]?, PebEnc.ann k st j) := by
  rw [CG.confEnc, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

lemma confEnc_getElem?_of_gt {j : ℕ} (hj : w.length < j) :
    (CG.confEnc (k := k) q₀ st w)[j]? = none := by
  rw [List.getElem?_eq_none]
  simp only [confEnc_length]
  omega

/-- The letters of the marked string representation of a configuration. -/
lemma mark_confEnc_getElem? (x r j : ℕ) :
    (markAt2 (CG.confEnc (k := k) q₀ st w) x r)[j]? =
      if j ≤ w.length then some ((q₀, w[j]?, PebEnc.ann k st j), decide (j = x), decide (j = r))
      else none := by
  rw [markAt2_getElem?]
  by_cases hj : j ≤ w.length
  · rw [if_pos hj, confEnc_getElem? hj]
    rfl
  · rw [if_neg hj, confEnc_getElem?_of_gt (by omega)]
    rfl

@[simp] lemma mark_confEnc_length (x r : ℕ) :
    (markAt2 (CG.confEnc (k := k) q₀ st w) x r).length = w.length + 1 := by
  simp

/-- The window of a position of the marked string representation of a configuration. -/
lemma winMap_mark_confEnc_getElem? {x r j : ℕ} (hj : j ≤ w.length) :
    (winMap (markAt2 (CG.confEnc (k := k) q₀ st w) x r))[j]? =
      some ((if j = 0 then none
              else some ((q₀, w[j - 1]?, PebEnc.ann k st (j - 1)),
                decide (j - 1 = x), decide (j - 1 = r))),
            ((q₀, w[j]?, PebEnc.ann k st j), decide (j = x), decide (j = r)),
            (if j + 1 ≤ w.length
              then some ((q₀, w[j + 1]?, PebEnc.ann k st (j + 1)),
                decide (j + 1 = x), decide (j + 1 = r))
              else none)) := by
  rw [winMap_getElem?]
  rw [show (markAt2 (CG.confEnc (k := k) q₀ st w) x r)[j]?
      = some ((q₀, w[j]?, PebEnc.ann k st j), decide (j = x), decide (j = r)) from by
    rw [mark_confEnc_getElem?, if_pos hj]]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
  refine ⟨?_, ?_⟩
  · by_cases h0 : j = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, mark_confEnc_getElem?, if_pos (show j - 1 ≤ w.length by omega)]
  · rw [mark_confEnc_getElem?]

/-- **The spot bit is the indicator of the position that the spot names.** -/
lemma spotBit_window {x r j : ℕ} (hj : j ≤ w.length) (hx : x ≤ w.length)
    {sp : Spot} (hok : SpotOk sp x w.length) :
    spotBit (A := A) (Q := Q) (k := k) sp
        ((if j = 0 then none
              else some ((q₀, w[j - 1]?, PebEnc.ann k st (j - 1)),
                decide (j - 1 = x), decide (j - 1 = r))),
            ((q₀, w[j]?, PebEnc.ann k st j), decide (j = x), decide (j = r)),
            (if j + 1 ≤ w.length
              then some ((q₀, w[j + 1]?, PebEnc.ann k st (j + 1)),
                decide (j + 1 = x), decide (j + 1 = r))
              else none))
      = decide (spotPos sp x r = some j) := by
  cases sp with
  | nop => simp [spotBit, spotPos]
  | zero =>
      simp only [spotBit, spotPos, Option.some.injEq]
      by_cases h0 : j = 0 <;> simp [h0, eq_comm]
  | mark =>
      simp only [spotBit, spotPos, Option.some.injEq, decide_eq_decide]
      omega
  | markL =>
      simp only [SpotOk] at hok
      simp only [spotBit, spotPos, Option.some.injEq]
      by_cases hc : j + 1 ≤ w.length
      · rw [if_pos hc]
        simp only [Option.map_some, Option.getD_some, decide_eq_decide]
        omega
      · rw [if_neg hc]
        simp only [Option.map_none, Option.getD_none]
        symm
        simp only [decide_eq_false_iff_not]
        omega
  | markR =>
      simp only [spotBit, spotPos, Option.some.injEq]
      by_cases h0 : j = 0
      · rw [if_pos h0]
        simp only [Option.map_none, Option.getD_none]
        symm
        simp only [decide_eq_false_iff_not]
        omega
      · rw [if_neg h0]
        simp only [Option.map_some, Option.getD_some, decide_eq_decide]
        omega
  | extra =>
      simp only [spotBit, spotPos, Option.some.injEq, decide_eq_decide]
      omega

/-- Adding the pebble named by the spot to the stack. -/
lemma ann_spotStack {nid : Fin k} (hnid : (nid : ℕ) = st.length) (sp : Spot) (x r j : ℕ) :
    PebEnc.ann k (st ++ spotStack sp x r) j
      = fun i => PebEnc.ann k st j i ||
          (decide (i = nid) && decide (spotPos sp x r = some j)) := by
  cases sp with
  | nop =>
      show PebEnc.ann k (st ++ []) j = _
      rw [List.append_nil]
      funext i
      simp [spotPos]
  | zero =>
      show PebEnc.ann k (st ++ [0]) j = _
      rw [CG.ann_append_singleton st 0 j nid hnid]
      funext i
      simp [spotPos, eq_comm]
  | mark =>
      show PebEnc.ann k (st ++ [x]) j = _
      rw [CG.ann_append_singleton st x j nid hnid]
      funext i
      simp [spotPos, eq_comm]
  | markL =>
      show PebEnc.ann k (st ++ [x - 1]) j = _
      rw [CG.ann_append_singleton st (x - 1) j nid hnid]
      funext i
      simp [spotPos, eq_comm]
  | markR =>
      show PebEnc.ann k (st ++ [x + 1]) j = _
      rw [CG.ann_append_singleton st (x + 1) j nid hnid]
      funext i
      simp [spotPos, eq_comm]
  | extra =>
      show PebEnc.ann k (st ++ [r]) j = _
      rw [CG.ann_append_singleton st r j nid hnid]
      funext i
      simp [spotPos, eq_comm]

/-- **The key lemma**: on the marked string representation of a configuration, the window map
`pairMap` produces exactly the string representation of the pair of configurations obtained by
adding the pebbles named by the two spots. -/
theorem pairMap_confEnc {nid : Fin k} (hnid : (nid : ℕ) = st.length) (q₁ q₂ : Q')
    {x r : ℕ} (hx : x ≤ w.length) {sp₁ sp₂ : Spot}
    (h₁ : SpotOk sp₁ x w.length) (h₂ : SpotOk sp₂ x w.length) :
    (winMap (markAt2 (CG.confEnc (k := k) q₀ st w) x r)).map (pairMap nid q₁ q₂ sp₁ sp₂)
      = PebEnc.pairEnc q₁ q₂ (st ++ spotStack sp₁ x r) (st ++ spotStack sp₂ x r) w := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map]
  by_cases hj : j ≤ w.length
  · rw [winMap_mark_confEnc_getElem? hj, PebEnc.pairEnc_getElem? _ _ _ _ _ hj]
    simp only [Option.map_some, Option.some.injEq]
    rw [pairMap]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_)))
    · show (fun i => PebEnc.ann k st j i || (decide (i = nid) && spotBit sp₁ _))
        = PebEnc.ann k (st ++ spotStack sp₁ x r) j
      rw [ann_spotStack hnid, spotBit_window hj hx h₁]
    · show (fun i => PebEnc.ann k st j i || (decide (i = nid) && spotBit sp₂ _))
        = PebEnc.ann k (st ++ spotStack sp₂ x r) j
      rw [ann_spotStack hnid, spotBit_window hj hx h₂]
  · rw [PebEnc.pairEnc_getElem?_of_gt _ _ _ _ _ (by omega)]
    rw [List.getElem?_eq_none, Option.map_none]
    rw [winMap_length]
    simp only [mark_confEnc_length]
    omega

end CGL

end Lax194892Proofs.Transducers
