/- The composed two-way transducer (the main construction for Theorem
`thm:composition-of-two-way-transducers` of *Transducers*, M. Bojańczyk).

Let `M` be a two-way transducer whose transitions all produce an output of the
same length `m+1`, ending with a fixed letter `b₀`, and let `N` be a second
two-way transducer.  The transducer built here reads the *annotated* input of
`TwoWayAnnot.lean` and simulates `N` on the output of `M`.

The head of `N` is represented by a pair: a configuration of `M` on the run
(represented by the position of the head of the composed transducer, together
with the state of `M`, which is kept in the state of the composed transducer)
and an offset inside the output produced by the transition taken at that
configuration.  Moving the head of `N` to the right means following the run of
`M` forwards, which is deterministic; moving it to the left means following the
run of `M` backwards, which is possible because the annotation tells the
composed transducer which configurations lie on the run, and a configuration on
the run has a unique predecessor on the run (`TwoWay.pred_unique`).

Since the output of every transition of `M` ends with the fixed letter `b₀`, the
letter to the left of the head of `N` is `b₀` whenever the offset is `0` and the
configuration is not the initial one, so it never has to be looked up backwards.

A step of `N` that does not change the configuration of `M` is implemented by a
*bouncing* step: the head moves away and comes back.  Finally, an input that is
not a correct annotation is detected by a left-to-right scan (all the
consistency conditions are local), and answered with the empty output; this is
what makes the composed transducer total.
-/
import Lax916827Proofs.Source.PartC.TwoWayCompPred
import Lax916827Proofs.Source.PartC.TwoWayRat
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

open scoped Classical

variable {A B' C Q P S : Type}

/-- The position of the head of `N`: either a state of `N`, a state of `M` (the
configuration of `M` at the head of the composed transducer) and an offset in
the output of the corresponding transition, or the end of the output. -/
abbrev CompCore (P Q : Type) (k : ℕ) := (P × Q × Fin k) ⊕ (P × Q)

/-- The head of `N` is at the offset `j` of the output of the transition taken
at the current configuration of `M`. -/
def coreMain (p : P) (q : Q) {k : ℕ} (j : Fin k) : CompCore P Q k := Sum.inl (p, q, j)

/-- The head of `N` is at the end of the output. -/
def coreEnd (p : P) (q : Q) {k : ℕ} : CompCore P Q k := Sum.inr (p, q)

/-- The state of the composed transducer: a scanning state (`Sum.inr false` for
the left-to-right check of the annotation, `Sum.inr true` for the return to the
left end), a simulating state (`Sum.inl (c, none)`) or a bouncing state
(`Sum.inl (c, some d)`, which moves in the direction `d` and then simulates). -/
abbrev CompSt (P Q : Type) (k : ℕ) := (CompCore P Q k × Option Bool) ⊕ Bool

/-- The simulating state. -/
def stRun {k : ℕ} (c : CompCore P Q k) : CompSt P Q k := Sum.inl (c, none)
/-- The bouncing state. -/
def stBounce {k : ℕ} (c : CompCore P Q k) (d : Bool) : CompSt P Q k := Sum.inl (c, some d)
/-- The state of the left-to-right scan checking the annotation. -/
def stScanR (P Q : Type) (k : ℕ) : CompSt P Q k := Sum.inr false
/-- The state of the return to the left end of the input. -/
def stScanL (P Q : Type) (k : ℕ) : CompSt P Q k := Sum.inr true

/-- A transition that produces the output `o` and leaves the head where it is:
it moves one step away from the head and comes back. -/
def stay {k : ℕ} (c : CompCore P Q k) (o : List C) (r : Option (AnnLet A S)) :
    List C ⊕ (CompSt P Q k × List C × Bool) :=
  Sum.inr (stBounce c (!r.isSome), o, r.isSome)

/-- The output produced by the transition of `M` taken at the current cut, read
off the two adjacent annotation letters. -/
noncomputable def stepWord (M : TwoWay A B' Q) (l r : Option (AnnLet A S)) (q : Q) : List B' :=
  outWord (M.step (l.map AnnLet.letter) q (r.map AnnLet.letter))

/-- The letter of the output of `M` that lies to the left of the head of `N`.
At the offset `0` it is the last letter `b₀` of the previous transition, unless
the current configuration of `M` is the initial one. -/
noncomputable def leftLet (M : TwoWay A B' Q) (b₀ : B') (l r : Option (AnnLet A S)) (q : Q)
    (j : ℕ) : Option B' :=
  if j = 0 then (if l.isNone ∧ q = M.init then none else some b₀) else (stepWord M l r q)[j - 1]?

/-- The letter of the output of `M` that lies to the right of the head of `N`. -/
noncomputable def rightLet (M : TwoWay A B' Q) (l r : Option (AnnLet A S)) (q : Q) (j : ℕ) :
    Option B' := (stepWord M l r q)[j]?

/-- The transition of the composed transducer in a simulating state. -/
noncomputable def compRun (D : DFA (Marked A Q) S) (M : TwoWay A B' Q) (N : TwoWay B' C P)
    {m : ℕ} (b₀ : B') (l r : Option (AnnLet A S)) (c : CompCore P Q (m + 1)) :
    List C ⊕ (CompSt P Q (m + 1) × List C × Bool) :=
  match c with
  | Sum.inr (p, q) =>
      match N.step (some b₀) p none with
      | Sum.inl o => Sum.inl o
      | Sum.inr (p', o, false) => stay (coreMain p' q (Fin.last m)) o r
      | Sum.inr (_, _, true) => Sum.inl []
  | Sum.inl (p, q, j) =>
      match N.step (leftLet M b₀ l r q (j : ℕ)) p (rightLet M l r q (j : ℕ)) with
      | Sum.inl o => Sum.inl o
      | Sum.inr (p', o, true) =>
          if h : (j : ℕ) + 1 < m + 1 then stay (coreMain p' q ⟨(j : ℕ) + 1, h⟩) o r
          else
            match M.step (l.map AnnLet.letter) q (r.map AnnLet.letter) with
            | Sum.inl _ => stay (coreEnd p' q) o r
            | Sum.inr (q', _, d) => Sum.inr (stRun (coreMain p' q' 0), o, d)
      | Sum.inr (p', o, false) =>
          if (j : ℕ) = 0 then
            match predOf D M l r q with
            | none => Sum.inl []
            | some (q', d) => Sum.inr (stRun (coreMain p' q' (Fin.last m)), o, d)
          else
            stay (coreMain p' q ⟨(j : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩) o r

/-- The transition function of the composed transducer. -/
noncomputable def compStep (D : DFA (Marked A Q) S) (M : TwoWay A B' Q) (N : TwoWay B' C P)
    {m : ℕ} (b₀ : B') (outNil : List C)
    (l : Option (AnnLet A S)) (st : CompSt P Q (m + 1)) (r : Option (AnnLet A S)) :
    List C ⊕ (CompSt P Q (m + 1) × List C × Bool) :=
  if l.isNone ∧ r.isNone then Sum.inl outNil
  else
    match st with
    | Sum.inr false =>
        if LocalOK D l r then
          (if r.isNone then Sum.inr (stScanL P Q (m + 1), [], false)
            else Sum.inr (stScanR P Q (m + 1), [], true))
        else Sum.inl []
    | Sum.inr true =>
        if l.isNone then Sum.inr (stBounce (coreMain N.init M.init (0 : Fin (m + 1))) false, [], true)
        else Sum.inr (stScanL P Q (m + 1), [], false)
    | Sum.inl (c, some d) => Sum.inr (stRun c, [], d)
    | Sum.inl (c, none) => compRun D M N b₀ l r c

/-- The composed transducer: it reads the annotated input and simulates `N` on
the output of `M`. -/
noncomputable def compAut (D : DFA (Marked A Q) S) (M : TwoWay A B' Q) (N : TwoWay B' C P)
    (m : ℕ) (b₀ : B') (outNil : List C) : TwoWay (AnnLet A S) C (CompSt P Q (m + 1)) where
  init := stScanR P Q (m + 1)
  step := compStep D M N b₀ outNil

/-- The function computed by the composed transducer: on a correct annotation it
is the composition, on any other input it is the empty string. -/
noncomputable def compFun (D : DFA (Marked A Q) S) (f : List A → List B') (g : List B' → List C)
    (z : List (AnnLet A S)) : List C :=
  if Valid D z then g (f (z.map AnnLet.letter)) else []

/-! ### The configurations of the composed transducer -/

/-- The configuration of the composed transducer with the head at the cut `i`. -/
def cutCfg {k : ℕ} (z : List (AnnLet A S)) (i : ℕ) (st : CompSt P Q k) :
    Cfg (AnnLet A S) (CompSt P Q k) := Cfg.conf (z.take i) st (z.drop i)

lemma take_getLast? (z : List (AnnLet A S)) {i : ℕ} (hi : i ≤ z.length) :
    (z.take i).getLast? = prevLet z i := by
  rw [take_getLast?' z hi, prevLet]

lemma drop_head? (z : List (AnnLet A S)) (i : ℕ) : (z.drop i).head? = z[i]? := List.head?_drop

/-- At a cut of a nonempty string, at least one of the two adjacent letters
exists. -/
lemma not_both_none {z : List (AnnLet A S)} (hz : z ≠ []) {i : ℕ} (hi : i ≤ z.length) :
    ¬ ((prevLet z i).isNone = true ∧ (z[i]?).isNone = true) := by
  rintro ⟨h1, h2⟩
  have hlen : 0 < z.length := List.length_pos_iff.mpr hz
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [List.getElem?_eq_getElem hlen] at h2; simp at h2
  · rw [prevLet_pos (by omega), List.getElem?_eq_getElem (by omega : i - 1 < z.length)] at h1
    simp at h1

section Machine

variable (D : DFA (Marked A Q) S) (M : TwoWay A B' Q) (N : TwoWay B' C P) {m : ℕ} (b₀ : B')
  (outNil : List C)

/-! ### The basic steps of the composed transducer -/

lemma compStep_run {l r : Option (AnnLet A S)} {c : CompCore P Q (m + 1)}
    (hg : ¬ (l.isNone = true ∧ r.isNone = true)) :
    compStep D M N b₀ outNil l (stRun c) r = compRun D M N b₀ l r c := by
  simp only [stRun]
  rw [compStep, if_neg hg]

lemma compStep_bounce {l r : Option (AnnLet A S)} {c : CompCore P Q (m + 1)} {d : Bool}
    (hg : ¬ (l.isNone = true ∧ r.isNone = true)) :
    compStep D M N b₀ outNil l (stBounce c d) r = Sum.inr (stRun c, [], d) := by
  simp only [stBounce]
  rw [compStep, if_neg hg]

lemma compStep_scanR_ok {l r : Option (AnnLet A S)}
    (hg : ¬ (l.isNone = true ∧ r.isNone = true)) (hok : LocalOK D l r) (hr : r.isNone = false) :
    compStep D M N b₀ outNil l (stScanR P Q (m + 1)) r
      = Sum.inr (stScanR P Q (m + 1), [], true) := by
  simp only [stScanR]
  rw [compStep, if_neg hg]
  simp [stScanR, hok, hr]

lemma compStep_scanR_end {l r : Option (AnnLet A S)}
    (hg : ¬ (l.isNone = true ∧ r.isNone = true)) (hok : LocalOK D l r) (hr : r.isNone = true) :
    compStep D M N b₀ outNil l (stScanR P Q (m + 1)) r
      = Sum.inr (stScanL P Q (m + 1), [], false) := by
  simp only [stScanR, stScanL]
  rw [compStep, if_neg hg]
  simp [stScanL, hok, hr]

lemma compStep_scanR_bad {l r : Option (AnnLet A S)}
    (hg : ¬ (l.isNone = true ∧ r.isNone = true)) (hok : ¬ LocalOK D l r) :
    compStep D M N b₀ outNil l (stScanR P Q (m + 1)) r = Sum.inl [] := by
  simp only [stScanR]
  rw [compStep, if_neg hg]
  simp [hok]

lemma compStep_scanL_left {l r : Option (AnnLet A S)}
    (hg : ¬ (l.isNone = true ∧ r.isNone = true)) (hl : l.isNone = false) :
    compStep D M N b₀ outNil l (stScanL P Q (m + 1)) r
      = Sum.inr (stScanL P Q (m + 1), [], false) := by
  simp only [stScanL]
  rw [compStep, if_neg hg]
  simp [stScanL, hl]

lemma compStep_scanL_start {l r : Option (AnnLet A S)}
    (hg : ¬ (l.isNone = true ∧ r.isNone = true)) (hl : l.isNone = true) :
    compStep D M N b₀ outNil l (stScanL P Q (m + 1)) r
      = Sum.inr (stBounce (coreMain N.init M.init (0 : Fin (m + 1))) false, [], true) := by
  simp only [stScanL]
  rw [compStep, if_neg hg]
  simp [hl]

/-! ### Unfolding the simulating transition -/

lemma compRun_main_halt {l r : Option (AnnLet A S)} {p : P} {q : Q} {j : Fin (m + 1)} {o : List C}
    (h : N.step (leftLet M b₀ l r q (j : ℕ)) p (rightLet M l r q (j : ℕ)) = Sum.inl o) :
    compRun D M N b₀ l r (coreMain p q j) = Sum.inl o := by
  simp only [coreMain, compRun, h]

lemma compRun_main_right_mid {l r : Option (AnnLet A S)} {p p' : P} {q : Q} {j : Fin (m + 1)}
    {o : List C}
    (h : N.step (leftLet M b₀ l r q (j : ℕ)) p (rightLet M l r q (j : ℕ))
      = Sum.inr (p', o, true))
    (hj : (j : ℕ) + 1 < m + 1) :
    compRun D M N b₀ l r (coreMain p q j) = stay (coreMain p' q ⟨(j : ℕ) + 1, hj⟩) o r := by
  simp only [coreMain, compRun, h, dif_pos hj]

lemma compRun_main_right_end_halt {l r : Option (AnnLet A S)} {p p' : P} {q : Q} {j : Fin (m + 1)}
    {o : List C} {oM : List B'}
    (h : N.step (leftLet M b₀ l r q (j : ℕ)) p (rightLet M l r q (j : ℕ))
      = Sum.inr (p', o, true))
    (hj : ¬ ((j : ℕ) + 1 < m + 1))
    (hM : M.step (l.map AnnLet.letter) q (r.map AnnLet.letter) = Sum.inl oM) :
    compRun D M N b₀ l r (coreMain p q j) = stay (coreEnd p' q) o r := by
  simp only [coreMain, compRun, h, dif_neg hj, hM]

lemma compRun_main_right_end_move {l r : Option (AnnLet A S)} {p p' : P} {q q' : Q}
    {j : Fin (m + 1)} {o : List C} {oM : List B'} {d : Bool}
    (h : N.step (leftLet M b₀ l r q (j : ℕ)) p (rightLet M l r q (j : ℕ))
      = Sum.inr (p', o, true))
    (hj : ¬ ((j : ℕ) + 1 < m + 1))
    (hM : M.step (l.map AnnLet.letter) q (r.map AnnLet.letter) = Sum.inr (q', oM, d)) :
    compRun D M N b₀ l r (coreMain p q j) = Sum.inr (stRun (coreMain p' q' 0), o, d) := by
  simp only [coreMain, compRun, h, dif_neg hj, hM]

lemma compRun_main_left_pos {l r : Option (AnnLet A S)} {p p' : P} {q : Q} {j : Fin (m + 1)}
    {o : List C}
    (h : N.step (leftLet M b₀ l r q (j : ℕ)) p (rightLet M l r q (j : ℕ))
      = Sum.inr (p', o, false))
    (hj : (j : ℕ) ≠ 0) (hlt : (j : ℕ) - 1 < m + 1) :
    compRun D M N b₀ l r (coreMain p q j) = stay (coreMain p' q ⟨(j : ℕ) - 1, hlt⟩) o r := by
  simp only [coreMain, compRun, h, if_neg hj]

lemma compRun_main_left_zero {l r : Option (AnnLet A S)} {p p' : P} {q q₁ : Q} {j : Fin (m + 1)}
    {o : List C} {d : Bool}
    (h : N.step (leftLet M b₀ l r q (j : ℕ)) p (rightLet M l r q (j : ℕ))
      = Sum.inr (p', o, false))
    (hj : (j : ℕ) = 0) (hpred : predOf D M l r q = some (q₁, d)) :
    compRun D M N b₀ l r (coreMain p q j)
      = Sum.inr (stRun (coreMain p' q₁ (Fin.last m)), o, d) := by
  simp only [coreMain, compRun, h, if_pos hj, hpred]

lemma compRun_end_halt {l r : Option (AnnLet A S)} {p : P} {q : Q} {o : List C}
    (h : N.step (some b₀) p none = Sum.inl o) :
    compRun D M N b₀ l r ((coreEnd p q : CompCore P Q (m + 1))) = Sum.inl o := by
  simp only [coreEnd, compRun, h]

lemma compRun_end_left {l r : Option (AnnLet A S)} {p p' : P} {q : Q} {o : List C}
    (h : N.step (some b₀) p none = Sum.inr (p', o, false)) :
    compRun D M N b₀ l r ((coreEnd p q : CompCore P Q (m + 1)))
      = stay (coreMain p' q (Fin.last m)) o r := by
  simp only [coreEnd, compRun, h]

lemma compRun_end_right {l r : Option (AnnLet A S)} {p p' : P} {q : Q} {o : List C}
    (h : N.step (some b₀) p none = Sum.inr (p', o, true)) :
    compRun D M N b₀ l r ((coreEnd p q : CompCore P Q (m + 1))) = Sum.inl [] := by
  simp only [coreEnd, compRun, h]

/-! ### Steps at a cut -/

lemma cutCfg_halt {z : List (AnnLet A S)} {i : ℕ} (hi : i ≤ z.length)
    {st : CompSt P Q (m + 1)} {o : List C}
    (h : compStep D M N b₀ outNil (prevLet z i) st z[i]? = Sum.inl o) :
    (compAut D M N m b₀ outNil).stepCfg (cutCfg z i st) = some (o, Cfg.halt) := by
  simp only [cutCfg]
  apply stepCfg_halt_eq
  rw [take_getLast? z hi, drop_head?]
  exact h

lemma cutCfg_right {z : List (AnnLet A S)} {i : ℕ} (hi : i < z.length)
    {st st' : CompSt P Q (m + 1)} {o : List C}
    (h : compStep D M N b₀ outNil (prevLet z i) st z[i]? = Sum.inr (st', o, true)) :
    (compAut D M N m b₀ outNil).stepCfg (cutCfg z i st) = some (o, cutCfg z (i + 1) st') := by
  have hd : z.drop i = (z[i]'hi) :: z.drop (i + 1) := List.drop_eq_getElem_cons hi
  have h' : (compAut D M N m b₀ outNil).step (z.take i).getLast? st
      (((z[i]'hi) :: z.drop (i + 1)).head?) = Sum.inr (st', o, true) := by
    rw [take_getLast? z (le_of_lt hi), ← hd, drop_head?]
    exact h
  simp only [cutCfg, hd]
  rw [stepCfg_right_cons (compAut D M N m b₀ outNil) h',
    List.take_succ_eq_append_getElem hi]

lemma cutCfg_left {z : List (AnnLet A S)} {i : ℕ} (hpos : 0 < i) (hi : i ≤ z.length)
    {st st' : CompSt P Q (m + 1)} {o : List C}
    (h : compStep D M N b₀ outNil (prevLet z i) st z[i]? = Sum.inr (st', o, false)) :
    (compAut D M N m b₀ outNil).stepCfg (cutCfg z i st) = some (o, cutCfg z (i - 1) st') := by
  have hi1 : i - 1 < z.length := by omega
  have hlast : (z.take i).getLast? = some (z[i - 1]'hi1) := by
    rw [take_getLast? z hi, prevLet_pos (by omega), List.getElem?_eq_getElem hi1]
  have h' : (compAut D M N m b₀ outNil).step (z.take i).getLast? st (z.drop i).head?
      = Sum.inr (st', o, false) := by
    rw [take_getLast? z hi, drop_head?]
    exact h
  have hdl : (z.take i).dropLast = z.take (i - 1) := by
    rw [List.dropLast_eq_take, List.length_take, min_eq_left hi, List.take_take]
    congr 1
    omega
  have hdr : (z[i - 1]'hi1) :: z.drop i = z.drop (i - 1) := by
    rw [List.drop_eq_getElem_cons hi1, show i - 1 + 1 = i from by omega]
  simp only [cutCfg]
  rw [stepCfg_left_some (compAut D M N m b₀ outNil) hlast h', hdl, hdr]

/-- A step that produces its output and leaves the head where it is. -/
lemma stay_reaches {z : List (AnnLet A S)} {i : ℕ} (hi : i ≤ z.length) (hz : z ≠ [])
    {st : CompSt P Q (m + 1)} {c : CompCore P Q (m + 1)} {o : List C}
    (h : compStep D M N b₀ outNil (prevLet z i) st z[i]? = stay c o z[i]?) :
    (compAut D M N m b₀ outNil).Reaches (cutCfg z i st) o (cutCfg z i (stRun c)) := by
  have hlen : 0 < z.length := List.length_pos_iff.mpr hz
  by_cases hr : i < z.length
  · have hsome : (z[i]?).isSome = true := by
      rw [List.getElem?_eq_getElem hr]; rfl
    rw [stay, hsome] at h
    simp only [Bool.not_true] at h
    have h1 := cutCfg_right D M N b₀ outNil hr h
    have hb : compStep D M N b₀ outNil (prevLet z (i + 1)) (stBounce c false) z[i + 1]?
        = Sum.inr (stRun c, [], false) :=
      compStep_bounce D M N b₀ outNil (not_both_none hz (by omega : i + 1 ≤ z.length))
    have h2 := cutCfg_left D M N b₀ outNil (show 0 < i + 1 by omega) (by omega) hb
    simp only [Nat.add_sub_cancel] at h2
    simpa using (reaches_one h1).trans (reaches_one h2)
  · have hieq : i = z.length := by omega
    have hnone : z[i]? = none := List.getElem?_eq_none (by omega)
    have hstay : stay (C := C) c o z[i]? = Sum.inr (stBounce c true, o, false) := by
      rw [hnone]; rfl
    rw [hstay] at h
    have h1 := cutCfg_left D M N b₀ outNil (show 0 < i by omega) hi h
    have hb : compStep D M N b₀ outNil (prevLet z (i - 1)) (stBounce c true) z[i - 1]?
        = Sum.inr (stRun c, [], true) :=
      compStep_bounce D M N b₀ outNil (not_both_none hz (by omega : i - 1 ≤ z.length))
    have h2 := cutCfg_right D M N b₀ outNil (show i - 1 < z.length by omega) hb
    rw [show i - 1 + 1 = i from by omega] at h2
    simpa using (reaches_one h1).trans (reaches_one h2)

/-! ### The scanning phases -/

/-- The left-to-right scan moves from the cut `i` to the cut `j`. -/
lemma scanR_to {z : List (AnnLet A S)} (hz : z ≠ []) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ z.length)
    (hok : ∀ i', i ≤ i' → i' < j → LocalOK D (prevLet z i') z[i']?) :
    (compAut D M N m b₀ outNil).Reaches (cutCfg z i (stScanR P Q (m + 1))) []
      (cutCfg z j (stScanR P Q (m + 1))) := by
  revert hj hok
  induction j, hij using Nat.le_induction with
  | base => intro _ _; exact Reaches.refl _
  | succ j hij ih =>
      intro hj hok
      have hjl : j < z.length := by omega
      have h1 := ih (by omega) (fun i' h1 _ => hok i' h1 (by omega))
      have hb : compStep D M N b₀ outNil (prevLet z j) (stScanR P Q (m + 1)) z[j]?
          = Sum.inr (stScanR P Q (m + 1), [], true) :=
        compStep_scanR_ok D M N b₀ outNil (not_both_none hz (by omega))
          (hok j hij (by omega)) (by rw [List.getElem?_eq_getElem hjl]; rfl)
      have hstep := cutCfg_right D M N b₀ outNil hjl hb
      simpa using h1.trans (reaches_one hstep)

/-- The left-to-right scan reaches the right end of the input if all the local
conditions hold. -/
lemma scanR_reaches {z : List (AnnLet A S)} (hz : z ≠ []) (i : ℕ) (hi : i ≤ z.length)
    (hok : ∀ i', i ≤ i' → i' ≤ z.length → LocalOK D (prevLet z i') z[i']?) :
    (compAut D M N m b₀ outNil).Reaches (cutCfg z i (stScanR P Q (m + 1))) []
      (cutCfg z (z.length - 1) (stScanL P Q (m + 1))) := by
  have hlen : 0 < z.length := List.length_pos_iff.mpr hz
  have h1 := scanR_to D M N b₀ outNil (m := m) hz hi (le_refl z.length)
    (fun i' a hlt => hok i' a (le_of_lt hlt))
  have hnone : z[z.length]? = none := List.getElem?_eq_none (le_refl _)
  have hb : compStep D M N b₀ outNil (prevLet z z.length) (stScanR P Q (m + 1)) z[z.length]?
      = Sum.inr (stScanL P Q (m + 1), [], false) :=
    compStep_scanR_end D M N b₀ outNil (not_both_none hz (le_refl _))
      (hok _ hi (le_refl _)) (by rw [hnone]; rfl)
  have hstep := cutCfg_left D M N b₀ outNil hlen (le_refl z.length) hb
  simpa using h1.trans (reaches_one hstep)

/-- The return to the left end of the input. -/
lemma scanL_reaches {z : List (AnnLet A S)} (hz : z ≠ []) (i : ℕ) (hi : i ≤ z.length) :
    (compAut D M N m b₀ outNil).Reaches (cutCfg z i (stScanL P Q (m + 1))) []
      (cutCfg z 0 (stScanL P Q (m + 1))) := by
  revert hi
  induction i with
  | zero => intro _; exact Reaches.refl _
  | succ k ih =>
      intro hi
      have hk : k < z.length := by omega
      have hl : (prevLet z (k + 1)).isNone = false := by
        rw [prevLet_pos (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [List.getElem?_eq_getElem hk]
        rfl
      have hb : compStep D M N b₀ outNil (prevLet z (k + 1)) (stScanL P Q (m + 1)) z[k + 1]?
          = Sum.inr (stScanL P Q (m + 1), [], false) :=
        compStep_scanL_left D M N b₀ outNil (not_both_none hz hi) hl
      have hstep := cutCfg_left D M N b₀ outNil (show 0 < k + 1 by omega) hi hb
      simp only [Nat.add_sub_cancel] at hstep
      simpa using (reaches_one hstep).trans (ih (by omega))

/-- If the annotation is correct, the transducer reaches the configuration in
which the simulation of `N` starts. -/
lemma pre_reaches {z : List (AnnLet A S)} (hz : z ≠ []) (hv : Valid D z) :
    (compAut D M N m b₀ outNil).Reaches (Cfg.conf [] (compAut D M N m b₀ outNil).init z) []
      (cutCfg z 0 (stRun (coreMain N.init M.init (0 : Fin (m + 1))))) := by
  have hlen : 0 < z.length := List.length_pos_iff.mpr hz
  have h0 : Cfg.conf [] (compAut D M N m b₀ outNil).init z
      = cutCfg z 0 (stScanR P Q (m + 1)) := rfl
  have h1 := scanR_reaches D M N b₀ outNil (m := m) hz 0 (by omega) (fun i' _ h2 => hv i' h2)
  have h2 := scanL_reaches D M N b₀ outNil (m := m) hz (z.length - 1) (by omega)
  have hl0 : (prevLet z 0).isNone = true := rfl
  have hb1 : compStep D M N b₀ outNil (prevLet z 0) (stScanL P Q (m + 1)) z[0]?
      = Sum.inr (stBounce (coreMain N.init M.init (0 : Fin (m + 1))) false, [], true) :=
    compStep_scanL_start D M N b₀ outNil (not_both_none hz (by omega)) hl0
  have hstep1 := cutCfg_right D M N b₀ outNil hlen hb1
  have hb2 : compStep D M N b₀ outNil (prevLet z (0 + 1))
      (stBounce (coreMain N.init M.init (0 : Fin (m + 1))) false) z[0 + 1]?
      = Sum.inr (stRun (coreMain N.init M.init (0 : Fin (m + 1))), [], false) :=
    compStep_bounce D M N b₀ outNil (not_both_none hz (by omega : 0 + 1 ≤ z.length))
  have hstep2 := cutCfg_left D M N b₀ outNil (show (0:ℕ) < 0 + 1 by omega)
    (by omega : 0 + 1 ≤ z.length) hb2
  simp only [Nat.add_sub_cancel] at hstep2
  rw [h0]
  simpa using h1.trans (h2.trans ((reaches_one hstep1).trans (reaches_one hstep2)))

/-- If the annotation is incorrect, the transducer halts with the empty
output. -/
lemma scanR_halts {z : List (AnnLet A S)} (hz : z ≠ []) (hv : ¬ Valid D z) :
    (compAut D M N m b₀ outNil).Computes z [] := by
  classical
  have hex : ∃ i, i ≤ z.length ∧ ¬ LocalOK D (prevLet z i) z[i]? := by
    by_contra hc
    push_neg at hc
    exact hv (fun i hi => hc i hi)
  obtain ⟨hi0, hbad⟩ := Nat.find_spec hex
  have hok : ∀ i', 0 ≤ i' → i' < Nat.find hex → LocalOK D (prevLet z i') z[i']? := by
    intro i' _ hlt
    have hmin := Nat.find_min hex hlt
    push_neg at hmin
    exact hmin (by omega)
  have h1 := scanR_to D M N b₀ outNil (m := m) hz (Nat.zero_le (Nat.find hex)) hi0 hok
  have hb : compStep D M N b₀ outNil (prevLet z (Nat.find hex)) (stScanR P Q (m + 1))
      z[Nat.find hex]? = Sum.inl [] :=
    compStep_scanR_bad D M N b₀ outNil (not_both_none hz hi0) hbad
  have hstep := cutCfg_halt D M N b₀ outNil hi0 hb
  have h0 : Cfg.conf [] (compAut D M N m b₀ outNil).init z
      = cutCfg z 0 (stScanR P Q (m + 1)) := rfl
  show (compAut D M N m b₀ outNil).Reaches _ [] Cfg.halt
  rw [h0]
  simpa using h1.trans (reaches_one hstep)
/-! ### The simulation -/

variable (f : List A → List B') (g : List B' → List C)

/-- The relation between the configurations of the composed transducer on the
annotated input and the configurations of `N` on the output of `M`. -/
def compRel (w : List A) (z : List (AnnLet A S)) (T : ℕ) :
    Cfg (AnnLet A S) (CompSt P Q (m + 1)) → Cfg B' P → Prop := fun X c =>
  (X = Cfg.halt ∧ c = Cfg.halt) ∨
  (∃ (t : ℕ) (u v : List A) (q : Q) (p : P) (j : Fin (m + 1)),
      t < T ∧ cfgAt M w t = some (Cfg.conf u q v) ∧
      X = cutCfg z u.length (stRun (coreMain p q j)) ∧
      c = Cfg.conf (outRange M w 0 t ++ (outAt M w t).take (j : ℕ)) p
            ((outAt M w t).drop (j : ℕ) ++ outRange M w (t + 1) T)) ∨
  (∃ (u v : List A) (q : Q) (p : P),
      cfgAt M w (T - 1) = some (Cfg.conf u q v) ∧
      X = cutCfg z u.length (stRun (coreEnd p q)) ∧
      c = Cfg.conf (outRange M w 0 T) p [])

/-- One step of the simulation, when the head of `N` is inside the output of
the transition taken at the time `t` of the run of `M`. -/
lemma compRel_step_main (hD : D.accepts = {z | (visitAut M).Accepts z})
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀)
    {w : List A} (hw : w ≠ []) {T : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    {t : ℕ} {u v : List A} {q : Q} {p : P} {j : Fin (m + 1)}
    (htT : t < T) (hcfg : cfgAt M w t = some (Cfg.conf u q v))
    {o : List C} {c' : Cfg B' P}
    (hs : N.stepCfg (Cfg.conf (outRange M w 0 t ++ (outAt M w t).take (j : ℕ)) p
      ((outAt M w t).drop (j : ℕ) ++ outRange M w (t + 1) T)) = some (o, c')) :
    ∃ Y, (compAut D M N m b₀ outNil).Reaches
        (cutCfg (annot D w) u.length (stRun (coreMain p q j))) o Y ∧
      compRel M w (annot D w) T Y c' := by
  classical
  have huv : u ++ v = w := cfgAt_append M w t hcfg
  have hiw : u.length ≤ w.length := by rw [← huv]; simp
  have hiz : u.length ≤ (annot D w).length := by rw [annot_length]; exact hiw
  have hu : w.take u.length = u := by rw [← huv]; simp
  have hv : w.drop u.length = v := by rw [← huv]; simp
  have hznil : annot D w ≠ [] := by
    intro h
    apply hw
    have h1 : (annot D w).length = 0 := by rw [h]; rfl
    rw [annot_length] at h1
    simpa using h1
  have hguard : ¬ ((prevLet (annot D w) u.length).isNone = true ∧
      ((annot D w)[u.length]?).isNone = true) := not_both_none hznil hiz
  have hnext : cfgAt M w (t + 1) ≠ none := by
    intro hnone
    have h1 := cfgAt_none_mono M w (show t + 1 ≤ T by omega) hnone
    rw [hT] at h1
    exact absurd h1 (by simp)
  obtain ⟨O, c₁, hstepM⟩ := exists_step_of_succ M w hcfg hnext
  have hOout : outAt M w t = O := outAt_of_step M w hcfg hstepM
  have hOw : O = outWord (M.step u.getLast? q v.head?) := stepCfg_outWord hstepM
  have hOlen : O.length = m + 1 := by rw [hOw]; exact houtlen _ _ _
  have hOlast : O.getLast? = some b₀ := by rw [hOw]; exact houtlast _ _ _
  obtain ⟨hll, hlr⟩ := annot_letters_at D huv
  have hMlet : M.step ((prevLet (annot D w) u.length).map AnnLet.letter) q
      (((annot D w)[u.length]?).map AnnLet.letter) = M.step u.getLast? q v.head? := by
    rw [hll, hlr]
  have hSW : stepWord M (prevLet (annot D w) u.length) ((annot D w)[u.length]?) q = O := by
    rw [stepWord, hMlet, ← hOw]
  have hjlt : (j : ℕ) < O.length := by rw [hOlen]; exact j.isLt
  have hjle : (j : ℕ) ≤ O.length := le_of_lt hjlt
  have hdropj : O.drop (j : ℕ) = (O[(j : ℕ)]'hjlt) :: O.drop ((j : ℕ) + 1) :=
    List.drop_eq_getElem_cons hjlt
  have hRhead : (O.drop (j : ℕ) ++ outRange M w (t + 1) T).head?
      = rightLet M (prevLet (annot D w) u.length) ((annot D w)[u.length]?) q (j : ℕ) := by
    rw [rightLet, hSW, hdropj, List.cons_append, List.head?_cons,
      List.getElem?_eq_getElem hjlt]
  have hLeft : (outRange M w 0 t ++ O.take (j : ℕ)).getLast?
      = leftLet M b₀ (prevLet (annot D w) u.length) ((annot D w)[u.length]?) q (j : ℕ) := by
    by_cases hj0 : (j : ℕ) = 0
    · rw [leftLet, if_pos hj0, hj0, List.take_zero, List.append_nil]
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · have h0 : Cfg.conf ([] : List A) M.init w = Cfg.conf u q v :=
          Option.some_injective _ (by rw [← cfgAt_zero M w]; exact hcfg)
        rw [Cfg.conf.injEq] at h0
        obtain ⟨hu0, hq0, -⟩ := h0
        have hcond : (prevLet (annot D w) u.length).isNone = true ∧ q = M.init := by
          refine ⟨?_, hq0.symm⟩
          rw [← hu0]
          rfl
        rw [outRange_self, if_pos hcond]
        rfl
      · have hcond : ¬ ((prevLet (annot D w) u.length).isNone = true ∧ q = M.init) := by
          rintro ⟨hnone, hqinit⟩
          have hi0 : u.length = 0 := (prevLet_annot_isNone D w hiw).mp hnone
          have hu0 : u = [] := by simpa using hi0
          have hvw : v = w := by rw [← huv, hu0]; simp
          have h2 : cfgAt M w 0 = some (Cfg.conf u q v) := by
            rw [cfgAt_zero, hu0, hqinit, hvw]
          have h3 := run_inj M w hT h2 hcfg
          omega
        rw [outRange_getLast? M w htpos (by rw [hcfg]; simp) houtlen houtlast, if_neg hcond]
    · have hne : O.take (j : ℕ) ≠ [] := by
        intro hnil
        have h1 := congrArg List.length hnil
        simp only [List.length_take, List.length_nil] at h1
        omega
      rw [List.getLast?_append_of_ne_nil _ hne, take_getLast?' O hjle, if_neg hj0,
        leftLet, if_neg hj0, hSW]
  have hLR : N.step (outRange M w 0 t ++ O.take (j : ℕ)).getLast? p
      ((O.drop (j : ℕ) ++ outRange M w (t + 1) T)).head?
      = N.step (leftLet M b₀ (prevLet (annot D w) u.length) ((annot D w)[u.length]?) q (j : ℕ)) p
        (rightLet M (prevLet (annot D w) u.length) ((annot D w)[u.length]?) q (j : ℕ)) := by
    rw [hLeft, hRhead]
  rw [hOout] at hs
  rcases hN : N.step
      (leftLet M b₀ (prevLet (annot D w) u.length) ((annot D w)[u.length]?) q (j : ℕ)) p
      (rightLet M (prevLet (annot D w) u.length) ((annot D w)[u.length]?) q (j : ℕ)) with
    oN | ⟨p', oN, dir⟩
  · -- `N` halts
    have hNs := hLR.trans hN
    rw [stepCfg_halt_eq N hNs] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨Cfg.halt, reaches_one (cutCfg_halt D M N b₀ outNil hiz ?_), Or.inl ⟨rfl, rfl⟩⟩
    rw [compStep_run D M N b₀ outNil hguard]
    exact compRun_main_halt D M N b₀ hN
  · cases dir with
    | true =>
      have hNs := hLR.trans hN
      rw [hdropj, List.cons_append] at hNs hs
      rw [stepCfg_right_cons N hNs] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      have hLapp : outRange M w 0 t ++ O.take (j : ℕ) ++ [O[(j : ℕ)]'hjlt]
          = outRange M w 0 t ++ O.take ((j : ℕ) + 1) := by
        rw [List.append_assoc, ← List.take_succ_eq_append_getElem hjlt]
      by_cases hjm : (j : ℕ) + 1 < m + 1
      · refine ⟨cutCfg (annot D w) u.length (stRun (coreMain p' q ⟨(j : ℕ) + 1, hjm⟩)), ?_, ?_⟩
        · refine stay_reaches D M N b₀ outNil hiz hznil ?_
          rw [compStep_run D M N b₀ outNil hguard]
          exact compRun_main_right_mid D M N b₀ hN hjm
        · refine Or.inr (Or.inl ⟨t, u, v, q, p', ⟨(j : ℕ) + 1, hjm⟩, htT, hcfg, rfl, ?_⟩)
          rw [hOout, hLapp]
      · have hjeq : (j : ℕ) = m := by omega
        have hLeq : outRange M w 0 t ++ O.take (j : ℕ) ++ [O[(j : ℕ)]'hjlt]
            = outRange M w 0 (t + 1) := by
          rw [hLapp, hjeq, ← hOlen, List.take_length, ← hOout,
            outRange_succ M w 0 t (Nat.zero_le _)]
        have hReq : O.drop ((j : ℕ) + 1) = [] := by
          rw [hjeq]
          exact List.drop_eq_nil_of_le (by omega)
        rcases hMs : M.step u.getLast? q v.head? with oM | ⟨q', oM, d⟩
        · have hhalt : cfgAt M w (t + 1) = some Cfg.halt :=
            cfgAt_succ_of_step M w hcfg (stepCfg_halt_eq M hMs)
          have hTeq : t + 1 = T := halt_time_unique M w hhalt hT
          refine ⟨cutCfg (annot D w) u.length (stRun (coreEnd p' q)), ?_, ?_⟩
          · refine stay_reaches D M N b₀ outNil hiz hznil ?_
            rw [compStep_run D M N b₀ outNil hguard]
            exact compRun_main_right_end_halt D M N b₀ hN (by omega) (hMlet.trans hMs)
          · refine Or.inr (Or.inr ⟨u, v, q, p', ?_, rfl, ?_⟩)
            · rw [show T - 1 = t by omega]
              exact hcfg
            · rw [hLeq, hReq, hTeq]
              simp
        · cases d with
          | true =>
            obtain ⟨a, v', hvcons, hc₁⟩ := stepCfg_move_right hMs hstepM
            have hnext' : cfgAt M w (t + 1) = some (Cfg.conf (u ++ [a]) q' v') := by
              rw [cfgAt_succ_of_step M w hcfg hstepM, hc₁]
            have hlt : t + 1 < T := by
              have hle : t + 1 ≤ T := by
                by_contra hcon
                exact hnext (cfgAt_none_mono M w (show T + 1 ≤ t + 1 by omega)
                  (cfgAt_halt_succ M w hT))
              rcases Nat.lt_or_ge (t + 1) T with h | h
              · exact h
              · exfalso
                rw [show t + 1 = T by omega, hT] at hnext'
                exact absurd hnext' (by simp)
            have hilt : u.length < w.length := by
              rw [← huv, hvcons]
              simp
            refine ⟨cutCfg (annot D w) (u.length + 1) (stRun (coreMain p' q' 0)), ?_, ?_⟩
            · refine reaches_one (cutCfg_right D M N b₀ outNil
                (show u.length < (annot D w).length by rw [annot_length]; exact hilt) ?_)
              rw [compStep_run D M N b₀ outNil hguard]
              exact compRun_main_right_end_move D M N b₀ hN (by omega) (hMlet.trans hMs)
            · refine Or.inr (Or.inl ⟨t + 1, u ++ [a], v', q', p', 0, hlt, hnext', ?_, ?_⟩)
              · simp
              · rw [hLeq, hReq]
                simp only [Fin.val_zero, List.take_zero, List.append_nil, List.drop_zero,
                  List.nil_append]
                rw [outRange_cons M w (t + 1) T hlt]
          | false =>
            obtain ⟨a, ha, hc₁⟩ := stepCfg_move_left hMs hstepM
            have hune : u ≠ [] := by
              intro h
              rw [h] at ha
              simp at ha
            have hipos : 0 < u.length := List.length_pos_iff.mpr hune
            have hnext' : cfgAt M w (t + 1) = some (Cfg.conf u.dropLast q' (a :: v)) := by
              rw [cfgAt_succ_of_step M w hcfg hstepM, hc₁]
            have hlt : t + 1 < T := by
              have hle : t + 1 ≤ T := by
                by_contra hcon
                exact hnext (cfgAt_none_mono M w (show T + 1 ≤ t + 1 by omega)
                  (cfgAt_halt_succ M w hT))
              rcases Nat.lt_or_ge (t + 1) T with h | h
              · exact h
              · exfalso
                rw [show t + 1 = T by omega, hT] at hnext'
                exact absurd hnext' (by simp)
            refine ⟨cutCfg (annot D w) (u.length - 1) (stRun (coreMain p' q' 0)), ?_, ?_⟩
            · refine reaches_one (cutCfg_left D M N b₀ outNil hipos hiz ?_)
              rw [compStep_run D M N b₀ outNil hguard]
              exact compRun_main_right_end_move D M N b₀ hN (by omega) (hMlet.trans hMs)
            · refine Or.inr (Or.inl ⟨t + 1, u.dropLast, a :: v, q', p', 0, hlt, hnext', ?_, ?_⟩)
              · simp
              · rw [hLeq, hReq]
                simp only [Fin.val_zero, List.take_zero, List.append_nil, List.drop_zero,
                  List.nil_append]
                rw [outRange_cons M w (t + 1) T hlt]
    | false =>
      have hNs := hLR.trans hN
      by_cases hj0 : (j : ℕ) = 0
      · have htpos : 0 < t := by
          rcases Nat.eq_zero_or_pos t with rfl | h
          · exfalso
            have hnil : (outRange M w 0 0 ++ O.take (j : ℕ)).getLast? = none := by
              rw [hj0]
              simp
            rw [stepCfg_left_none N hnil hNs] at hs
            simp at hs
          · exact h
        have hb : (outRange M w 0 t ++ O.take (j : ℕ)).getLast? = some b₀ := by
          rw [hj0, List.take_zero, List.append_nil]
          exact outRange_getLast? M w htpos (by rw [hcfg]; simp) houtlen houtlast
        rw [stepCfg_left_some N hb hNs] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have hcfg' : cfgAt M w ((t - 1) + 1)
            = some (Cfg.conf (w.take u.length) q (w.drop u.length)) := by
          rw [show t - 1 + 1 = t by omega, hu, hv]
          exact hcfg
        obtain ⟨c₀, hc₀, hstep₀⟩ := exists_pred M w hcfg'
        obtain ⟨u₀, q₀, v₀, rfl⟩ := exists_conf_of_stepCfg M hstep₀
        have hvis₀ : Visits M w (Cfg.conf u₀ q₀ v₀) := ⟨t - 1, hc₀⟩
        obtain ⟨⟨q₁, dirp⟩, hx⟩ := predOf_isSome D M hD w hiw hvis₀ hstep₀
        obtain ⟨k, oK, hcase, hvisK, hstepK⟩ := predOf_sound D M hD w hx
        have hpredcfg : cfgAt M w (t - 1) = some (Cfg.conf (w.take k) q₁ (w.drop k)) :=
          pred_unique M w hT hcfg' hvisK hstepK
        have hcompstep : compStep D M N b₀ outNil (prevLet (annot D w) u.length)
            (stRun (coreMain p q j)) ((annot D w)[u.length]?)
            = Sum.inr (stRun (coreMain p' q₁ (Fin.last m)), oN, dirp) := by
          rw [compStep_run D M N b₀ outNil hguard]
          exact compRun_main_left_zero D M N b₀ hN hj0 hx
        have hkw : k ≤ w.length := by
          rcases hcase with ⟨-, -, rfl⟩ | ⟨-, h, rfl⟩ <;> omega
        have hklen : (w.take k).length = k := by
          rw [List.length_take, min_eq_left hkw]
        have hcfin : Cfg.conf (outRange M w 0 t ++ O.take (j : ℕ)).dropLast p'
              (b₀ :: (O.drop (j : ℕ) ++ outRange M w (t + 1) T))
            = Cfg.conf (outRange M w 0 (t - 1) ++ (outAt M w (t - 1)).take m) p'
              ((outAt M w (t - 1)).drop m ++ outRange M w ((t - 1) + 1) T) := by
          obtain ⟨hdl, hdr⟩ :=
            outRange_dropLast M w htpos (by rw [hcfg]; simp) houtlen houtlast
          rw [hj0, List.take_zero, List.append_nil, hdl, hdr, List.drop_zero,
            show t - 1 + 1 = t by omega, ← hOout, ← outRange_cons M w t T htT]
          rfl
        refine ⟨cutCfg (annot D w) k (stRun (coreMain p' q₁ (Fin.last m))), ?_, ?_⟩
        · rcases hcase with ⟨rfl, hipos, rfl⟩ | ⟨rfl, hilt, rfl⟩
          · exact reaches_one (cutCfg_left D M N b₀ outNil hipos hiz hcompstep)
          · exact reaches_one (cutCfg_right D M N b₀ outNil
              (show u.length < (annot D w).length by rw [annot_length]; exact hilt) hcompstep)
        · exact Or.inr (Or.inl ⟨t - 1, w.take k, w.drop k, q₁, p', Fin.last m, by omega,
            hpredcfg, by rw [hklen], hcfin⟩)
      · have hj1 : (j : ℕ) - 1 < O.length := by omega
        have hne : O.take (j : ℕ) ≠ [] := by
          intro hnil
          have h1 := congrArg List.length hnil
          simp only [List.length_take, List.length_nil] at h1
          omega
        have haL : (outRange M w 0 t ++ O.take (j : ℕ)).getLast?
            = some (O[(j : ℕ) - 1]'hj1) := by
          rw [List.getLast?_append_of_ne_nil _ hne, take_getLast?' O hjle, if_neg hj0,
            List.getElem?_eq_getElem hj1]
        rw [stepCfg_left_some N haL hNs] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        have hjlt' : (j : ℕ) - 1 < m + 1 := by omega
        refine ⟨cutCfg (annot D w) u.length (stRun (coreMain p' q ⟨(j : ℕ) - 1, hjlt'⟩)), ?_, ?_⟩
        · refine stay_reaches D M N b₀ outNil hiz hznil ?_
          rw [compStep_run D M N b₀ outNil hguard]
          exact compRun_main_left_pos D M N b₀ hN hj0 hjlt'
        · refine Or.inr (Or.inl ⟨t, u, v, q, p', ⟨(j : ℕ) - 1, hjlt'⟩, htT, hcfg, rfl, ?_⟩)
          have hdl : (outRange M w 0 t ++ O.take (j : ℕ)).dropLast
              = outRange M w 0 t ++ O.take ((j : ℕ) - 1) := by
            rw [List.dropLast_append_of_ne_nil hne, take_dropLast O hjle]
          have hdr : (O[(j : ℕ) - 1]'hj1) :: O.drop (j : ℕ) = O.drop ((j : ℕ) - 1) := by
            rw [List.drop_eq_getElem_cons hj1, show (j : ℕ) - 1 + 1 = (j : ℕ) by omega]
          rw [hOout, hdl, ← List.cons_append, hdr]

/-- One step of the simulation, when the head of `N` is at the very end of the
output of `M`. -/
lemma compRel_step_end
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀)
    {w : List A} (hw : w ≠ []) {T : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    {u v : List A} {q : Q} {p : P}
    (hcfg : cfgAt M w (T - 1) = some (Cfg.conf u q v))
    {o : List C} {c' : Cfg B' P}
    (hs : N.stepCfg (Cfg.conf (outRange M w 0 T) p []) = some (o, c')) :
    ∃ Y, (compAut D M N m b₀ outNil).Reaches
        (cutCfg (annot D w) u.length (stRun (coreEnd p q))) o Y ∧
      compRel M w (annot D w) T Y c' := by
  classical
  have hTpos : 0 < T := by
    rcases Nat.eq_zero_or_pos T with rfl | h
    · rw [cfgAt_zero] at hT
      exact absurd hT (by simp)
    · exact h
  have huv : u ++ v = w := cfgAt_append M w (T - 1) hcfg
  have hiw : u.length ≤ w.length := by rw [← huv]; simp
  have hiz : u.length ≤ (annot D w).length := by rw [annot_length]; exact hiw
  have hznil : annot D w ≠ [] := by
    intro h
    apply hw
    have h1 : (annot D w).length = 0 := by rw [h]; rfl
    rw [annot_length] at h1
    simpa using h1
  have hguard : ¬ ((prevLet (annot D w) u.length).isNone = true ∧
      ((annot D w)[u.length]?).isNone = true) := not_both_none hznil hiz
  have hlast : (outRange M w 0 T).getLast? = some b₀ :=
    outRange_getLast? M w hTpos (by rw [hT]; simp) houtlen houtlast
  rcases hN : N.step (some b₀) p none with oN | ⟨p', oN, dir⟩
  · have hNs : N.step (outRange M w 0 T).getLast? p (([] : List B').head?) = Sum.inl oN := by
      rw [hlast]
      exact hN
    rw [stepCfg_halt_eq N hNs] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨Cfg.halt, reaches_one (cutCfg_halt D M N b₀ outNil hiz ?_), Or.inl ⟨rfl, rfl⟩⟩
    rw [compStep_run D M N b₀ outNil hguard]
    exact compRun_end_halt D M N b₀ hN
  · cases dir with
    | true =>
      have hNs : N.step (outRange M w 0 T).getLast? p (([] : List B').head?)
          = Sum.inr (p', oN, true) := by
        rw [hlast]
        exact hN
      rw [stepCfg_right_nil N hNs] at hs
      exact absurd hs (by simp)
    | false =>
      have hNs : N.step (outRange M w 0 T).getLast? p (([] : List B').head?)
          = Sum.inr (p', oN, false) := by
        rw [hlast]
        exact hN
      rw [stepCfg_left_some N hlast hNs] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hdl, hdr⟩ :=
        outRange_dropLast M w hTpos (by rw [hT]; simp) houtlen houtlast
      refine ⟨cutCfg (annot D w) u.length (stRun (coreMain p' q (Fin.last m))), ?_, ?_⟩
      · refine stay_reaches D M N b₀ outNil hiz hznil ?_
        rw [compStep_run D M N b₀ outNil hguard]
        exact compRun_end_left D M N b₀ hN
      · refine Or.inr (Or.inl ⟨T - 1, u, v, q, p', Fin.last m, by omega, hcfg, rfl, ?_⟩)
        rw [Fin.val_last, hdl, hdr, show T - 1 + 1 = T by omega, outRange_self]
        rfl

/-- The one-step condition of the simulation principle. -/
lemma compRel_step (hD : D.accepts = {z | (visitAut M).Accepts z})
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀)
    {w : List A} {z : List (AnnLet A S)} (hz : z = annot D w) (hw : w ≠ [])
    {T : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    (X : Cfg (AnnLet A S) (CompSt P Q (m + 1))) (c : Cfg B' P) (o : List C) (c' : Cfg B' P)
    (hR : compRel M w z T X c) (hs : N.stepCfg c = some (o, c')) :
    ∃ Y, (compAut D M N m b₀ outNil).Reaches X o Y ∧ compRel M w z T Y c' := by
  subst hz
  rcases hR with ⟨rfl, rfl⟩ | ⟨t, u, v, q, p, j, htT, hcfg, rfl, rfl⟩ |
    ⟨u, v, q, p, hcfg, rfl, rfl⟩
  · exact absurd hs (by simp [stepCfg])
  · exact compRel_step_main D M N b₀ outNil hD houtlen houtlast hw hT htT hcfg hs
  · exact compRel_step_end D M N b₀ outNil houtlen houtlast hw hT hcfg hs

/-- The simulation principle: a run of `N` on the output of `M` is mirrored by a
run of the composed transducer on the annotated input. -/
lemma compRel_sim (hD : D.accepts = {z | (visitAut M).Accepts z})
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀)
    {w : List A} (hw : w ≠ []) {T : ℕ} (hT : cfgAt M w T = some Cfg.halt)
    {c cend : Cfg B' P} {o : List C} (h : N.Reaches c o cend) :
    ∀ X, compRel M w (annot D w) T X c →
      ∃ Y, (compAut D M N m b₀ outNil).Reaches X o Y ∧ compRel M w (annot D w) T Y cend := by
  induction h with
  | refl c => exact fun X hX => ⟨X, Reaches.refl X, hX⟩
  | @step c c₁ c₂ o₁ o₂ hstep _ ih =>
      intro X hX
      obtain ⟨Y, hY, hRY⟩ :=
        compRel_step D M N b₀ outNil hD houtlen houtlast rfl hw hT X c o₁ c₁ hX hstep
      obtain ⟨Z, hZ, hRZ⟩ := ih Y hRY
      exact ⟨Z, hY.trans hZ, hRZ⟩

/-- The composed transducer computes the composition on correct annotations, and
the empty string on all other inputs. -/
theorem compAut_computes (hD : D.accepts = {z | (visitAut M).Accepts z})
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀)
    (hf : ∀ w, M.Computes w (f w)) (hg : ∀ v, N.Computes v (g v)) (z : List (AnnLet A S)) :
    (compAut D M N m b₀ (g (f []))).Computes z (compFun D f g z) := by
  classical
  by_cases hznil : z = []
  · subst hznil
    have hvalid : Valid D ([] : List (AnnLet A S)) := by
      intro i hi
      simp only [List.length_nil, Nat.le_zero] at hi
      subst hi
      exact trivial
    rw [compFun, if_pos hvalid]
    refine reaches_one ?_
    apply stepCfg_halt_eq
    simp [compAut, compStep]
  · by_cases hv : Valid D z
    · obtain ⟨w, rfl⟩ : ∃ w, z = annot D w := ⟨z.map AnnLet.letter, annot_of_valid D hv⟩
      have hw : w ≠ [] := by
        intro h
        apply hznil
        have h1 : (annot D w).length = 0 := by rw [annot_length, h]; rfl
        exact List.length_eq_zero_iff.mp h1
      rw [compFun, if_pos hv, annot_map_letter]
      obtain ⟨T, hT, hout⟩ := exists_halt_time M w (hf w)
      have hTpos : 0 < T := by
        rcases Nat.eq_zero_or_pos T with rfl | h
        · rw [cfgAt_zero] at hT
          exact absurd hT (by simp)
        · exact h
      have hstart : compRel M w (annot D w) T
          (cutCfg (annot D w) 0 (stRun (coreMain N.init M.init (0 : Fin (m + 1)))))
          (Cfg.conf [] N.init (f w)) := by
        refine Or.inr (Or.inl ⟨0, [], w, M.init, N.init, 0, hTpos, cfgAt_zero M w, rfl, ?_⟩)
        simp only [Fin.val_zero, List.take_zero, List.drop_zero, outRange_self,
          List.append_nil]
        rw [← hout, outRange_cons M w 0 T hTpos]
      obtain ⟨Y, hY, hRY⟩ := compRel_sim D M N b₀ (g (f [])) hD houtlen houtlast hw hT
        (hg (f w)) _ hstart
      have hYhalt : Y = Cfg.halt := by
        rcases hRY with ⟨h1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, hc⟩ | ⟨_, _, _, _, _, _, hc⟩
        · exact h1
        · exact absurd hc (by simp)
        · exact absurd hc (by simp)
      subst hYhalt
      have hpre := pre_reaches D M N b₀ (g (f [])) (m := m) hznil hv
      simpa using hpre.trans hY
    · rw [compFun, if_neg hv]
      exact scanR_halts D M N b₀ (g (f [])) hznil hv

end Machine

/-- **The composition of two two-way transducers**, in the special case where
all the transitions of the first one produce an output of the same length,
ending with a fixed letter. -/
theorem isTwoWay_comp_uniform [Finite A] [Finite B'] [Finite C] [Finite Q] [Finite P]
    {M : TwoWay A B' Q} {N : TwoWay B' C P} {m : ℕ} {b₀ : B'}
    (houtlen : ∀ l q r, (outWord (M.step l q r)).length = m + 1)
    (houtlast : ∀ l q r, (outWord (M.step l q r)).getLast? = some b₀)
    {f : List A → List B'} {g : List B' → List C}
    (hf : ∀ w, M.Computes w (f w)) (hg : ∀ v, N.Computes v (g v)) :
    IsTwoWay (fun w => g (f w)) := by
  classical
  obtain ⟨S, hS, D, hD⟩ := visitLang_isRegular M
  haveI : Fintype S := hS
  have hcomp : IsTwoWay (compFun D f g) :=
    ⟨CompSt P Q (m + 1), inferInstance, compAut D M N m b₀ (g (f [])),
      fun z => compAut_computes D M N b₀ f g hD houtlen houtlast hf hg z⟩
  have hrat : IsRationalFun (annot D) := isRationalFun_annot D
  have := isTwoWay_comp_rational hrat hcomp
  refine (funext ?_ : (compFun D f g ∘ annot D) = fun w => g (f w)) ▸ this
  intro w
  simp only [Function.comp_apply, compFun, if_pos (valid_annot D w), annot_map_letter]

end TwoWay

end Lax916827Proofs.Transducers
