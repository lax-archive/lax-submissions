/-
The data of the walking transducer of an mso transduction, and its correctness:
the hard half of Theorem `thm:logic-regular-functions` of *Transducers* (M. Bojańczyk).

After the normalisation of the type `τ` (`RequestProject/PartC/MSONorm.lean`,
Lemma `lem:logic-reduction-to-type-n`) an mso transduction is presented by a finite set of tags, a
universe formula and letter formulas with one free variable, and an order
formula with two free variables (`NormT`).  The questions that the walking
transducer of `RequestProject/PartC/WalkAut.lean` asks -- "is this element the
last one?", "where is its successor?" -- are the mso formulas built in
`RequestProject/PartC/MSOWalkForms.lean`; by Lemma `lem:logic-precomputation` the unary ones are
precomputed into the letters of a rational, letter-to-letter function `pre`, and
the binary ones become regular languages of infixes of `pre w`, read by a finite
family of deterministic automata.

This file assembles those answers into a `WalkAut.Data` and checks the nine
hypotheses of `WalkAut.computes_of_spec`, so that the walking transducer
computes the output of the transduction on every input of the form `pre w`.
The product of the family of automata is taken with an extra component
remembering the last letter read, which is what answers the unary question
"is this the first element of the output order?" at the end of a rightward
scan.
-/
import Lax314295Proofs.Source.PartC.MSOWalkForms
import Lax314295Proofs.Source.PartC.WalkAut
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace MSOWalk

open MSO NormT WalkAut

/-! ## The product of a finite family of deterministic automata -/

section ProdAut

variable {C K : Type} {sig : K → Type} (Mach : (k : K) → DFA C (sig k))

/-- The state of the product automaton: the last letter read, together with the
state of every automaton of the family. -/
abbrev PSt (C K : Type) (sig : K → Type) : Type := Option C × ((k : K) → sig k)

/-- The transition function of the product automaton. -/
def pstep (s : PSt C K sig) (c : C) : PSt C K sig :=
  (some c, fun k => (Mach k).step (s.2 k) c)

/-- The initial state of the product automaton. -/
def pstart : PSt C K sig := (none, fun k => (Mach k).start)

lemma foldl_pstep_snd (z : List C) (l : Option C) (s : (k : K) → sig k) (k : K) :
    (List.foldl (pstep Mach) (l, s) z).2 k = (Mach k).evalFrom (s k) z := by
  induction z generalizing l s with
  | nil => rfl
  | cons c z ih => exact ih (some c) (fun k => (Mach k).step (s k) c)

lemma foldl_pstep_fst (z : List C) (l : Option C) (s : (k : K) → sig k) :
    (List.foldl (pstep Mach) (l, s) z).1 = if z = [] then l else z.getLast? := by
  induction z generalizing l s with
  | nil => simp
  | cons c z ih =>
      rw [List.foldl_cons,
        show pstep Mach (l, s) c = (some c, fun k => (Mach k).step (s k) c) from rfl,
        ih (some c) (fun k => (Mach k).step (s k) c)]
      cases z with
      | nil => simp
      | cons d z => simp [List.getLast?_cons_cons]

end ProdAut

/-! ## The tags of a normalised transduction -/

/-- A list of all the tags of a normalised transduction. -/
noncomputable def tagList {A B : Type} (N : NormT A B) : List N.Tag :=
  letI : Fintype N.Tag := @Fintype.ofFinite _ N.finTag
  Finset.univ.toList

lemma mem_tagList {A B : Type} (N : NormT A B) (t : N.Tag) : t ∈ tagList N := by
  letI : Fintype N.Tag := @Fintype.ofFinite _ N.finTag
  simp [tagList]

/-! ## The data of the walk -/

/-- The index of the two families of binary questions: "is the element with tag
`t'` at the marked position to the right the successor of the element with tag
`t` at the marked position to the left?", and the mirror question. -/
abbrev QIdx {A B : Type} (N : NormT A B) : Type := (N.Tag × N.Tag) ⊕ (N.Tag × N.Tag)

section Build

variable {A B C : Type} (N : NormT A B) {sig : QIdx N → Type}
  (Mach : (k : QIdx N) → DFA C (sig k)) (nilOut : List B)
  (Flb : N.Tag → B → Set C) (FMax FMin FR : N.Tag → Set C) (FH : N.Tag → N.Tag → Set C)

open scoped Classical in
/-- The data of the walking transducer of a normalised mso transduction, built
from the precomputed answers to the unary questions (the sets `Flb`, `FMax`,
`FMin`, `FR` and `FH` of letters) and to the binary questions (the family
`Mach` of automata). -/
noncomputable def walkData [Nonempty B] :
    Data C B N.Tag (PSt C (QIdx N) sig) where
  lb := fun i c => if h : ∃ b, c ∈ Flb i b then h.choose else Classical.arbitrary B
  isMax := fun i c => c ∈ FMax i
  succH := fun i j c => c ∈ FH i j
  succR := fun i c => c ∈ FR i
  Dstep := pstep Mach
  Dstart := pstart Mach
  accR := fun o j s =>
    match o with
    | none => ∃ c, s.1 = some c ∧ c ∈ FMin j
    | some i => s.2 (Sum.inl (i, j)) ∈ (Mach (Sum.inl (i, j))).accept
  accL := fun i j s => s.2 (Sum.inr (i, j)) ∈ (Mach (Sum.inr (i, j))).accept
  outNil := nilOut

variable [Nonempty B]

open scoped Classical in
lemma walkData_lb_of_exists (i : N.Tag) (c : C) (h : ∃ b, c ∈ Flb i b) :
    (walkData N Mach nilOut Flb FMax FMin FR FH).lb i c = h.choose := dif_pos h

@[simp] lemma walkData_isMax (i : N.Tag) (c : C) :
    (walkData N Mach nilOut Flb FMax FMin FR FH).isMax i c ↔ c ∈ FMax i := Iff.rfl

@[simp] lemma walkData_succH (i j : N.Tag) (c : C) :
    (walkData N Mach nilOut Flb FMax FMin FR FH).succH i j c ↔ c ∈ FH i j := Iff.rfl

@[simp] lemma walkData_succR (i : N.Tag) (c : C) :
    (walkData N Mach nilOut Flb FMax FMin FR FH).succR i c ↔ c ∈ FR i := Iff.rfl

@[simp] lemma walkData_accR_some (i j : N.Tag) (s : PSt C (QIdx N) sig) :
    (walkData N Mach nilOut Flb FMax FMin FR FH).accR (some i) j s ↔
      s.2 (Sum.inl (i, j)) ∈ (Mach (Sum.inl (i, j))).accept := Iff.rfl

@[simp] lemma walkData_accR_none (j : N.Tag) (s : PSt C (QIdx N) sig) :
    (walkData N Mach nilOut Flb FMax FMin FR FH).accR none j s ↔
      ∃ c, s.1 = some c ∧ c ∈ FMin j := Iff.rfl

@[simp] lemma walkData_accL (i j : N.Tag) (s : PSt C (QIdx N) sig) :
    (walkData N Mach nilOut Flb FMax FMin FR FH).accL i j s ↔
      s.2 (Sum.inr (i, j)) ∈ (Mach (Sum.inr (i, j))).accept := Iff.rfl

@[simp] lemma walkData_outNil :
    (walkData N Mach nilOut Flb FMax FMin FR FH).outNil = nilOut := rfl

lemma segFold_walkData_snd (u : List C) (a b : ℕ) (k : QIdx N) :
    (segFold (walkData N Mach nilOut Flb FMax FMin FR FH) u a b).2 k
      = (Mach k).eval ((u.take b).drop a) :=
  foldl_pstep_snd Mach _ none (fun k => (Mach k).start) k

lemma segFold_walkData_fst (u : List C) (a b : ℕ) :
    (segFold (walkData N Mach nilOut Flb FMax FMin FR FH) u a b).1
      = if (u.take b).drop a = [] then none else ((u.take b).drop a).getLast? :=
  foldl_pstep_fst Mach _ none (fun k => (Mach k).start)

end Build

/-! ## Auxiliary lemmas -/

lemma nodup_index {α : Type} {l : List α} (h : l.Nodup) {r r' : ℕ} {x : α}
    (h1 : l[r]? = some x) (h2 : l[r']? = some x) : r = r' := by
  obtain ⟨hr, hre⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hr', hre'⟩ := List.getElem?_eq_some_iff.1 h2
  exact h.getElem_inj_iff.1 (hre.trans hre'.symm)

/-- The letter form of the unary part of Lemma `lem:logic-precomputation`: a formula with one free
variable holds at a position if and only if the letter of the precomputed
string at that position belongs to the corresponding set. -/
lemma letter_mem_iff {A C : Type} {pre : List A → List C} {F : Set C} {φ : MSO A}
    (hF : ∀ (w : List A) (x : ℕ), x < w.length →
      (MSO.Sat w (fun _ => x) (fun _ => ∅) φ ↔ ∃ c ∈ F, (pre w)[x]? = some c))
    (w : List A) (x : ℕ) (hx : x < w.length) (a : C) (ha : (pre w)[x]? = some a) :
    (a ∈ F ↔ MSO.Sat w (fun _ => x) (fun _ => ∅) φ) := by
  rw [hF w x hx]
  constructor
  · intro h; exact ⟨a, h, ha⟩
  · rintro ⟨c, hc, hcx⟩
    rw [ha, Option.some_inj] at hcx
    exact hcx ▸ hc

/-! ## The walking transducer computes the transduction -/

section Computes

variable {A B C : Type} [Nonempty B] (N : NormT A B) {sig : QIdx N → Type}
  (Mach : (k : QIdx N) → DFA C (sig k))
  (pre : List A → List C) (fv : List A → List B) (esf : List A → List N.Elt)
  (Flb : N.Tag → B → Set C) (FMax FMin FR : N.Tag → Set C) (FH : N.Tag → N.Tag → Set C)

/-- **The walking transducer computes the output of the normalised mso
transduction**, on every string of the form `pre w`.  The hypotheses are the
specifications of the precomputed answers: `hFlb`, `hFMax`, `hFMin`, `hFR` and
`hFH` for the unary questions, `hMS` and `hML` for the binary ones. -/
theorem computes_walkData
    (hlenpre : ∀ w, (pre w).length = w.length)
    (hProp : ∀ w : List A, 0 < w.length → N.Proper w)
    (hPres : ∀ w : List A, 0 < w.length → N.Presents w (esf w) (fv w))
    (hFlb : ∀ (t : N.Tag) (b : B) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ Flb t b ↔ MSO.Sat w (fun _ => x) (fun _ => ∅) (N.Lb t b)))
    (hFMax : ∀ (t : N.Tag) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ FMax t ↔ MSO.Sat w (fun _ => x) (fun _ => ∅) (N.isMaxF (tagList N) t)))
    (hFMin : ∀ (t : N.Tag) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ FMin t ↔ MSO.Sat w (fun _ => x) (fun _ => ∅) (N.isMinF (tagList N) t)))
    (hFR : ∀ (t : N.Tag) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ FR t ↔ MSO.Sat w (fun _ => x) (fun _ => ∅) (N.succRF (tagList N) t)))
    (hFH : ∀ (t t' : N.Tag) (w : List A) (x : ℕ), x < w.length → ∀ a : C,
      (pre w)[x]? = some a →
        (a ∈ FH t t' ↔ MSO.Sat w (fun _ => x) (fun _ => ∅) (N.succHF (tagList N) t t')))
    (hMS : ∀ (t t' : N.Tag) (w : List A) (x y : ℕ), x ≤ y → y < w.length →
      (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) (N.isSuccF (tagList N) t t') ↔
        ((pre w).take (y + 1)).drop x ∈ (Mach (Sum.inl (t, t'))).accepts))
    (hML : ∀ (t t' : N.Tag) (w : List A) (x y : ℕ), x ≤ y → y < w.length →
      (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅)
          (N.isSuccSwapF (tagList N) t t') ↔
        ((pre w).take (y + 1)).drop x ∈ (Mach (Sum.inr (t, t'))).accepts))
    (w : List A) :
    (aut (walkData N Mach (fv []) Flb FMax FMin FR FH)).Computes (pre w) (fv w) := by
  classical
  by_cases hw : 0 < w.length
  swap
  · have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hw0
    have hp0 : pre [] = [] := List.eq_nil_of_length_eq_zero (by simp [hlenpre])
    rw [hp0]
    exact computes_nil _
  set D := walkData N Mach (fv []) Flb FMax FMin FR FH with hD
  have hProp' : N.Proper w := hProp w hw
  have hPres' : N.Presents w (esf w) (fv w) := hPres w hw
  have hnodup : (esf w).Nodup := hPres'.1
  have hmem : ∀ x, x ∈ esf w ↔ N.sel w x := hPres'.2.1
  have hlenev : (esf w).length = (fv w).length := hPres'.2.2.2.1
  have hlabs := hPres'.2.2.2.2
  have hulen : (pre w).length = w.length := hlenpre w
  have hposw : ∀ x ∈ esf w, x.2 < w.length := fun x hx => ((hmem x).1 hx).1
  have hmemof : ∀ (r : ℕ) (x : N.Elt), (esf w)[r]? = some x → x ∈ esf w :=
    fun r x h => List.mem_iff_getElem?.2 ⟨r, h⟩
  have hgetu : ∀ p, p < w.length → ∃ a, (pre w)[p]? = some a := by
    intro p hp
    exact ⟨_, List.getElem?_eq_getElem (by rw [hulen]; exact hp)⟩
  have hu : 0 < (pre w).length := by rw [hulen]; exact hw
  -- the length of the enumeration
  have hlen0 : (esf w).length = (fv w).length := hlenev
  -- the positions of the elements
  have hpos : ∀ x ∈ esf w, x.2 < (pre w).length := by
    intro x hx; rw [hulen]; exact hposw x hx
  -- the letters
  have hlab : ∀ (r : ℕ) (i : N.Tag) (p : ℕ) (a : C), (esf w)[r]? = some (i, p) →
      (pre w)[p]? = some a → (fv w)[r]? = some (D.lb i a) := by
    intro r i p a hes ha
    obtain ⟨hr, hre⟩ := List.getElem?_eq_some_iff.1 hes
    have hrv : r < (fv w).length := by rw [← hlenev]; exact hr
    have hmemx : (i, p) ∈ esf w := hre ▸ List.getElem_mem hr
    have hp : p < w.length := hposw _ hmemx
    have hsel : N.sel w (i, p) := (hmem _).1 hmemx
    have hlabv : N.lab w (i, p) (fv w)[r] := by
      have := hlabs r hr hrv
      rw [hre] at this
      exact this
    have hin : a ∈ Flb i (fv w)[r] := (hFlb i (fv w)[r] w p hp a ha).2 hlabv
    have hex : ∃ b, a ∈ Flb i b := ⟨(fv w)[r], hin⟩
    have hlab2 : N.lab w (i, p) hex.choose := (hFlb i hex.choose w p hp a ha).1 hex.choose_spec
    have heq : hex.choose = (fv w)[r] := hProp'.1 (i, p) _ _ hsel hlab2 hlabv
    have hDlb : D.lb i a = hex.choose := by
      rw [hD]; exact walkData_lb_of_exists N Mach (fv []) Flb FMax FMin FR FH i a hex
    rw [List.getElem?_eq_getElem hrv, hDlb, heq]
  -- the last element
  have hmax : ∀ (r : ℕ) (i : N.Tag) (p : ℕ) (a : C), (esf w)[r]? = some (i, p) →
      (pre w)[p]? = some a → (D.isMax i a ↔ r + 1 = (esf w).length) := by
    intro r i p a hes ha
    have hp : p < w.length := hposw _ (hmemof _ _ hes)
    rw [hD, walkData_isMax, hFMax i w p hp a ha, sat_isMaxF (mem_tagList N) hProp' hPres' i hp]
    constructor
    · rintro ⟨r', hr', hlast⟩
      rw [nodup_index hnodup hes hr']
      exact hlast
    · intro h
      exact ⟨r, hes, h⟩
  -- the successor in the same position
  have hsuccH : ∀ (r : ℕ) (i : N.Tag) (p : ℕ) (a : C) (i₁ : N.Tag) (p₁ : ℕ),
      (esf w)[r]? = some (i, p) → (esf w)[r + 1]? = some (i₁, p₁) → (pre w)[p]? = some a →
      ∀ j, (D.succH i j a ↔ (p₁ = p ∧ i₁ = j)) := by
    intro r i p a i₁ p₁ hes hes1 ha j
    have hp : p < w.length := hposw _ (hmemof _ _ hes)
    rw [hD, walkData_succH, hFH i j w p hp a ha, sat_succHF (mem_tagList N) hProp' hPres' i j hp]
    constructor
    · rintro ⟨r', hr0, hr1⟩
      have hrr : r' = r := nodup_index hnodup hr0 hes
      subst hrr
      have hcon := hes1.symm.trans hr1
      rw [Option.some_inj, Prod.ext_iff] at hcon
      exact ⟨hcon.2, hcon.1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨r, hes, hes1⟩
  -- the successor to the right
  have hsuccR : ∀ (r : ℕ) (i : N.Tag) (p : ℕ) (a : C) (i₁ : N.Tag) (p₁ : ℕ),
      (esf w)[r]? = some (i, p) → (esf w)[r + 1]? = some (i₁, p₁) → (pre w)[p]? = some a →
      (D.succR i a ↔ p < p₁) := by
    intro r i p a i₁ p₁ hes hes1 ha
    have hp : p < w.length := hposw _ (hmemof _ _ hes)
    rw [hD, walkData_succR, hFR i w p hp a ha, sat_succRF (mem_tagList N) hProp' hPres' i hp]
    constructor
    · rintro ⟨r', q, t', hr0, hr1, hlt⟩
      have hrr : r' = r := nodup_index hnodup hr0 hes
      subst hrr
      have hcon := hes1.symm.trans hr1
      rw [Option.some_inj, Prod.ext_iff] at hcon
      omega
    · intro h
      exact ⟨r, p₁, i₁, hes, hes1, h⟩
  -- the rightward search for the successor
  have haccR : ∀ (r : ℕ) (i : N.Tag) (p : ℕ) (i₁ : N.Tag) (p₁ : ℕ),
      (esf w)[r]? = some (i, p) → (esf w)[r + 1]? = some (i₁, p₁) →
      ∀ q, p ≤ q → q < (pre w).length → ∀ j,
        (D.accR (some i) j (segFold D (pre w) p (q + 1)) ↔ (j = i₁ ∧ q = p₁)) := by
    intro r i p i₁ p₁ hes hes1 q hpq hq j
    have hqw : q < w.length := by rwa [hulen] at hq
    have hp : p < w.length := hposw _ (hmemof _ _ hes)
    have hfo0 : (if (0 : ℕ) = 0 then p else q) = p := by norm_num
    have hfo1 : (if (1 : ℕ) = 0 then p else q) = q := by norm_num
    rw [hD, walkData_accR_some, segFold_walkData_snd, ← DFA.mem_accepts,
      ← hMS i j w p q hpq hqw,
      sat_isSuccF (mem_tagList N) hProp' hPres' i j (by rw [hfo0]; exact hp)
        (by rw [hfo1]; exact hqw), hfo0, hfo1]
    constructor
    · rintro ⟨r', hr0, hr1⟩
      have hrr : r' = r := nodup_index hnodup hr0 hes
      subst hrr
      have hcon := hes1.symm.trans hr1
      rw [Option.some_inj, Prod.ext_iff] at hcon
      exact ⟨hcon.1.symm, hcon.2.symm⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨r, hes, hes1⟩
  -- the leftward search for the successor
  have haccL : ∀ (r : ℕ) (i : N.Tag) (p : ℕ) (i₁ : N.Tag) (p₁ : ℕ),
      (esf w)[r]? = some (i, p) → (esf w)[r + 1]? = some (i₁, p₁) →
      ∀ q, q ≤ p → ∀ j,
        (D.accL i j (segFold D (pre w) q (p + 1)) ↔ (j = i₁ ∧ q = p₁)) := by
    intro r i p i₁ p₁ hes hes1 q hqp j
    have hp : p < w.length := hposw _ (hmemof _ _ hes)
    have hfo0 : (if (0 : ℕ) = 0 then q else p) = q := by norm_num
    have hfo1 : (if (1 : ℕ) = 0 then q else p) = p := by norm_num
    rw [hD, walkData_accL, segFold_walkData_snd, ← DFA.mem_accepts,
      ← hML i j w q p hqp hp,
      sat_isSuccSwapF (mem_tagList N) hProp' hPres' i j (by rw [hfo0]; exact hqp.trans_lt hp)
        (by rw [hfo1]; exact hp), hfo0, hfo1]
    constructor
    · rintro ⟨r', hr0, hr1⟩
      have hrr : r' = r := nodup_index hnodup hr0 hes
      subst hrr
      have hcon := hes1.symm.trans hr1
      rw [Option.some_inj, Prod.ext_iff] at hcon
      exact ⟨hcon.1.symm, hcon.2.symm⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨r, hes, hes1⟩
  -- the search for the first element
  have haccRmin : ∀ q, q < (pre w).length → ∀ j,
      (D.accR none j (segFold D (pre w) 0 (q + 1)) ↔ (esf w)[0]? = some (j, q)) := by
    intro q hq j
    have hqw : q < w.length := by rwa [hulen] at hq
    obtain ⟨a, ha⟩ := hgetu q hqw
    have hne : ((pre w).take (q + 1)).drop 0 ≠ [] := by
      rw [List.drop_zero]
      intro hcon
      have hl : ((pre w).take (q + 1)).length = 0 := by rw [hcon]; rfl
      rw [List.length_take] at hl
      omega
    rw [hD, walkData_accR_none, segFold_walkData_fst, if_neg hne, List.drop_zero,
      WalkAut.getLast?_take_pos (by omega) (by omega)]
    simp only [Nat.add_sub_cancel, ha, Option.some_inj]
    rw [show (∃ c, a = c ∧ c ∈ FMin j) ↔ a ∈ FMin j from ⟨by rintro ⟨c, rfl, hc⟩; exact hc,
      fun h => ⟨a, rfl, h⟩⟩]
    rw [hFMin j w q hqw a ha, sat_isMinF (mem_tagList N) hProp' hPres' j hqw]
  exact computes_of_spec (D := D) (es := esf w) hlen0 hpos hlab hmax hsuccH hsuccR haccR haccL
    haccRmin hu

end Computes

end MSOWalk

end Lax314295Proofs.Transducers
