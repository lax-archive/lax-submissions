/-
The backwards translation of first-order formulas along an mso transduction.

This is the syntactic heart of the closure of first-order transductions under
composition ("first-order transductions are closed under composition, which is
proved by substituting formulas", in the sketch that the book gives for
Theorem `nolabel:thm-fo-transduction-into-primes`).

Let `T : ITrans A B` be a transduction, `w` an input string and `v` its output.
The positions of `v` are the elements selected by the universe formulas of `T`,
ordered by its order formulas; such an element is either a *copy* `(i, p)` of a
position `p` of `w`, or one of the finitely many *extra* elements.  A first-order
formula `φ` over `B`, evaluated in `v`, can therefore be translated into a
first-order formula over `A`, evaluated in `w`: one fixes, for every variable of
`φ`, the *kind* of the element of `v` that it denotes (`FOTr.Kind T`), the
atomic formulas become the corresponding universe, order and letter formulas of
`T` plugged in at the relevant variables (`FOTr.selF`, `FOTr.ordF`,
`FOTr.labF`), and a quantifier becomes a finite disjunction, over the kinds, of
a quantifier relativised to the selected elements of that kind.

`FOTr.sat_tr` is the correctness statement of the translation, and `FOTr.trZ`
is the variant needed for the formulas of the extra elements of a second
transduction, which are evaluated at the position `0` of `v`.
-/
import Lax314295Proofs.Source.PartC.TransEnum
import Lax314295Proofs.Source.PartC.FOPlug
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers
namespace FOTr

open MSO

variable {A B : Type}

/-! ## Kinds of elements -/

/-- The kind of an element of the output structure: a copy of the input
positions, or one of the extra elements. -/
abbrev Kind (T : ITrans A B) : Type := T.P ⊕ T.E

/-- The element of the output structure of the given kind sitting above the
given input position (the position is ignored by the extra elements). -/
def eltOf (T : ITrans A B) : Kind T → ℕ → T.Elt
  | Sum.inl i, p => Sum.inl (i, p)
  | Sum.inr r, _ => Sum.inr r

/-! ## The atomic formulas of the translation -/

variable (T : ITrans A B)

/-- "The element of kind `k` above the position `x_u` is selected." -/
noncomputable def selF : Kind T → ℕ → MSO A
  | Sum.inl i, u => atvF u (T.univP i)
  | Sum.inr r, _ => atZeroF (T.univC r)

/-- "The element of kind `k` above `x_u` precedes the element of kind `k'`
above `x_u'`." -/
noncomputable def ordF : Kind T → ℕ → Kind T → ℕ → MSO A
  | Sum.inl i, u, Sum.inl i', u' => atv2F u u' (T.ordPP i i')
  | Sum.inl i, u, Sum.inr r', _ => atvF u (T.ordPC i r')
  | Sum.inr r, _, Sum.inl i', u' => atvF u' (T.ordCP r i')
  | Sum.inr r, _, Sum.inr r', _ => atZeroF (T.ordCC r r')

/-- "The element of kind `k` above `x_u` carries the letter `b`." -/
noncomputable def labF : Kind T → ℕ → B → MSO A
  | Sum.inl i, u, b => atvF u (T.labP i b)
  | Sum.inr r, _, b => atZeroF (T.labC r b)

variable {T}

lemma isFO_selF (hFO : T.AllFO) (k : Kind T) (u : ℕ) : (selF T k u).IsFO := by
  cases k with
  | inl i => exact isFO_atvF _ (hFO.1 i)
  | inr r => exact isFO_atZeroF (hFO.2.1 r)

lemma isFO_ordF (hFO : T.AllFO) (k : Kind T) (u : ℕ) (k' : Kind T) (u' : ℕ) :
    (ordF T k u k' u').IsFO := by
  cases k with
  | inl i =>
      cases k' with
      | inl i' => exact isFO_atv2F _ _ (hFO.2.2.2.2.1 i i')
      | inr r' => exact isFO_atvF _ (hFO.2.2.2.2.2.1 i r')
  | inr r =>
      cases k' with
      | inl i' => exact isFO_atvF _ (hFO.2.2.2.2.2.2.1 r i')
      | inr r' => exact isFO_atZeroF (hFO.2.2.2.2.2.2.2 r r')

lemma isFO_labF (hFO : T.AllFO) (k : Kind T) (u : ℕ) (b : B) : (labF T k u b).IsFO := by
  cases k with
  | inl i => exact isFO_atvF _ (hFO.2.2.1 i b)
  | inr r => exact isFO_atZeroF (hFO.2.2.2.1 r b)

lemma sat_selF (hFO : T.AllFO) (w : List A) (k : Kind T) (u : ℕ) (fo : ℕ → ℕ) (so : ℕ → Set ℕ)
    (hu : ∀ i : T.P, k = Sum.inl i → fo u < w.length) :
    Sat w fo so (selF T k u) ↔ T.selected w (eltOf T k (fo u)) := by
  cases k with
  | inl i =>
      rw [selF, sat_atvF w u (hFO.1 i) fo so (hu i rfl)]
      exact ⟨fun h => ⟨hu i rfl, h⟩, fun h => h.2⟩
  | inr r => exact sat_atZeroF w (hFO.2.1 r) fo so

lemma sat_ordF (hFO : T.AllFO) (w : List A) (k : Kind T) (u : ℕ) (k' : Kind T) (u' : ℕ)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ)
    (hu : ∀ i : T.P, k = Sum.inl i → fo u < w.length)
    (hu' : ∀ i : T.P, k' = Sum.inl i → fo u' < w.length) :
    Sat w fo so (ordF T k u k' u') ↔
      T.ordRel w (eltOf T k (fo u)) (eltOf T k' (fo u')) := by
  cases k with
  | inl i =>
      cases k' with
      | inl i' =>
          rw [ordF, sat_atv2F w u u' (hFO.2.2.2.2.1 i i') fo so (hu i rfl) (hu' i' rfl)]
          rfl
      | inr r' =>
          rw [ordF, sat_atvF w u (hFO.2.2.2.2.2.1 i r') fo so (hu i rfl)]
          rfl
  | inr r =>
      cases k' with
      | inl i' =>
          rw [ordF, sat_atvF w u' (hFO.2.2.2.2.2.2.1 r i') fo so (hu' i' rfl)]
          rfl
      | inr r' =>
          rw [ordF, sat_atZeroF w (hFO.2.2.2.2.2.2.2 r r') fo so]
          rfl

lemma sat_labF (hFO : T.AllFO) (w : List A) (k : Kind T) (u : ℕ) (b : B) (fo : ℕ → ℕ)
    (so : ℕ → Set ℕ) (hu : ∀ i : T.P, k = Sum.inl i → fo u < w.length) :
    Sat w fo so (labF T k u b) ↔ T.labRel w (eltOf T k (fo u)) b := by
  cases k with
  | inl i =>
      rw [labF, sat_atvF w u (hFO.2.2.1 i b) fo so (hu i rfl)]
      rfl
  | inr r =>
      rw [labF, sat_atZeroF w (hFO.2.2.2.1 r b) fo so]
      rfl

/-! ## The translation -/

variable (T)

/-- The backwards translation of a formula over the output alphabet into a
formula over the input alphabet, along the transduction `T`.  The function `κ`
assigns to every variable the kind of the output element that it denotes; the
lists `lP` and `lE` enumerate the kinds. -/
noncomputable def tr (lP : List T.P) (lE : List T.E) : (ℕ → Kind T) → MSO B → MSO A
  | κ, MSO.le i j => ordF T (κ i) i (κ j) j
  | κ, MSO.lab b i => labF T (κ i) i b
  | _, MSO.mem _ _ => MSO.ff
  | κ, MSO.not φ => MSO.not (tr lP lE κ φ)
  | κ, MSO.and φ ψ => MSO.and (tr lP lE κ φ) (tr lP lE κ ψ)
  | κ, MSO.or φ ψ => MSO.or (tr lP lE κ φ) (tr lP lE κ ψ)
  | κ, MSO.exFO m φ =>
      MSO.or
        (bigOr (lP.map (fun i =>
          MSO.exFO m (MSO.and (selF T (Sum.inl i) m)
            (tr lP lE (Function.update κ m (Sum.inl i)) φ)))))
        (bigOr (lE.map (fun r =>
          MSO.and (selF T (Sum.inr r) m)
            (tr lP lE (Function.update κ m (Sum.inr r)) φ))))
  | _, MSO.exSO _ _ => MSO.ff

variable {T}

lemma isFO_tr (hFO : T.AllFO) (lP : List T.P) (lE : List T.E) :
    ∀ (φ : MSO B) (κ : ℕ → Kind T), (tr T lP lE κ φ).IsFO := by
  intro φ
  induction φ with
  | le i j => exact fun κ => isFO_ordF hFO _ _ _ _
  | lab b i => exact fun κ => isFO_labF hFO _ _ _
  | mem i j => exact fun _ => isFO_ff
  | not φ ih => exact fun κ => ih κ
  | and φ ψ ihφ ihψ => exact fun κ => ⟨ihφ κ, ihψ κ⟩
  | or φ ψ ihφ ihψ => exact fun κ => ⟨ihφ κ, ihψ κ⟩
  | exFO m φ ih =>
      intro κ
      refine ⟨isFO_bigOr _ ?_, isFO_bigOr _ ?_⟩
      · intro ψ hψ
        rw [List.mem_map] at hψ
        obtain ⟨i, -, rfl⟩ := hψ
        exact ⟨isFO_selF hFO _ _, ih _⟩
      · intro ψ hψ
        rw [List.mem_map] at hψ
        obtain ⟨r, -, rfl⟩ := hψ
        exact ⟨isFO_selF hFO _ _, ih _⟩
  | exSO i φ _ => exact fun _ => isFO_ff

/-! ## Correctness of the translation -/

section Correct

variable {w : List A} {v : List B} {es : List T.Elt}

/-- The compatibility of a valuation of the variables in the input string with
a valuation in the output string: the variable `i` denotes the output position
`ofo i`, whose element is of kind `κ i` and sits above the input position
`fo i`. -/
def Compat (T : ITrans A B) (es : List T.Elt) (κ : ℕ → Kind T) (fo ofo : ℕ → ℕ)
    (S : Set ℕ) : Prop :=
  ∀ i ∈ S, ∃ h : ofo i < es.length, es[ofo i] = eltOf T (κ i) (fo i)

lemma Compat.lt_length (H : ITrans.Enum T w v es) {κ : ℕ → Kind T} {fo ofo : ℕ → ℕ} {S : Set ℕ}
    (hc : Compat T es κ fo ofo S) {i : ℕ} (hi : i ∈ S) {i₀ : T.P} (hk : κ i = Sum.inl i₀) :
    fo i < w.length := by
  obtain ⟨h, he⟩ := hc i hi
  rw [hk] at he
  exact H.lt_length_of_getElem_inl h he

theorem sat_tr (hFO : T.AllFO) (hP : T.Proper) (H : ITrans.Enum T w v es)
    {lP : List T.P} {lE : List T.E} (hlP : ∀ i, i ∈ lP) (hlE : ∀ r, r ∈ lE) :
    ∀ (φ : MSO B), φ.IsFO → ∀ (κ : ℕ → Kind T) (fo ofo : ℕ → ℕ) (so : ℕ → Set ℕ)
      (so' : ℕ → Set ℕ), Compat T es κ fo ofo φ.freeFO →
      (Sat v ofo so' φ ↔ Sat w fo so (tr T lP lE κ φ)) := by
  intro φ
  induction φ with
  | le i j =>
      intro _ κ fo ofo so so' hc
      have hi : i ∈ (MSO.le (A := B) i j).freeFO := by simp [freeFO]
      have hj : j ∈ (MSO.le (A := B) i j).freeFO := by simp [freeFO]
      obtain ⟨hli, hei⟩ := hc i hi
      obtain ⟨hlj, hej⟩ := hc j hj
      rw [show tr T lP lE κ (MSO.le (A := B) i j) = ordF T (κ i) i (κ j) j from rfl,
        sat_ordF hFO w _ _ _ _ fo so (fun i₀ hk => hc.lt_length H hi hk)
          (fun i₀ hk => hc.lt_length H hj hk),
        ← hei, ← hej, H.ord_iff_le hP hli hlj]
      exact Iff.rfl
  | lab b i =>
      intro _ κ fo ofo so so' hc
      have hi : i ∈ (MSO.lab (A := B) b i).freeFO := by simp [freeFO]
      obtain ⟨hli, hei⟩ := hc i hi
      rw [show tr T lP lE κ (MSO.lab (A := B) b i) = labF T (κ i) i b from rfl,
        sat_labF hFO w _ _ _ fo so (fun i₀ hk => hc.lt_length H hi hk), ← hei,
        H.getElem?_eq hP hli b]
      exact Iff.rfl
  | mem i j => intro h; exact absurd h (by simp [IsFO])
  | not φ ih =>
      intro hfo κ fo ofo so so' hc
      have := ih hfo κ fo ofo so so' hc
      exact not_congr this
  | and φ ψ ihφ ihψ =>
      intro hfo κ fo ofo so so' hc
      exact and_congr (ihφ hfo.1 κ fo ofo so so' (fun i hi => hc i (Or.inl hi)))
        (ihψ hfo.2 κ fo ofo so so' (fun i hi => hc i (Or.inr hi)))
  | or φ ψ ihφ ihψ =>
      intro hfo κ fo ofo so so' hc
      exact or_congr (ihφ hfo.1 κ fo ofo so so' (fun i hi => hc i (Or.inl hi)))
        (ihψ hfo.2 κ fo ofo so so' (fun i hi => hc i (Or.inr hi)))
  | exFO m φ ih =>
      intro hfo κ fo ofo so so' hc
      have hlen : es.length = v.length := H.length
      constructor
      · rintro ⟨p, hp, hsat⟩
        have hples : p < es.length := by rw [hlen]; exact hp
        have hsel : T.selected w es[p] := H.selected_getElem hples
        rcases hx : es[p] with ⟨i, q⟩ | r
        · -- the output position `p` is a copy of the input position `q`
          have hq : q < w.length := H.lt_length_of_getElem_inl hples hx
          refine Or.inl ?_
          rw [sat_bigOr]
          refine ⟨_, List.mem_map_of_mem (hlP i), ?_⟩
          refine ⟨q, hq, ?_, ?_⟩
          · rw [sat_selF hFO w _ _ _ so (fun i₀ hk => by
              rw [Function.update_self]; exact hq)]
            rw [Function.update_self]
            rw [hx] at hsel
            exact hsel
          · refine (ih hfo (Function.update κ m (Sum.inl i)) (Function.update fo m q)
              (Function.update ofo m p) so so' ?_).1 hsat
            intro i' hi'
            by_cases hm : i' = m
            · subst hm
              refine ⟨by rw [Function.update_self]; exact hples, ?_⟩
              simp only [Function.update_self]
              rw [hx]
              rfl
            · rw [Function.update_of_ne hm, Function.update_of_ne hm,
                Function.update_of_ne hm]
              exact hc i' ⟨hi', hm⟩
        · -- the output position `p` is an extra element
          refine Or.inr ?_
          rw [sat_bigOr]
          refine ⟨_, List.mem_map_of_mem (hlE r), ?_, ?_⟩
          · rw [sat_selF hFO w (Sum.inr r) m fo so (by rintro i₀ ⟨⟩)]
            rw [hx] at hsel
            exact hsel
          · refine (ih hfo (Function.update κ m (Sum.inr r)) fo
              (Function.update ofo m p) so so' ?_).1 hsat
            intro i' hi'
            by_cases hm : i' = m
            · subst hm
              refine ⟨by rw [Function.update_self]; exact hples, ?_⟩
              simp only [Function.update_self]
              rw [hx]
              rfl
            · rw [Function.update_of_ne hm, Function.update_of_ne hm]
              exact hc i' ⟨hi', hm⟩
      · rintro (h | h)
        · rw [sat_bigOr] at h
          obtain ⟨ψ, hψ, hsat⟩ := h
          rw [List.mem_map] at hψ
          obtain ⟨i, -, rfl⟩ := hψ
          obtain ⟨q, hq, hsel, hrest⟩ := hsat
          rw [sat_selF hFO w (Sum.inl i) m (Function.update fo m q) so
            (fun i₀ hk => by rw [Function.update_self]; exact hq)] at hsel
          rw [Function.update_self] at hsel
          obtain ⟨p, hples, hxp⟩ := H.exists_index hsel
          refine ⟨p, by rw [← hlen]; exact hples, ?_⟩
          refine (ih hfo (Function.update κ m (Sum.inl i)) (Function.update fo m q)
            (Function.update ofo m p) so so' ?_).2 hrest
          intro i' hi'
          by_cases hm : i' = m
          · subst hm
            refine ⟨by rw [Function.update_self]; exact hples, ?_⟩
            simp only [Function.update_self]
            rw [hxp]
          · rw [Function.update_of_ne hm, Function.update_of_ne hm, Function.update_of_ne hm]
            exact hc i' ⟨hi', hm⟩
        · rw [sat_bigOr] at h
          obtain ⟨ψ, hψ, hsat⟩ := h
          rw [List.mem_map] at hψ
          obtain ⟨r, -, rfl⟩ := hψ
          obtain ⟨hsel, hrest⟩ := hsat
          rw [sat_selF hFO w (Sum.inr r) m fo so (by rintro i₀ ⟨⟩)] at hsel
          obtain ⟨p, hples, hxp⟩ := H.exists_index hsel
          refine ⟨p, by rw [← hlen]; exact hples, ?_⟩
          refine (ih hfo (Function.update κ m (Sum.inr r)) fo
            (Function.update ofo m p) so so' ?_).2 hrest
          intro i' hi'
          by_cases hm : i' = m
          · subst hm
            refine ⟨by rw [Function.update_self]; exact hples, ?_⟩
            simp only [Function.update_self]
            rw [hxp]
          · rw [Function.update_of_ne hm, Function.update_of_ne hm]
            exact hc i' ⟨hi', hm⟩
  | exSO i φ _ => intro h; exact absurd h (by simp [IsFO])

end Correct

/-! ## Formulas evaluated at the first output position

The formulas of the extra elements of a transduction are evaluated under the
valuation that sends every variable to the position `0`.  When the transduction
is applied to the output `v` of `T`, this is the first element of `v` in the
order given by the order formulas of `T` -- if `v` is non-empty; and if `v` is
empty the truth value in question is a constant. -/

variable (T)

/-- "The element of kind `k` above `x_u` is selected and precedes every
selected element." -/
noncomputable def minF (lP : List T.P) (lE : List T.E) (k : Kind T) (u : ℕ) : MSO A :=
  MSO.and (selF T k u)
    (MSO.and
      (bigAnd (lP.map (fun i =>
        allF (u + 1) (impF (selF T (Sum.inl i) (u + 1)) (ordF T k u (Sum.inl i) (u + 1))))))
      (bigAnd (lE.map (fun r =>
        impF (selF T (Sum.inr r) (u + 1)) (ordF T k u (Sum.inr r) (u + 1))))))

/-- "No element is selected", i.e. the output string is empty. -/
noncomputable def noOutF (lP : List T.P) (lE : List T.E) : MSO A :=
  MSO.and (bigAnd (lP.map (fun i => allF 0 (MSO.not (selF T (Sum.inl i) 0)))))
    (bigAnd (lE.map (fun r => MSO.not (selF T (Sum.inr r) 0))))

open scoped Classical in
/-- The translation of a formula over the output alphabet that is evaluated
under the valuation sending every variable to the output position `0`. -/
noncomputable def trZ (lP : List T.P) (lE : List T.E) (ψ : MSO B) : MSO A :=
  MSO.or
    (MSO.or
      (bigOr (lP.map (fun i =>
        MSO.exFO 0 (MSO.and (minF T lP lE (Sum.inl i) 0)
          (atvF 0 (tr T lP lE (fun _ => Sum.inl i) ψ))))))
      (bigOr (lE.map (fun r =>
        MSO.and (minF T lP lE (Sum.inr r) 0) (tr T lP lE (fun _ => Sum.inr r) ψ)))))
    (MSO.and (noOutF T lP lE)
      (if Sat ([] : List B) (fun _ => 0) (fun _ => ∅) ψ then MSO.tt else MSO.ff))

variable {T}

lemma isFO_minF (hFO : T.AllFO) (lP : List T.P) (lE : List T.E) (k : Kind T) (u : ℕ) :
    (minF T lP lE k u).IsFO := by
  refine ⟨isFO_selF hFO _ _, isFO_bigAnd _ ?_, isFO_bigAnd _ ?_⟩
  · intro ψ hψ
    rw [List.mem_map] at hψ
    obtain ⟨i, -, rfl⟩ := hψ
    exact ⟨isFO_selF hFO _ _, isFO_ordF hFO _ _ _ _⟩
  · intro ψ hψ
    rw [List.mem_map] at hψ
    obtain ⟨r, -, rfl⟩ := hψ
    exact ⟨isFO_selF hFO _ _, isFO_ordF hFO _ _ _ _⟩

lemma isFO_noOutF (hFO : T.AllFO) (lP : List T.P) (lE : List T.E) :
    (noOutF T lP lE).IsFO := by
  refine ⟨isFO_bigAnd _ ?_, isFO_bigAnd _ ?_⟩
  · intro ψ hψ
    rw [List.mem_map] at hψ
    obtain ⟨i, -, rfl⟩ := hψ
    exact isFO_selF hFO _ _
  · intro ψ hψ
    rw [List.mem_map] at hψ
    obtain ⟨r, -, rfl⟩ := hψ
    exact isFO_selF hFO _ _

lemma isFO_trZ (hFO : T.AllFO) (lP : List T.P) (lE : List T.E) (ψ : MSO B) :
    (trZ T lP lE ψ).IsFO := by
  refine ⟨⟨isFO_bigOr _ ?_, isFO_bigOr _ ?_⟩, isFO_noOutF hFO _ _, ?_⟩
  · intro χ hχ
    rw [List.mem_map] at hχ
    obtain ⟨i, -, rfl⟩ := hχ
    exact ⟨isFO_minF hFO _ _ _ _, isFO_atvF _ (isFO_tr hFO lP lE ψ _)⟩
  · intro χ hχ
    rw [List.mem_map] at hχ
    obtain ⟨r, -, rfl⟩ := hχ
    exact ⟨isFO_minF hFO _ _ _ _, isFO_tr hFO lP lE ψ _⟩
  · by_cases hc : Sat ([] : List B) (fun _ => 0) (fun _ => ∅) ψ <;> simp [hc]

section Zero

variable {w : List A} {v : List B} {es : List T.Elt} {lP : List T.P} {lE : List T.E}

lemma sat_minF (hFO : T.AllFO) (hlP : ∀ i, i ∈ lP) (hlE : ∀ r, r ∈ lE) (k : Kind T) (u : ℕ)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (hu : ∀ i : T.P, k = Sum.inl i → fo u < w.length) :
    Sat w fo so (minF T lP lE k u) ↔
      (T.selected w (eltOf T k (fo u)) ∧
        ∀ y, T.selected w y → T.ordRel w (eltOf T k (fo u)) y) := by
  have hu' : ∀ (p : ℕ), ∀ i : T.P, k = Sum.inl i → Function.update fo (u + 1) p u < w.length :=
    fun p i hk => by rw [Function.update_of_ne (by omega)]; exact hu i hk
  constructor
  · rintro ⟨hsel, hPa, hEa⟩
    rw [sat_selF hFO w k u fo so hu] at hsel
    refine ⟨hsel, ?_⟩
    rintro (⟨i, p⟩ | r) hy
    · rw [sat_bigAnd] at hPa
      have hall := hPa _ (List.mem_map_of_mem (hlP i))
      rw [sat_allF] at hall
      have hp : p < w.length := hy.1
      have h2 := hall p hp
      have hupd : Function.update fo (u + 1) p (u + 1) = p := Function.update_self _ _ _
      rw [sat_impF, sat_selF hFO w (Sum.inl i) (u + 1) _ so
        (fun i₀ hk => by rw [hupd]; exact hp), hupd] at h2
      have h3 := h2 hy
      rw [sat_ordF hFO w k u (Sum.inl i) (u + 1) _ so (hu' p)
        (fun i₀ hk => by rw [hupd]; exact hp), hupd,
        Function.update_of_ne (show u ≠ u + 1 by omega)] at h3
      exact h3
    · rw [sat_bigAnd] at hEa
      have hall := hEa _ (List.mem_map_of_mem (hlE r))
      rw [sat_impF, sat_selF hFO w (Sum.inr r) (u + 1) fo so (by rintro i₀ ⟨⟩)] at hall
      have h3 := hall hy
      rw [sat_ordF hFO w k u (Sum.inr r) (u + 1) fo so hu (by rintro i₀ ⟨⟩)] at h3
      exact h3
  · rintro ⟨hsel, hmin⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [sat_selF hFO w k u fo so hu]; exact hsel
    · rw [sat_bigAnd]
      intro χ hχ
      rw [List.mem_map] at hχ
      obtain ⟨i, -, rfl⟩ := hχ
      rw [sat_allF]
      intro p hp
      have hupd : Function.update fo (u + 1) p (u + 1) = p := Function.update_self _ _ _
      rw [sat_impF, sat_selF hFO w (Sum.inl i) (u + 1) _ so
        (fun i₀ hk => by rw [hupd]; exact hp), hupd]
      intro hy
      rw [sat_ordF hFO w k u (Sum.inl i) (u + 1) _ so (hu' p)
        (fun i₀ hk => by rw [hupd]; exact hp), hupd,
        Function.update_of_ne (show u ≠ u + 1 by omega)]
      exact hmin _ hy
    · rw [sat_bigAnd]
      intro χ hχ
      rw [List.mem_map] at hχ
      obtain ⟨r, -, rfl⟩ := hχ
      rw [sat_impF, sat_selF hFO w (Sum.inr r) (u + 1) fo so (by rintro i₀ ⟨⟩)]
      intro hy
      rw [sat_ordF hFO w k u (Sum.inr r) (u + 1) fo so hu (by rintro i₀ ⟨⟩)]
      exact hmin _ hy

lemma sat_noOutF (hFO : T.AllFO) (hlP : ∀ i, i ∈ lP) (hlE : ∀ r, r ∈ lE) (fo : ℕ → ℕ)
    (so : ℕ → Set ℕ) :
    Sat w fo so (noOutF T lP lE) ↔ ∀ x, ¬ T.selected w x := by
  constructor
  · rintro ⟨hPa, hEa⟩ (⟨i, p⟩ | r) hx
    · rw [sat_bigAnd] at hPa
      have hall := hPa _ (List.mem_map_of_mem (hlP i))
      rw [sat_allF] at hall
      have hp : p < w.length := hx.1
      have h2 := hall p hp
      have hupd : Function.update fo 0 p 0 = p := Function.update_self _ _ _
      have h2' : ¬ Sat w (Function.update fo 0 p) so (selF T (Sum.inl i) 0) := h2
      rw [sat_selF hFO w (Sum.inl i) 0 _ so (fun i₀ hk => by rw [hupd]; exact hp),
        hupd] at h2'
      exact h2' hx
    · rw [sat_bigAnd] at hEa
      have hall := hEa _ (List.mem_map_of_mem (hlE r))
      have hall' : ¬ Sat w fo so (selF T (Sum.inr r) 0) := hall
      rw [sat_selF hFO w (Sum.inr r) 0 fo so (by rintro i₀ ⟨⟩)] at hall'
      exact hall' hx
  · intro h
    refine ⟨?_, ?_⟩
    · rw [sat_bigAnd]
      intro χ hχ
      rw [List.mem_map] at hχ
      obtain ⟨i, -, rfl⟩ := hχ
      rw [sat_allF]
      intro p hp
      have hupd : Function.update fo 0 p 0 = p := Function.update_self _ _ _
      show ¬ Sat w (Function.update fo 0 p) so (selF T (Sum.inl i) 0)
      rw [sat_selF hFO w (Sum.inl i) 0 _ so (fun i₀ hk => by rw [hupd]; exact hp), hupd]
      exact h _
    · rw [sat_bigAnd]
      intro χ hχ
      rw [List.mem_map] at hχ
      obtain ⟨r, -, rfl⟩ := hχ
      show ¬ Sat w fo so (selF T (Sum.inr r) 0)
      rw [sat_selF hFO w (Sum.inr r) 0 fo so (by rintro i₀ ⟨⟩)]
      exact h _

theorem sat_trZ (hFO : T.AllFO) (hP : T.Proper) (H : ITrans.Enum T w v es)
    (hlP : ∀ i, i ∈ lP) (hlE : ∀ r, r ∈ lE) (ψ : MSO B) (hψ : ψ.IsFO) (fo : ℕ → ℕ)
    (so : ℕ → Set ℕ) (so' : ℕ → Set ℕ) :
    Sat w fo so (trZ T lP lE ψ) ↔ Sat v (fun _ => 0) so' ψ := by
  rcases Nat.eq_zero_or_pos es.length with h0 | h0
  · have hnone : ∀ x, ¬ T.selected w x := by
      intro x hx
      obtain ⟨q, hq, -⟩ := H.exists_index hx
      omega
    have hvnil : v = [] := H.v_eq_nil_of_no_selected hnone
    subst hvnil
    constructor
    · rintro ((h | h) | ⟨-, hc⟩)
      · rw [sat_bigOr] at h
        obtain ⟨χ, hχ, hsat⟩ := h
        rw [List.mem_map] at hχ
        obtain ⟨i, -, rfl⟩ := hχ
        obtain ⟨q, hq, hmin, -⟩ := hsat
        rw [sat_minF hFO hlP hlE (Sum.inl i) 0 _ so
          (fun i₀ hk => by rw [Function.update_self]; exact hq)] at hmin
        exact absurd hmin.1 (hnone _)
      · rw [sat_bigOr] at h
        obtain ⟨χ, hχ, hsat⟩ := h
        rw [List.mem_map] at hχ
        obtain ⟨r, -, rfl⟩ := hχ
        obtain ⟨hmin, -⟩ := hsat
        rw [sat_minF hFO hlP hlE (Sum.inr r) 0 fo so (by rintro i₀ ⟨⟩)] at hmin
        exact absurd hmin.1 (hnone _)
      · by_cases hcc : Sat ([] : List B) (fun _ => 0) (fun _ => ∅) ψ
        · refine (MSO.sat_congr [] ψ _ _ _ _ (fun i _ => rfl) (fun j hj => ?_)).1 hcc
          rw [freeSO_eq_empty_of_isFO ψ hψ] at hj
          exact absurd hj (Set.notMem_empty _)
        · rw [if_neg hcc] at hc
          exact absurd (le_refl (fo 0)) hc
    · intro h
      refine Or.inr ⟨(sat_noOutF hFO hlP hlE fo so).2 hnone, ?_⟩
      have hc : Sat ([] : List B) (fun _ => 0) (fun _ => ∅) ψ := by
        refine (MSO.sat_congr [] ψ _ _ _ _ (fun i _ => rfl) (fun j hj => ?_)).1 h
        rw [freeSO_eq_empty_of_isFO ψ hψ] at hj
        exact absurd hj (Set.notMem_empty _)
      rw [if_pos hc]
      exact le_refl _
  · have hsel0 : T.selected w es[0] := H.selected_getElem h0
    have hmin0 : ∀ y, T.selected w y → T.ordRel w es[0] y := fun y hy => H.min_zero hP hy h0
    have hnotnone : ¬ ∀ x, ¬ T.selected w x := fun h => h _ hsel0
    constructor
    · rintro ((h | h) | ⟨hno, -⟩)
      · rw [sat_bigOr] at h
        obtain ⟨χ, hχ, hsat⟩ := h
        rw [List.mem_map] at hχ
        obtain ⟨i, -, rfl⟩ := hχ
        obtain ⟨q, hq, hmin, hrest⟩ := hsat
        have hupd : Function.update fo 0 q 0 = q := Function.update_self _ _ _
        rw [sat_minF hFO hlP hlE (Sum.inl i) 0 _ so
          (fun i₀ hk => by rw [hupd]; exact hq), hupd] at hmin
        have hx0 : eltOf T (Sum.inl i) q = es[0] := H.eq_zero_of_min hP hmin.1 hmin.2 h0
        rw [sat_atvF w 0 (isFO_tr hFO lP lE ψ _) _ so (by rw [hupd]; exact hq), hupd] at hrest
        refine (sat_tr hFO hP H hlP hlE ψ hψ (fun _ => Sum.inl i) (fun _ => q) (fun _ => 0)
          (fun _ => ∅) so' ?_).2 hrest
        intro i' _
        exact ⟨h0, hx0.symm⟩
      · rw [sat_bigOr] at h
        obtain ⟨χ, hχ, hsat⟩ := h
        rw [List.mem_map] at hχ
        obtain ⟨r, -, rfl⟩ := hχ
        obtain ⟨hmin, hrest⟩ := hsat
        rw [sat_minF hFO hlP hlE (Sum.inr r) 0 fo so (by rintro i₀ ⟨⟩)] at hmin
        have hx0 : eltOf T (Sum.inr r) (fo 0) = es[0] := H.eq_zero_of_min hP hmin.1 hmin.2 h0
        refine (sat_tr hFO hP H hlP hlE ψ hψ (fun _ => Sum.inr r) fo (fun _ => 0)
          so so' ?_).2 hrest
        intro i' _
        exact ⟨h0, hx0.symm⟩
      · exact absurd ((sat_noOutF hFO hlP hlE fo so).1 hno) hnotnone
    · intro h
      rcases hx : es[0] with ⟨i, q⟩ | r
      · have hq : q < w.length := H.lt_length_of_getElem_inl h0 hx
        refine Or.inl (Or.inl ?_)
        rw [sat_bigOr]
        refine ⟨_, List.mem_map_of_mem (hlP i), q, hq, ?_, ?_⟩
        · have hupd : Function.update fo 0 q 0 = q := Function.update_self _ _ _
          rw [sat_minF hFO hlP hlE (Sum.inl i) 0 _ so (fun i₀ hk => by rw [hupd]; exact hq),
            hupd]
          constructor
          · show T.selected w (Sum.inl (i, q))
            rw [← hx]; exact hsel0
          · intro y hy
            show T.ordRel w (Sum.inl (i, q)) y
            rw [← hx]; exact hmin0 y hy
        · have hupd : Function.update fo 0 q 0 = q := Function.update_self _ _ _
          rw [sat_atvF w 0 (isFO_tr hFO lP lE ψ _) _ so (by rw [hupd]; exact hq), hupd]
          refine (sat_tr hFO hP H hlP hlE ψ hψ (fun _ => Sum.inl i) (fun _ => q) (fun _ => 0)
            (fun _ => ∅) so' ?_).1 h
          intro i' _
          exact ⟨h0, by rw [hx]; rfl⟩
      · refine Or.inl (Or.inr ?_)
        rw [sat_bigOr]
        refine ⟨_, List.mem_map_of_mem (hlE r), ?_, ?_⟩
        · rw [sat_minF hFO hlP hlE (Sum.inr r) 0 fo so (by rintro i₀ ⟨⟩)]
          constructor
          · show T.selected w (Sum.inr r)
            rw [← hx]; exact hsel0
          · intro y hy
            show T.ordRel w (Sum.inr r) y
            rw [← hx]; exact hmin0 y hy
        · refine (sat_tr hFO hP H hlP hlE ψ hψ (fun _ => Sum.inr r) fo (fun _ => 0)
            so so' ?_).1 h
          intro i' _
          exact ⟨h0, by rw [hx]; rfl⟩

end Zero

end FOTr
end Lax314295Proofs.Transducers

