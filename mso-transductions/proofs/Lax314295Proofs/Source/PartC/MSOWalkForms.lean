/- The mso formulas that the walking transducer of the hard half of Theorem
`thm:logic-regular-functions` asks about.

For a normalised mso transduction (`NormT`, see
`RequestProject/PartC/MSONorm.lean`) the walking transducer needs to know, of a
position and a tag, whether the corresponding element is the first or the last
element of the output order, and where the successor of that element sits.  All
these questions are expressed by mso formulas with one or two free first-order
variables, built here from the universe and order formulas of the transduction;
their meaning is expressed in terms of the sorted enumeration of the selected
elements, through the dictionary of `RequestProject/PartC/SortedEnum.lean`.
-/
import Lax314295Proofs.Source.PartC.MSONorm
import Lax314295Proofs.Source.PartC.SortedEnum
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

namespace MSO

variable {A : Type} {w : List A} {fo : ℕ → ℕ} {so : ℕ → Set ℕ}

/-! ## Elementary connectives -/

/-- The always true formula. -/
def ttF (A : Type) : MSO A := le 0 0

/-- The always false formula. -/
def ffF (A : Type) : MSO A := not (le 0 0)

@[simp] lemma sat_ttF : Sat w fo so (ttF A) := le_refl _

@[simp] lemma sat_ffF : ¬ Sat w fo so (ffF A) := by
  simp only [ffF, Sat, not_not]
  exact le_refl _

/-- Implication. -/
def imp (φ ψ : MSO A) : MSO A := or (not φ) ψ

lemma sat_imp (φ ψ : MSO A) :
    Sat w fo so (imp φ ψ) ↔ (Sat w fo so φ → Sat w fo so ψ) := by
  simp only [imp, Sat]
  tauto

/-- Universal quantification over the positions. -/
def exAll (v : ℕ) (φ : MSO A) : MSO A := not (exFO v (not φ))

lemma sat_exAll (v : ℕ) (φ : MSO A) :
    Sat w fo so (exAll v φ) ↔ ∀ p < w.length, Sat w (Function.update fo v p) so φ := by
  simp only [exAll, Sat, not_exists, not_and, not_not]

/-- A finite conjunction. -/
def bigAndF {ι : Type} (L : List ι) (g : ι → MSO A) : MSO A :=
  L.foldr (fun t φ => and (g t) φ) (ttF A)

lemma sat_bigAndF {ι : Type} (L : List ι) (g : ι → MSO A) :
    Sat w fo so (bigAndF L g) ↔ ∀ t ∈ L, Sat w fo so (g t) := by
  induction L with
  | nil => simp [bigAndF]
  | cons a L ih =>
      simp only [bigAndF, List.foldr_cons, Sat, List.mem_cons, forall_eq_or_imp]
      rw [show L.foldr (fun t φ => and (g t) φ) (ttF A) = bigAndF L g from rfl, ih]

/-- A finite disjunction. -/
def bigOrF {ι : Type} (L : List ι) (g : ι → MSO A) : MSO A :=
  L.foldr (fun t φ => or (g t) φ) (ffF A)

lemma sat_bigOrF {ι : Type} (L : List ι) (g : ι → MSO A) :
    Sat w fo so (bigOrF L g) ↔ ∃ t ∈ L, Sat w fo so (g t) := by
  induction L with
  | nil => simp [bigOrF]
  | cons a L ih =>
      simp only [bigOrF, List.foldr_cons, Sat, List.mem_cons, exists_eq_or_imp]
      rw [show L.foldr (fun t φ => or (g t) φ) (ffF A) = bigOrF L g from rfl, ih]

end MSO

/-! ## The questions of the walking transducer -/

namespace NormT

open MSO

variable {A B : Type} (N : NormT A B)

/-- "The element with tag `t` in the position `x_a` is selected." -/
def selAt (a : ℕ) (t : N.Tag) : MSO A := MSO.atv a (N.U t)

/-- "The element with tag `t` in the position `x_a` is before the element with
tag `t'` in the position `x_b`." -/
def ordAt (a b : ℕ) (t t' : N.Tag) : MSO A := MSO.atv2 a b (N.Ord t t')

variable {N}
variable {w : List A} {fo : ℕ → ℕ} {so : ℕ → Set ℕ}

lemma sat_selAt {a : ℕ} (t : N.Tag) (ha : fo a < w.length) :
    MSO.Sat w fo so (N.selAt a t) ↔ N.sel w (t, fo a) := by
  rw [selAt, MSO.sat_atv w a _ _ _ ha]
  exact ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩

lemma sat_ordAt {a b : ℕ} (t t' : N.Tag) (ha : fo a < w.length) (hb : fo b < w.length) :
    MSO.Sat w fo so (N.ordAt a b t t') ↔ N.ord w (t, fo a) (t', fo b) := by
  rw [ordAt, MSO.sat_atv2 w a b _ _ _ ha hb]
  rfl

variable (N)

/-- "The element with tag `t` in the position `x₀` is the first element of the
output order." -/
def isMinF (L : List N.Tag) (t : N.Tag) : MSO A :=
  MSO.and (N.selAt 0 t)
    (exAll 1 (bigAndF L (fun t' => imp (N.selAt 1 t') (N.ordAt 0 1 t t'))))

/-- "The element with tag `t` in the position `x₀` is the last element of the
output order." -/
def isMaxF (L : List N.Tag) (t : N.Tag) : MSO A :=
  MSO.and (N.selAt 0 t)
    (exAll 1 (bigAndF L (fun t' => imp (N.selAt 1 t') (N.ordAt 1 0 t' t))))

/-- "The element with tag `t'` in the position `x₁` is the successor, in the
output order, of the element with tag `t` in the position `x₀`." -/
def isSuccF (L : List N.Tag) (t t' : N.Tag) : MSO A :=
  MSO.and (N.selAt 0 t)
    (MSO.and (N.selAt 1 t')
      (MSO.and (MSO.not (N.ordAt 1 0 t' t))
        (exAll 2 (bigAndF L (fun t'' =>
          MSO.not (MSO.and (N.selAt 2 t'')
            (MSO.and (MSO.not (N.ordAt 2 0 t'' t)) (MSO.not (N.ordAt 1 2 t' t'')))))))))

/-- "The element with tag `t'` in the position `x₀` is the successor, in the
output order, of the element with tag `t` in the position `x₁`."  This is
`isSuccF` with the two free variables exchanged. -/
def isSuccSwapF (L : List N.Tag) (t t' : N.Tag) : MSO A :=
  MSO.rename (Equiv.swap 0 1) (N.isSuccF L t t')

/-- "The successor of the element with tag `t` in the position `x₀` sits in the
same position and has the tag `t'`." -/
def succHF (L : List N.Tag) (t t' : N.Tag) : MSO A := MSO.atv 0 (N.isSuccF L t t')

/-- "The successor of the element with tag `t` in the position `x₀` sits in a
position further to the right." -/
def succRF (L : List N.Tag) (t : N.Tag) : MSO A :=
  MSO.exFO 1 (MSO.and (bigOrF L (fun t' => N.isSuccF L t t')) (MSO.not (MSO.le 1 0)))

/-! ## The meaning of the questions -/

section Spec

variable {N}
variable {es : List N.Elt} {v : List B} {L : List N.Tag}
  (hL : ∀ t, t ∈ L) (hProp : N.Proper w) (hPres : N.Presents w es v)

include hProp hPres

omit hProp in
lemma mem_es_iff (x : N.Elt) : x ∈ es ↔ N.sel w x := hPres.2.1 x

omit hProp in
lemma pos_lt_of_mem {x : N.Elt} (hx : x ∈ es) : x.2 < w.length := ((hPres.2.1 x).1 hx).1

/-- The sorted enumeration of the selected elements. -/
lemma spec_es : SortedEnum.Spec (N.ord w) es := by
  obtain ⟨hnodup, hmem, hsorted, -, -⟩ := hPres
  obtain ⟨-, hrefl, hanti, htot⟩ := hProp
  exact
    { nodup := hnodup
      sorted := hsorted
      refl := fun x hx => hrefl x ((hmem x).1 hx)
      antisymm := fun x hx y hy => hanti x y ((hmem x).1 hx) ((hmem y).1 hy)
      total := fun x hx y hy => htot x y ((hmem x).1 hx) ((hmem y).1 hy) }

include hL

lemma sat_isSuccF (t t' : N.Tag) (h0 : fo 0 < w.length) (h1 : fo 1 < w.length) :
    MSO.Sat w fo so (N.isSuccF L t t') ↔
      ∃ r, es[r]? = some (t, fo 0) ∧ es[r + 1]? = some (t', fo 1) := by
  have hspec := spec_es hProp hPres
  have key : MSO.Sat w fo so (N.isSuccF L t t') ↔
      ((t, fo 0) ∈ es ∧ (t', fo 1) ∈ es ∧ ¬ N.ord w (t', fo 1) (t, fo 0) ∧
        ∀ z ∈ es, ¬ (¬ N.ord w z (t, fo 0) ∧ ¬ N.ord w (t', fo 1) z)) := by
    simp only [isSuccF, MSO.Sat, sat_exAll, sat_bigAndF, sat_selAt _ h0, sat_selAt _ h1,
      sat_ordAt _ _ h1 h0]
    rw [mem_es_iff hPres, mem_es_iff hPres]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ => ?_)))
    constructor
    · rintro h ⟨t'', z⟩ hz
      have hzlt : z < w.length := pos_lt_of_mem hPres hz
      have := h z hzlt t'' (hL t'')
      rw [sat_selAt (fo := Function.update fo 2 z) t''
          (by rw [Function.update_self]; exact hzlt)] at this
      rw [sat_ordAt (fo := Function.update fo 2 z) t'' t
          (by rw [Function.update_self]; exact hzlt)
          (by rw [Function.update_of_ne (by omega)]; exact h0)] at this
      rw [sat_ordAt (fo := Function.update fo 2 z) t' t''
          (by rw [Function.update_of_ne (by omega)]; exact h1)
          (by rw [Function.update_self]; exact hzlt)] at this
      simp only [Function.update_self] at this
      rintro ⟨hz1, hz2⟩
      exact this ⟨(mem_es_iff hPres _).1 hz, hz1, hz2⟩
    · intro h z hz t'' _
      rw [sat_selAt (fo := Function.update fo 2 z) t''
          (by rw [Function.update_self]; exact hz)]
      rw [sat_ordAt (fo := Function.update fo 2 z) t'' t
          (by rw [Function.update_self]; exact hz)
          (by rw [Function.update_of_ne (by omega)]; exact h0)]
      rw [sat_ordAt (fo := Function.update fo 2 z) t' t''
          (by rw [Function.update_of_ne (by omega)]; exact h1)
          (by rw [Function.update_self]; exact hz)]
      simp only [Function.update_self]
      rintro ⟨hsel, hz1, hz2⟩
      exact h (t'', z) ((mem_es_iff hPres _).2 hsel) ⟨hz1, hz2⟩
  rw [key]
  constructor
  · rintro ⟨hx, hy, h1', h2'⟩
    obtain ⟨r, hr, hres⟩ := SortedEnum.mem_index hx
    obtain ⟨s, hs, hses⟩ := SortedEnum.mem_index hy
    have : s = r + 1 := by
      rw [← SortedEnum.succ_iff hspec hr hs]
      refine ⟨?_, ?_⟩
      · rw [hres, hses]; exact h1'
      · intro z hz
        rw [hres, hses]
        exact h2' z hz
    refine ⟨r, ?_, ?_⟩
    · rw [List.getElem?_eq_getElem hr, hres]
    · rw [← this, List.getElem?_eq_getElem hs, hses]
  · rintro ⟨r, hr0, hr1⟩
    obtain ⟨hr, hres⟩ := List.getElem?_eq_some_iff.1 hr0
    obtain ⟨hs, hses⟩ := List.getElem?_eq_some_iff.1 hr1
    have hsucc := (SortedEnum.succ_iff hspec hr hs).2 rfl
    rw [hres, hses] at hsucc
    exact ⟨hres ▸ List.getElem_mem hr, hses ▸ List.getElem_mem hs, hsucc.1, hsucc.2⟩

lemma sat_isMinF (t : N.Tag) (h0 : fo 0 < w.length) :
    MSO.Sat w fo so (N.isMinF L t) ↔ es[0]? = some (t, fo 0) := by
  have hspec := spec_es hProp hPres
  have key : MSO.Sat w fo so (N.isMinF L t) ↔
      ((t, fo 0) ∈ es ∧ ∀ z ∈ es, N.ord w (t, fo 0) z) := by
    simp only [isMinF, MSO.Sat, sat_exAll, sat_bigAndF, sat_imp, sat_selAt _ h0]
    rw [mem_es_iff hPres]
    refine and_congr_right (fun _ => ?_)
    constructor
    · rintro h ⟨t'', z⟩ hz
      have hzlt : z < w.length := pos_lt_of_mem hPres hz
      have := h z hzlt t'' (hL t'')
      rw [sat_selAt (fo := Function.update fo 1 z) t''
          (by rw [Function.update_self]; exact hzlt),
        sat_ordAt (fo := Function.update fo 1 z) t t''
          (by rw [Function.update_of_ne (by omega)]; exact h0)
          (by rw [Function.update_self]; exact hzlt)] at this
      simp only [Function.update_self] at this
      exact this ((mem_es_iff hPres _).1 hz)
    · intro h z hz t'' _
      rw [sat_selAt (fo := Function.update fo 1 z) t''
          (by rw [Function.update_self]; exact hz),
        sat_ordAt (fo := Function.update fo 1 z) t t''
          (by rw [Function.update_of_ne (by omega)]; exact h0)
          (by rw [Function.update_self]; exact hz)]
      simp only [Function.update_self]
      intro hsel
      exact h (t'', z) ((mem_es_iff hPres _).2 hsel)
  rw [key]
  constructor
  · rintro ⟨hx, hmin⟩
    obtain ⟨r, hr, hres⟩ := SortedEnum.mem_index hx
    have hr0 : r = 0 := by
      rw [← SortedEnum.isMin_iff hspec hr]
      intro z hz
      rw [hres]
      exact hmin z hz
    subst hr0
    rw [List.getElem?_eq_getElem hr, hres]
  · intro h
    obtain ⟨hr, hres⟩ := List.getElem?_eq_some_iff.1 h
    refine ⟨hres ▸ List.getElem_mem hr, ?_⟩
    have := (SortedEnum.isMin_iff hspec hr).2 rfl
    rw [hres] at this
    exact this

lemma sat_isMaxF (t : N.Tag) (h0 : fo 0 < w.length) :
    MSO.Sat w fo so (N.isMaxF L t) ↔
      ∃ r, es[r]? = some (t, fo 0) ∧ r + 1 = es.length := by
  have hspec := spec_es hProp hPres
  have key : MSO.Sat w fo so (N.isMaxF L t) ↔
      ((t, fo 0) ∈ es ∧ ∀ z ∈ es, N.ord w z (t, fo 0)) := by
    simp only [isMaxF, MSO.Sat, sat_exAll, sat_bigAndF, sat_imp, sat_selAt _ h0]
    rw [mem_es_iff hPres]
    refine and_congr_right (fun _ => ?_)
    constructor
    · rintro h ⟨t'', z⟩ hz
      have hzlt : z < w.length := pos_lt_of_mem hPres hz
      have := h z hzlt t'' (hL t'')
      rw [sat_selAt (fo := Function.update fo 1 z) t''
          (by rw [Function.update_self]; exact hzlt),
        sat_ordAt (fo := Function.update fo 1 z) t'' t
          (by rw [Function.update_self]; exact hzlt)
          (by rw [Function.update_of_ne (by omega)]; exact h0)] at this
      simp only [Function.update_self] at this
      exact this ((mem_es_iff hPres _).1 hz)
    · intro h z hz t'' _
      rw [sat_selAt (fo := Function.update fo 1 z) t''
          (by rw [Function.update_self]; exact hz),
        sat_ordAt (fo := Function.update fo 1 z) t'' t
          (by rw [Function.update_self]; exact hz)
          (by rw [Function.update_of_ne (by omega)]; exact h0)]
      simp only [Function.update_self]
      intro hsel
      exact h (t'', z) ((mem_es_iff hPres _).2 hsel)
  rw [key]
  constructor
  · rintro ⟨hx, hmax⟩
    obtain ⟨r, hr, hres⟩ := SortedEnum.mem_index hx
    refine ⟨r, by rw [List.getElem?_eq_getElem hr, hres], ?_⟩
    rw [← SortedEnum.isMax_iff hspec hr]
    intro z hz
    rw [hres]
    exact hmax z hz
  · rintro ⟨r, hr0, hlast⟩
    obtain ⟨hr, hres⟩ := List.getElem?_eq_some_iff.1 hr0
    refine ⟨hres ▸ List.getElem_mem hr, ?_⟩
    have := (SortedEnum.isMax_iff hspec hr).2 hlast
    rw [hres] at this
    exact this

lemma sat_isSuccSwapF (t t' : N.Tag) (h0 : fo 0 < w.length) (h1 : fo 1 < w.length) :
    MSO.Sat w fo so (N.isSuccSwapF L t t') ↔
      ∃ r, es[r]? = some (t, fo 1) ∧ es[r + 1]? = some (t', fo 0) := by
  rw [isSuccSwapF, MSO.sat_rename (Equiv.injective _) w]
  have e0 : (fo ∘ (Equiv.swap (0 : ℕ) 1)) 0 = fo 1 := by simp [Equiv.swap_apply_left]
  have e1 : (fo ∘ (Equiv.swap (0 : ℕ) 1)) 1 = fo 0 := by simp [Equiv.swap_apply_right]
  rw [sat_isSuccF hL hProp hPres t t' (by rw [e0]; exact h1) (by rw [e1]; exact h0), e0, e1]

lemma sat_succHF (t t' : N.Tag) (h0 : fo 0 < w.length) :
    MSO.Sat w fo so (N.succHF L t t') ↔
      ∃ r, es[r]? = some (t, fo 0) ∧ es[r + 1]? = some (t', fo 0) := by
  rw [succHF, MSO.sat_atv w 0 _ _ _ h0]
  exact sat_isSuccF hL hProp hPres t t' h0 h0

lemma sat_succRF (t : N.Tag) (h0 : fo 0 < w.length) :
    MSO.Sat w fo so (N.succRF L t) ↔
      ∃ (r q : ℕ) (t' : N.Tag), es[r]? = some (t, fo 0) ∧ es[r + 1]? = some (t', q) ∧
        fo 0 < q := by
  simp only [succRF, MSO.Sat, sat_bigOrF]
  constructor
  · rintro ⟨q, hq, ⟨t', -, hsat⟩, hlt⟩
    rw [sat_isSuccF hL hProp hPres t t'
      (by rw [Function.update_of_ne (by omega)]; exact h0) (by rw [Function.update_self]; exact hq)]
      at hsat
    rw [Function.update_of_ne (show (0:ℕ) ≠ 1 by omega)] at hsat
    rw [Function.update_self, Function.update_of_ne (show (0:ℕ) ≠ 1 by omega)] at hlt
    obtain ⟨r, hr0, hr1⟩ := hsat
    exact ⟨r, q, t', hr0, hr1, by omega⟩
  · rintro ⟨r, q, t', hr0, hr1, hlt⟩
    have hq : q < w.length := by
      have : (t', q) ∈ es := by
        obtain ⟨h, he⟩ := List.getElem?_eq_some_iff.1 hr1
        exact he ▸ List.getElem_mem h
      exact pos_lt_of_mem hPres this
    refine ⟨q, hq, ⟨t', hL t', ?_⟩, ?_⟩
    · rw [sat_isSuccF hL hProp hPres t t'
        (by rw [Function.update_of_ne (by omega)]; exact h0)
        (by rw [Function.update_self]; exact hq)]
      rw [Function.update_of_ne (show (0:ℕ) ≠ 1 by omega), Function.update_self]
      exact ⟨r, hr0, hr1⟩
    · rw [Function.update_self, Function.update_of_ne (show (0:ℕ) ≠ 1 by omega)]
      omega

end Spec

end NormT

end Lax314295Proofs.Transducers
