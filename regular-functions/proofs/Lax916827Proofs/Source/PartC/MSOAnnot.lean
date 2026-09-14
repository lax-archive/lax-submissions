/- Lemma `lem:mso-free-variables` of *Transducers* (M. Bojańczyk): for a monadic second-order
formula whose free variables are among `x₁, …, x_k, X₁, …, X_l`, the set of annotated strings that
satisfy it is a regular language over the alphabet `A × 2^{k+l}`.

The proof is the translation of a formula into an automaton, by induction on the
syntax of the formula.  An annotated string over `A × 2^{k+l}` is *valid* if
every first-order variable marks exactly one position; a valid annotated string
carries a string `w` (its first components) together with a valuation of the
variables (`foOf`, `soOf`), so that the language

  `AnnLang A k l φ = {u | u is valid and w, foOf u, soOf u satisfy φ}`

is the language of Lemma `lem:mso-free-variables` (see `annLang_eq`).  The atomic formulas
give languages recognised by the scanning automata of `RequestProject/PartC/RegAut.lean`; negation,
conjunction and disjunction use the Boolean closure properties; and a quantifier is a projection,
i.e. the image of a language under a letter-to-letter map, which is where nondeterminism enters.

For a quantifier `∃ x_i` the variable `i` need not be one of `0, …, k-1`, so the
induction hypothesis is applied with `k' = max k (i+1)` variables: the annotated
strings over `A × 2^{k'+l}` mark, besides the `k` variables of the conclusion,
the quantified variable `i` and (harmlessly) the variables between `k` and `k'`.
The projection forgets the variable `i`, which is what the existential
quantifier does.
-/
import Lax916827Proofs.Source.PartC.MSOSyntax
import Lax916827Proofs.Source.PartC.RegAut
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

open RegAut

namespace MSOAnnot

variable {A : Type}

/-! ## Annotated strings -/

/-- The alphabet of strings annotated by the values of `k` first-order and `l`
second-order variables. -/
abbrev Ann (A : Type) (k l : ℕ) : Type := A × (Fin k → Bool) × (Fin l → Bool)

/-- The positions marked by the first-order variable `i`. -/
def foBit {k l : ℕ} (i : Fin k) : Ann A k l → Bool := fun x => x.2.1 i

/-- The positions belonging to the second-order variable `j`. -/
def soBit {k l : ℕ} (j : Fin l) : Ann A k l → Bool := fun x => x.2.2 j

/-- The valuation of the first-order variables encoded by an annotated string:
the variable `m` is sent to the first position marked by it. -/
def foOf {k l : ℕ} (u : List (Ann A k l)) : ℕ → ℕ :=
  fun m => if h : m < k then u.findIdx (foBit (A := A) (l := l) ⟨m, h⟩) else 0

/-- The valuation of the second-order variables encoded by an annotated
string. -/
def soOf {k l : ℕ} (u : List (Ann A k l)) : ℕ → Set ℕ :=
  fun m => if h : m < l then {p | MarkedAt (soBit (A := A) (k := k) ⟨m, h⟩) u p} else ∅

/-- An annotated string is valid if every first-order variable marks exactly one
position. -/
def Valid {k l : ℕ} (u : List (Ann A k l)) : Prop :=
  ∀ i : Fin k, MarksOnce (foBit (A := A) (l := l) i) u

/-- The language of valid annotated strings that satisfy `φ`. -/
def AnnLang (A : Type) (k l : ℕ) (φ : MSO A) : Language (Ann A k l) :=
  {u | Valid u ∧ MSO.Sat (u.map Prod.fst) (foOf u) (soOf u) φ}

variable {k l : ℕ}

lemma foOf_of_lt (u : List (Ann A k l)) {m : ℕ} (h : m < k) :
    foOf u m = u.findIdx (foBit (A := A) (l := l) ⟨m, h⟩) := dif_pos h

lemma foOf_of_not_lt (u : List (Ann A k l)) {m : ℕ} (h : ¬ m < k) : foOf u m = 0 := dif_neg h

lemma soOf_of_lt (u : List (Ann A k l)) {m : ℕ} (h : m < l) :
    soOf u m = {p | MarkedAt (soBit (A := A) (k := k) ⟨m, h⟩) u p} := dif_pos h

lemma soOf_of_not_lt (u : List (Ann A k l)) {m : ℕ} (h : ¬ m < l) : soOf u m = ∅ := dif_neg h

lemma marked_iff_eq_foOf {u : List (Ann A k l)} (hv : Valid u) {m : ℕ} (hm : m < k) (q : ℕ) :
    MarkedAt (foBit (A := A) (l := l) ⟨m, hm⟩) u q ↔ q = foOf u m := by
  obtain ⟨p, hp⟩ := hv ⟨m, hm⟩
  have hfind : u.findIdx (foBit (A := A) (l := l) ⟨m, hm⟩) = p := findIdx_eq_of_marksOnce hp
  rw [foOf_of_lt u hm, hfind]
  exact hp q

lemma foOf_lt_length {u : List (Ann A k l)} (hv : Valid u) {m : ℕ} (hm : m < k) :
    foOf u m < u.length := by
  obtain ⟨p, hp⟩ := hv ⟨m, hm⟩
  have hfind : u.findIdx (foBit (A := A) (l := l) ⟨m, hm⟩) = p := findIdx_eq_of_marksOnce hp
  rw [foOf_of_lt u hm, hfind]
  exact marksOnce_lt_length hp

lemma soOf_subset_length (u : List (Ann A k l)) (m : ℕ) : soOf u m ⊆ {p | p < u.length} := by
  by_cases h : m < l
  · rw [soOf_of_lt u h]
    rintro p ⟨x, hx, -⟩
    rw [List.getElem?_eq_some_iff] at hx
    exact hx.1
  · rw [soOf_of_not_lt u h]
    simp

/-- The language of valid annotated strings is regular. -/
lemma isRegular_valid (A : Type) (k l : ℕ) :
    Language.IsRegular {u : List (Ann A k l) | Valid u} := by
  have h := isRegular_forall_list
    (fun i : Fin k => {u : List (Ann A k l) | MarksOnce (foBit (A := A) (l := l) i) u})
    (List.finRange k) (fun i _ => isRegular_marksOnce _)
  convert h using 1
  ext u
  simp only [List.mem_finRange, Valid]
  constructor
  · intro hu i _; exact hu i
  · intro hu i; exact hu i (by simp)

/-! ## The induction on the formula -/

open scoped Classical in
/-- **Lemma `lem:mso-free-variables`**, in terms of the language `AnnLang`: the valid
annotated strings satisfying `φ` form a regular language. -/
theorem isRegular_annLang (φ : MSO A) : ∀ (k l : ℕ),
    φ.freeFO ⊆ {i | i < k} → φ.freeSO ⊆ {j | j < l} →
    Language.IsRegular (AnnLang A k l φ) := by
  induction φ with
  | le i j =>
    intro k l hfo _
    have hi : i < k := hfo (by simp [MSO.freeFO])
    have hj : j < k := hfo (by simp [MSO.freeFO])
    have hreg := isRegular_and (isRegular_valid A k l)
      (isRegular_findIdx_le (foBit (A := A) (l := l) ⟨i, hi⟩) (foBit (A := A) (l := l) ⟨j, hj⟩))
    refine isRegular_of_eq hreg (fun u => ?_)
    constructor
    · rintro ⟨hv, hle⟩
      have hle' : foOf u i ≤ foOf u j := hle
      rw [foOf_of_lt u hi, foOf_of_lt u hj] at hle'
      exact ⟨hv, hle'⟩
    · rintro ⟨hv, hle⟩
      have hle' : u.findIdx (foBit (A := A) (l := l) ⟨i, hi⟩)
          ≤ u.findIdx (foBit (A := A) (l := l) ⟨j, hj⟩) := hle
      refine ⟨hv, ?_⟩
      show foOf u i ≤ foOf u j
      rw [foOf_of_lt u hi, foOf_of_lt u hj]
      exact hle'
  | lab a i =>
    intro k l hfo _
    have hi : i < k := hfo (by simp [MSO.freeFO])
    have hreg := isRegular_and (isRegular_valid A k l)
      (isRegular_scan (foBit (A := A) (l := l) ⟨i, hi⟩) (fun x : Ann A k l => decide (x.1 = a)))
    refine isRegular_of_eq hreg (fun u => ?_)
    constructor
    · rintro ⟨hv, hs⟩
      have hs' : (u.map Prod.fst)[foOf u i]? = some a := hs
      rw [foOf_of_lt u hi, List.getElem?_map] at hs'
      obtain ⟨x, hx, hxa⟩ := Option.map_eq_some_iff.1 hs'
      exact ⟨hv, x, hx, by simp [hxa]⟩
    · rintro ⟨hv, hs⟩
      obtain ⟨x, hx, hxa⟩ :
          ∃ x, u[u.findIdx (foBit (A := A) (l := l) ⟨i, hi⟩)]? = some x ∧ decide (x.1 = a) = true :=
        hs
      refine ⟨hv, ?_⟩
      show (u.map Prod.fst)[foOf u i]? = some a
      rw [foOf_of_lt u hi, List.getElem?_map, hx]
      simp only [decide_eq_true_eq] at hxa
      simp [hxa]
  | mem i j =>
    intro k l hfo hso
    have hi : i < k := hfo (by simp [MSO.freeFO])
    have hj : j < l := hso (by simp [MSO.freeSO])
    have hreg := isRegular_and (isRegular_valid A k l)
      (isRegular_scan (foBit (A := A) (l := l) ⟨i, hi⟩) (soBit (A := A) (k := k) ⟨j, hj⟩))
    refine isRegular_of_eq hreg (fun u => ?_)
    constructor
    · rintro ⟨hv, hs⟩
      have hs' : foOf u i ∈ soOf u j := hs
      rw [soOf_of_lt u hj, foOf_of_lt u hi] at hs'
      exact ⟨hv, hs'⟩
    · rintro ⟨hv, hs⟩
      have hs' : MarkedAt (soBit (A := A) (k := k) ⟨j, hj⟩) u
          (u.findIdx (foBit (A := A) (l := l) ⟨i, hi⟩)) := hs
      refine ⟨hv, ?_⟩
      show foOf u i ∈ soOf u j
      rw [soOf_of_lt u hj, foOf_of_lt u hi]
      exact hs'
  | not φ ih =>
    intro k l hfo hso
    have hreg := isRegular_and (isRegular_valid A k l) (isRegular_not (ih k l hfo hso))
    refine isRegular_of_eq hreg (fun u => ?_)
    constructor
    · rintro ⟨hv, hn⟩
      refine ⟨hv, ?_⟩
      intro hmem
      obtain ⟨-, hs⟩ := hmem
      exact hn hs
    · rintro ⟨hv, hn⟩
      refine ⟨hv, ?_⟩
      intro hs
      exact hn ⟨hv, hs⟩
  | and φ ψ ihφ ihψ =>
    intro k l hfo hso
    have h1 := ihφ k l (fun x hx => hfo (Or.inl hx)) (fun x hx => hso (Or.inl hx))
    have h2 := ihψ k l (fun x hx => hfo (Or.inr hx)) (fun x hx => hso (Or.inr hx))
    have hreg := isRegular_and h1 h2
    refine isRegular_of_eq hreg (fun u => ?_)
    constructor
    · rintro ⟨hv, hφ, hψ⟩
      exact ⟨⟨hv, hφ⟩, ⟨hv, hψ⟩⟩
    · rintro ⟨⟨hv, hφ⟩, -, hψ⟩
      exact ⟨hv, hφ, hψ⟩
  | or φ ψ ihφ ihψ =>
    intro k l hfo hso
    have h1 := ihφ k l (fun x hx => hfo (Or.inl hx)) (fun x hx => hso (Or.inl hx))
    have h2 := ihψ k l (fun x hx => hfo (Or.inr hx)) (fun x hx => hso (Or.inr hx))
    have hreg := isRegular_or h1 h2
    refine isRegular_of_eq hreg (fun u => ?_)
    constructor
    · rintro ⟨hv, hs⟩
      rcases hs with hφ | hψ
      · exact Or.inl ⟨hv, hφ⟩
      · exact Or.inr ⟨hv, hψ⟩
    · rintro (⟨hv, hφ⟩ | ⟨hv, hψ⟩)
      · exact ⟨hv, Or.inl hφ⟩
      · exact ⟨hv, Or.inr hψ⟩
  | exFO i φ ih =>
    intro k l hfo hso
    have hkk' : k ≤ max k (i + 1) := le_max_left _ _
    have hik' : i < max k (i + 1) := lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right _ _)
    have hfo' : φ.freeFO ⊆ {m | m < max k (i + 1)} := by
      intro x hx
      by_cases hxi : x = i
      · subst hxi; exact hik'
      · have hx' : x ∈ φ.freeFO \ {i} := ⟨hx, hxi⟩
        have hlt := hfo hx'
        simp only [Set.mem_setOf_eq] at hlt ⊢
        omega
    have IH := ih (max k (i + 1)) l hfo' hso
    set k' := max k (i + 1) with hk'def
    set π : Ann A k' l → Ann A k l := fun x =>
      (x.1, fun y : Fin k => if (y : ℕ) = i then false else x.2.1 (Fin.castLE hkk' y), x.2.2)
      with hπ
    set ζ : Ann A k l → Ann A k l := fun x =>
      (x.1, fun y : Fin k => if (y : ℕ) = i then false else x.2.1 y, x.2.2) with hζ
    have hreg := isRegular_and (isRegular_valid A k l) (isRegular_comap ζ (isRegular_image π IH))
    refine isRegular_of_eq hreg (fun v => ?_)
    have hsatEx : MSO.Sat (v.map Prod.fst) (foOf v) (soOf v) (MSO.exFO i φ)
        ↔ ∃ p < (v.map Prod.fst).length,
            MSO.Sat (v.map Prod.fst) (Function.update (foOf v) i p) (soOf v) φ := Iff.rfl
    constructor
    · -- from a satisfying valuation to an annotated string over `k'` variables
      rintro ⟨hv, hsEx⟩
      obtain ⟨p, hp, hsat⟩ := hsatEx.1 hsEx
      have hpv : p < v.length := by simpa using hp
      refine ⟨hv, ?_⟩
      set g : Ann A k l → Bool → Ann A k' l := fun x c =>
        (x.1, fun y : Fin k' => if h : ((y : ℕ) < k ∧ (y : ℕ) ≠ i) then x.2.1 ⟨y, h.1⟩ else c,
          x.2.2) with hg
      set u : List (Ann A k' l) := markWith g (fun q => decide (q = p)) v with hu
      have hfst : u.map Prod.fst = v.map Prod.fst :=
        map_markWith g _ v Prod.fst Prod.fst (fun x c => rfl)
      have hmapπ : u.map π = v.map ζ := by
        refine map_markWith g _ v π ζ (fun x c => ?_)
        simp only [hπ, hζ, hg, Prod.mk.injEq, true_and, and_true]
        funext y
        by_cases hy : (y : ℕ) = i
        · simp [hy]
        · simp [hy, y.isLt]
      have hmark : ∀ y : Fin k', ¬ ((y : ℕ) < k ∧ (y : ℕ) ≠ i) →
          ∀ q, MarkedAt (foBit (A := A) (l := l) y) u q ↔ q = p := by
        intro y hy q
        rw [hu, markedAt_markWith_mark g _ v (foBit (A := A) (l := l) y)
          (fun x c => by simp [foBit, hg, hy]) q]
        constructor
        · rintro ⟨-, hq⟩; simpa using hq
        · rintro rfl; exact ⟨hpv, by simp⟩
      have hcopy : ∀ (y : Fin k') (hy : (y : ℕ) < k ∧ (y : ℕ) ≠ i),
          ∀ q, MarkedAt (foBit (A := A) (l := l) y) u q
            ↔ MarkedAt (foBit (A := A) (l := l) ⟨(y : ℕ), hy.1⟩) v q := by
        intro y hy q
        rw [hu, markedAt_markWith_copy g _ v (foBit (A := A) (l := l) y)
          (foBit (A := A) (l := l) ⟨(y : ℕ), hy.1⟩) (fun x c => by simp [foBit, hg, hy]) q]
      have hvu : Valid u := by
        intro y
        by_cases hy : ((y : ℕ) < k ∧ (y : ℕ) ≠ i)
        · obtain ⟨q0, hq0⟩ := hv ⟨(y : ℕ), hy.1⟩
          exact ⟨q0, fun q => (hcopy y hy q).trans (hq0 q)⟩
        · exact ⟨p, hmark y hy⟩
      have hfoi : foOf u i = p := by
        rw [foOf_of_lt u hik']
        exact findIdx_eq_of_marksOnce (hmark ⟨i, hik'⟩ (by simp))
      have hfom : ∀ (m : ℕ), m < k → m ≠ i → foOf u m = foOf v m := by
        intro m hm hmi
        have hmk' : m < k' := lt_of_lt_of_le hm hkk'
        rw [foOf_of_lt u hmk']
        refine findIdx_eq_of_marksOnce ?_
        intro q
        rw [hcopy ⟨m, hmk'⟩ ⟨hm, hmi⟩ q]
        exact marked_iff_eq_foOf hv hm q
      have hsoeq : soOf u = soOf v := by
        funext m
        by_cases hm : m < l
        · rw [soOf_of_lt u hm, soOf_of_lt v hm]
          ext q
          simp only [Set.mem_setOf_eq]
          rw [hu, markedAt_markWith_copy g _ v (soBit (A := A) (k := k') ⟨m, hm⟩)
            (soBit (A := A) (k := k) ⟨m, hm⟩) (fun x c => by simp [soBit, hg]) q]
        · rw [soOf_of_not_lt u hm, soOf_of_not_lt v hm]
      refine ⟨u, ⟨hvu, ?_⟩, hmapπ⟩
      rw [hfst, hsoeq]
      have hagree : ∀ m ∈ φ.freeFO, Function.update (foOf v) i p m = foOf u m := by
        intro m hm
        by_cases hmi : m = i
        · subst hmi; rw [Function.update_self, hfoi]
        · have hmk : m < k := hfo ⟨hm, hmi⟩
          rw [Function.update_of_ne hmi, hfom m hmk hmi]
      exact (MSO.sat_congr (v.map Prod.fst) φ (Function.update (foOf v) i p) (foOf u)
        (soOf v) (soOf v) hagree (fun _ _ => rfl)).1 hsat
    · -- from an annotated string over `k'` variables back to a valuation
      rintro ⟨hv, u, ⟨hvu, hsu⟩, hmap⟩
      have hlen : u.length = v.length := by
        have h := congrArg List.length hmap
        simpa using h
      have hfst : u.map Prod.fst = v.map Prod.fst := by
        have h := congrArg (fun z => z.map Prod.fst) hmap
        simpa [List.map_map, Function.comp_def, hπ, hζ] using h
      have hmarkeq : ∀ (m : ℕ) (hm : m < k), m ≠ i → ∀ q,
          MarkedAt (foBit (A := A) (l := l) ⟨m, lt_of_lt_of_le hm hkk'⟩) u q
            ↔ MarkedAt (foBit (A := A) (l := l) ⟨m, hm⟩) v q := by
        intro m hm hmi q
        rw [markedAt_map (f := π) (P := foBit (A := A) (l := l) ⟨m, lt_of_lt_of_le hm hkk'⟩)
              (Q := foBit (A := A) (l := l) ⟨m, hm⟩) (fun x => by simp [foBit, hπ, hmi]) u q,
            hmap,
            ← markedAt_map (f := ζ) (P := foBit (A := A) (l := l) ⟨m, hm⟩)
              (Q := foBit (A := A) (l := l) ⟨m, hm⟩) (fun x => by simp [foBit, hζ, hmi]) v q]
      have hfom : ∀ (m : ℕ) (hm : m < k), m ≠ i → foOf u m = foOf v m := by
        intro m hm hmi
        rw [foOf_of_lt u (lt_of_lt_of_le hm hkk')]
        refine findIdx_eq_of_marksOnce ?_
        intro q
        rw [hmarkeq m hm hmi q]
        exact marked_iff_eq_foOf hv hm q
      have hsoeq : soOf u = soOf v := by
        funext m
        by_cases hm : m < l
        · rw [soOf_of_lt u hm, soOf_of_lt v hm]
          ext q
          simp only [Set.mem_setOf_eq]
          rw [markedAt_map (f := π) (P := soBit (A := A) (k := k') ⟨m, hm⟩)
                (Q := soBit (A := A) (k := k) ⟨m, hm⟩) (fun x => by simp [soBit, hπ]) u q,
              hmap,
              ← markedAt_map (f := ζ) (P := soBit (A := A) (k := k) ⟨m, hm⟩)
                (Q := soBit (A := A) (k := k) ⟨m, hm⟩) (fun x => by simp [soBit, hζ]) v q]
        · rw [soOf_of_not_lt u hm, soOf_of_not_lt v hm]
      refine ⟨hv, hsatEx.2 ⟨foOf u i, ?_, ?_⟩⟩
      · have hlt : foOf u i < u.length := foOf_lt_length hvu hik'
        simpa [hlen] using hlt
      · have hagree : ∀ m ∈ φ.freeFO, foOf u m = Function.update (foOf v) i (foOf u i) m := by
          intro m hm
          by_cases hmi : m = i
          · subst hmi; rw [Function.update_self]
          · have hmk : m < k := hfo ⟨hm, hmi⟩
            rw [Function.update_of_ne hmi, hfom m hmk hmi]
        have hs := (MSO.sat_congr (u.map Prod.fst) φ (foOf u)
          (Function.update (foOf v) i (foOf u i)) (soOf u) (soOf v) hagree
          (fun m _ => congrFun hsoeq m)).1 hsu
        rwa [hfst] at hs
  | exSO j φ ih =>
    intro k l hfo hso
    have hll' : l ≤ max l (j + 1) := le_max_left _ _
    have hjl' : j < max l (j + 1) := lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)
    have hso' : φ.freeSO ⊆ {m | m < max l (j + 1)} := by
      intro x hx
      by_cases hxj : x = j
      · subst hxj; exact hjl'
      · have hx' : x ∈ φ.freeSO \ {j} := ⟨hx, hxj⟩
        have hlt := hso hx'
        simp only [Set.mem_setOf_eq] at hlt ⊢
        omega
    have IH := ih k (max l (j + 1)) hfo hso'
    set l' := max l (j + 1) with hl'def
    set π : Ann A k l' → Ann A k l := fun x =>
      (x.1, x.2.1, fun y : Fin l => if (y : ℕ) = j then false else x.2.2 (Fin.castLE hll' y))
      with hπ
    set ζ : Ann A k l → Ann A k l := fun x =>
      (x.1, x.2.1, fun y : Fin l => if (y : ℕ) = j then false else x.2.2 y) with hζ
    have hreg := isRegular_and (isRegular_valid A k l) (isRegular_comap ζ (isRegular_image π IH))
    refine isRegular_of_eq hreg (fun v => ?_)
    have hsatEx : MSO.Sat (v.map Prod.fst) (foOf v) (soOf v) (MSO.exSO j φ)
        ↔ ∃ S ⊆ {p | p < (v.map Prod.fst).length},
            MSO.Sat (v.map Prod.fst) (foOf v) (Function.update (soOf v) j S) φ := Iff.rfl
    constructor
    · rintro ⟨hv, hsEx⟩
      obtain ⟨S, hS, hsat⟩ := hsatEx.1 hsEx
      refine ⟨hv, ?_⟩
      set g : Ann A k l → Bool → Ann A k l' := fun x c =>
        (x.1, x.2.1,
          fun y : Fin l' => if h : ((y : ℕ) < l ∧ (y : ℕ) ≠ j) then x.2.2 ⟨y, h.1⟩ else c)
        with hg
      set u : List (Ann A k l') := markWith g (fun q => decide (q ∈ S)) v with hu
      have hfst : u.map Prod.fst = v.map Prod.fst :=
        map_markWith g _ v Prod.fst Prod.fst (fun x c => rfl)
      have hmapπ : u.map π = v.map ζ := by
        refine map_markWith g _ v π ζ (fun x c => ?_)
        simp only [hπ, hζ, hg, Prod.mk.injEq, true_and]
        funext y
        by_cases hy : (y : ℕ) = j
        · simp [hy]
        · simp [hy, y.isLt]
      have hvu : Valid u := by
        intro y
        obtain ⟨q0, hq0⟩ := hv y
        refine ⟨q0, fun q => ?_⟩
        rw [hu, markedAt_markWith_copy g _ v (foBit (A := A) (l := l') y)
          (foBit (A := A) (l := l) y) (fun x c => rfl) q]
        exact hq0 q
      have hfoeq : foOf u = foOf v := by
        funext m
        by_cases hm : m < k
        · rw [foOf_of_lt u hm]
          refine findIdx_eq_of_marksOnce ?_
          intro q
          rw [hu, markedAt_markWith_copy g _ v (foBit (A := A) (l := l') ⟨m, hm⟩)
            (foBit (A := A) (l := l) ⟨m, hm⟩) (fun x c => rfl) q]
          exact marked_iff_eq_foOf hv hm q
        · rw [foOf_of_not_lt u hm, foOf_of_not_lt v hm]
      have hsoj : soOf u j = S := by
        rw [soOf_of_lt u hjl']
        ext q
        simp only [Set.mem_setOf_eq]
        rw [hu, markedAt_markWith_mark g _ v (soBit (A := A) (k := k) ⟨j, hjl'⟩)
          (fun x c => by simp [soBit, hg]) q]
        constructor
        · rintro ⟨-, hq⟩; simpa using hq
        · intro hq
          have hql : q < v.length := by simpa using hS hq
          exact ⟨hql, by simp [hq]⟩
      have hsom : ∀ (m : ℕ), m < l → m ≠ j → soOf u m = soOf v m := by
        intro m hm hmj
        have hml' : m < l' := lt_of_lt_of_le hm hll'
        rw [soOf_of_lt u hml', soOf_of_lt v hm]
        ext q
        simp only [Set.mem_setOf_eq]
        rw [hu, markedAt_markWith_copy g _ v (soBit (A := A) (k := k) ⟨m, hml'⟩)
          (soBit (A := A) (k := k) ⟨m, hm⟩) (fun x c => by simp [soBit, hg, hm, hmj]) q]
      refine ⟨u, ⟨hvu, ?_⟩, hmapπ⟩
      rw [hfst, hfoeq]
      have hagree : ∀ m ∈ φ.freeSO, Function.update (soOf v) j S m = soOf u m := by
        intro m hm
        by_cases hmj : m = j
        · subst hmj; rw [Function.update_self, hsoj]
        · have hml : m < l := hso ⟨hm, hmj⟩
          rw [Function.update_of_ne hmj, hsom m hml hmj]
      exact (MSO.sat_congr (v.map Prod.fst) φ (foOf v) (foOf v)
        (Function.update (soOf v) j S) (soOf u) (fun _ _ => rfl) hagree).1 hsat
    · rintro ⟨hv, u, ⟨hvu, hsu⟩, hmap⟩
      have hlen : u.length = v.length := by
        have h := congrArg List.length hmap
        simpa using h
      have hfst : u.map Prod.fst = v.map Prod.fst := by
        have h := congrArg (fun z => z.map Prod.fst) hmap
        simpa [List.map_map, Function.comp_def, hπ, hζ] using h
      have hfoeq : foOf u = foOf v := by
        funext m
        by_cases hm : m < k
        · rw [foOf_of_lt u hm]
          refine findIdx_eq_of_marksOnce ?_
          intro q
          rw [markedAt_map (f := π) (P := foBit (A := A) (l := l') ⟨m, hm⟩)
                (Q := foBit (A := A) (l := l) ⟨m, hm⟩) (fun x => by simp [foBit, hπ]) u q,
              hmap,
              ← markedAt_map (f := ζ) (P := foBit (A := A) (l := l) ⟨m, hm⟩)
                (Q := foBit (A := A) (l := l) ⟨m, hm⟩) (fun x => by simp [foBit, hζ]) v q]
          exact marked_iff_eq_foOf hv hm q
        · rw [foOf_of_not_lt u hm, foOf_of_not_lt v hm]
      have hsom : ∀ (m : ℕ), m < l → m ≠ j → soOf u m = soOf v m := by
        intro m hm hmj
        have hml' : m < l' := lt_of_lt_of_le hm hll'
        rw [soOf_of_lt u hml', soOf_of_lt v hm]
        ext q
        simp only [Set.mem_setOf_eq]
        rw [markedAt_map (f := π) (P := soBit (A := A) (k := k) ⟨m, hml'⟩)
              (Q := soBit (A := A) (k := k) ⟨m, hm⟩) (fun x => by simp [soBit, hπ, hmj]) u q,
            hmap,
            ← markedAt_map (f := ζ) (P := soBit (A := A) (k := k) ⟨m, hm⟩)
              (Q := soBit (A := A) (k := k) ⟨m, hm⟩) (fun x => by simp [soBit, hζ, hmj]) v q]
      refine ⟨hv, hsatEx.2 ⟨soOf u j, ?_, ?_⟩⟩
      · intro p hp
        have hlt := soOf_subset_length u j hp
        simp only [Set.mem_setOf_eq] at hlt ⊢
        simpa [hlen] using hlt
      · have hagree : ∀ m ∈ φ.freeSO, soOf u m = Function.update (soOf v) j (soOf u j) m := by
          intro m hm
          by_cases hmj : m = j
          · subst hmj; rw [Function.update_self]
          · have hml : m < l := hso ⟨hm, hmj⟩
            rw [Function.update_of_ne hmj, hsom m hml hmj]
        have hs := (MSO.sat_congr (u.map Prod.fst) φ (foOf u) (foOf v)
          (soOf u) (Function.update (soOf v) j (soOf u j)) (fun m _ => congrFun hfoeq m)
          hagree).1 hsu
        rwa [hfst] at hs

/-! ## The language of Lemma `lem:mso-free-variables`

`AnnLang A k l φ` is exactly the language of annotated strings that appears in
the statement of Lemma `lem:mso-free-variables`. -/

@[simp] lemma annotate_length (k l : ℕ) (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ) :
    (annotate k l w fo so).length = w.length := by
  simp [annotate]

open scoped Classical in
lemma annotate_getElem? (k l : ℕ) (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ) (q : ℕ) :
    (annotate k l w fo so)[q]? =
      (w[q]?).map (fun a => (a, fun i => decide (fo i = q), fun j => decide (q ∈ so j))) := by
  simp [annotate, Option.map_map, Function.comp_def]

lemma map_fst_annotate (k l : ℕ) (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ) :
    (annotate k l w fo so).map Prod.fst = w := by
  apply List.ext_getElem?
  intro q
  simp [annotate_getElem?, Option.map_map, Function.comp_def]

open scoped Classical in
lemma markedAt_annotate_fo (k l : ℕ) (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ)
    (i : Fin k) (q : ℕ) :
    MarkedAt (foBit (A := A) (l := l) i) (annotate k l w fo so) q ↔ (q < w.length ∧ fo i = q) := by
  simp only [MarkedAt, annotate_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
    rw [List.getElem?_eq_some_iff] at ha
    exact ⟨ha.1, by simpa [foBit] using hy⟩
  · rintro ⟨hq, hfo⟩
    exact ⟨_, ⟨w[q], List.getElem?_eq_getElem hq, rfl⟩, by simpa [foBit] using hfo⟩

open scoped Classical in
lemma markedAt_annotate_so (k l : ℕ) (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ)
    (j : Fin l) (q : ℕ) :
    MarkedAt (soBit (A := A) (k := k) j) (annotate k l w fo so) q ↔ (q < w.length ∧ q ∈ so j) := by
  simp only [MarkedAt, annotate_getElem?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
    rw [List.getElem?_eq_some_iff] at ha
    exact ⟨ha.1, by simpa [soBit] using hy⟩
  · rintro ⟨hq, hso⟩
    exact ⟨_, ⟨w[q], List.getElem?_eq_getElem hq, rfl⟩, by simpa [soBit] using hso⟩

lemma valid_annotate {k l : ℕ} {w : List A} {fo : Fin k → ℕ} {so : Fin l → Set ℕ}
    (hfo : ∀ i, fo i < w.length) : Valid (annotate k l w fo so) := by
  intro i
  refine ⟨fo i, fun q => ?_⟩
  rw [markedAt_annotate_fo]
  constructor
  · rintro ⟨-, h⟩; exact h.symm
  · rintro rfl; exact ⟨hfo i, rfl⟩

lemma foOf_annotate {k l : ℕ} {w : List A} {fo : Fin k → ℕ} {so : Fin l → Set ℕ}
    (hfo : ∀ i, fo i < w.length) : foOf (annotate k l w fo so) = extFO k fo := by
  funext m
  by_cases hm : m < k
  · rw [foOf_of_lt _ hm, extFO, dif_pos hm]
    refine findIdx_eq_of_marksOnce (P := foBit (A := A) (l := l) ⟨m, hm⟩) (fun q => ?_)
    rw [markedAt_annotate_fo]
    constructor
    · rintro ⟨-, h⟩; exact h.symm
    · rintro rfl; exact ⟨hfo _, rfl⟩
  · rw [foOf_of_not_lt _ hm, extFO, dif_neg hm]

lemma soOf_annotate {k l : ℕ} {w : List A} {fo : Fin k → ℕ} {so : Fin l → Set ℕ}
    (hso : ∀ j, so j ⊆ {p | p < w.length}) : soOf (annotate k l w fo so) = extSO l so := by
  funext m
  by_cases hm : m < l
  · rw [soOf_of_lt _ hm, extSO, dif_pos hm]
    ext q
    rw [Set.mem_setOf_eq, markedAt_annotate_so]
    exact ⟨fun h => h.2, fun h => ⟨hso _ h, h⟩⟩
  · rw [soOf_of_not_lt _ hm, extSO, dif_neg hm]

open scoped Classical in
/-- The language `AnnLang A k l φ` is the language of Lemma `lem:mso-free-variables`: the
annotated strings `w ⊗ x₁ ⊗ ⋯ ⊗ x_k ⊗ X₁ ⊗ ⋯ ⊗ X_l` such that the valuation satisfies `φ` in `w`. -/
lemma annLang_eq (φ : MSO A) (k l : ℕ) :
    AnnLang A k l φ =
      {u : List (Ann A k l) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ} := by
  ext u
  constructor
  · rintro ⟨hv, hsat⟩
    refine ⟨u.map Prod.fst, fun i => foOf u i, fun j => soOf u j, ?_, ?_, ?_, ?_⟩
    · intro i; simpa using foOf_lt_length hv i.isLt
    · intro j p hp
      have := soOf_subset_length u j hp
      simpa using this
    · apply List.ext_getElem?
      intro q
      rw [annotate_getElem?]
      rcases hq : u[q]? with - | x
      · simp [hq]
      · have hqx : u[q]? = some x := hq
        have h2 : (fun i : Fin k => decide (foOf u i = q)) = x.2.1 := by
          funext i
          have hmk : MarkedAt (foBit (A := A) (l := l) i) u q ↔ q = foOf u i :=
            marked_iff_eq_foOf hv i.isLt q
          have hmk' : MarkedAt (foBit (A := A) (l := l) i) u q ↔ x.2.1 i = true := by
            constructor
            · rintro ⟨y, hy, hby⟩
              rw [hqx] at hy
              cases hy
              exact hby
            · intro h; exact ⟨x, hqx, h⟩
          by_cases hx : x.2.1 i = true
          · simp [hx, (hmk.1 (hmk'.2 hx)).symm]
          · have hne : ¬ (foOf u i = q) := by
              intro h; exact hx (hmk'.1 (hmk.2 h.symm))
            have hxf : x.2.1 i = false := by simpa using hx
            simp [hne, hxf]
        have h3 : (fun j : Fin l => decide (q ∈ soOf u j)) = x.2.2 := by
          funext j
          have hmk : MarkedAt (soBit (A := A) (k := k) j) u q ↔ q ∈ soOf u j := by
            rw [soOf_of_lt u j.isLt]; simp
          have hmk' : MarkedAt (soBit (A := A) (k := k) j) u q ↔ x.2.2 j = true := by
            constructor
            · rintro ⟨y, hy, hby⟩
              rw [hqx] at hy
              cases hy
              exact hby
            · intro h; exact ⟨x, hqx, h⟩
          by_cases hx : x.2.2 j = true
          · simp [hx, hmk.1 (hmk'.2 hx)]
          · have hne : ¬ (q ∈ soOf u j) := fun h => hx (hmk'.1 (hmk.2 h))
            have hxf : x.2.2 j = false := by simpa using hx
            simp [hne, hxf]
        simp only [hqx, List.getElem?_map, Option.map_some]
        rw [h2, h3]
    · have hfo : extFO k (fun i => foOf u i) = foOf u := by
        funext m
        by_cases hm : m < k
        · rw [extFO, dif_pos hm]
        · rw [extFO, dif_neg hm, foOf_of_not_lt u hm]
      have hso : extSO l (fun j => soOf u j) = soOf u := by
        funext m
        by_cases hm : m < l
        · rw [extSO, dif_pos hm]
        · rw [extSO, dif_neg hm, soOf_of_not_lt u hm]
      rw [hfo, hso]
      exact hsat
  · rintro ⟨w, fo, so, hfo, hso, rfl, hsat⟩
    refine ⟨valid_annotate hfo, ?_⟩
    rw [map_fst_annotate, foOf_annotate hfo, soOf_annotate hso]
    exact hsat

open scoped Classical in
/-- **Lemma `lem:mso-free-variables`** in the form in which it is stated in
`RequestProject/PartC/MSO.lean`. -/
theorem mso_annotated_regular_aux (φ : MSO A) (k l : ℕ)
    (hfo : φ.freeFO ⊆ {i | i < k}) (hso : φ.freeSO ⊆ {j | j < l}) :
    Language.IsRegular
      {u : List (A × (Fin k → Bool) × (Fin l → Bool)) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ} := by
  rw [← annLang_eq]
  exact isRegular_annLang φ k l hfo hso

end MSOAnnot

export MSOAnnot (mso_annotated_regular_aux)

end Lax916827Proofs.Transducers
