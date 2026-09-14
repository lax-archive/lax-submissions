/-
**The atoms of the child configuration graph.**

The letters of the child configuration graph of a configuration are determined, gap by gap, by
finitely many *regular properties of the string representation of the configuration with that gap
marked* -- the *atoms* of this file.  There are seven kinds:

* `Transducers.CGL.hgtL` -- the stack of the configuration contains a pebble of a given index; the
  indices that occur are exactly `0, …, ℓ - 1`, so these atoms recover the height `ℓ` of the
  configuration, which is the index `nid` of the moving pebble of the graph;
* `Transducers.CGL.stateL` -- the state of the configuration;
* `Transducers.CGL.lettL`, `Transducers.CGL.pebL` -- the input letter and the pebbles of the marked
  gap, which are the fields `lett` and `peb` of the letter of the graph;
* `Transducers.CGL.zeroL` -- the marked gap is the first one;
* `Transducers.CGL.firstL` -- a single step leads from the configuration to the first child, which
  gives the field `src`;
* `Transducers.CGL.edgeL` -- the vertex in the marked column is a child and its successor is a
  given vertex in a neighbouring column, which gives the fields `nxt` and `prv`.

All of them are inverse images of the reachability language of `RequestProject/PartD/PebReach.lean`
under the window map of `RequestProject/PartD/CGLang.lean`, or Boolean combinations of such, and
they are therefore regular.  The last one also uses the *second* mark, to say that no child lies
strictly between the two: this is the description of the successor relation given by
`Transducers.CG.nextChild_iff_no_mid`.  The second mark is quantified away by
`Transducers.CGL.existsExtraL`, the image of the language under the map that forgets it.
-/
import Lax194892Proofs.Source.PartD.CGLang
import Lax194892Proofs.Source.PartD.ChildReach
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CGL

open MarkStr RegAut

open scoped Classical

variable {A B Q : Type} {k : ℕ}

/-! ## Reachability, read off the marked string representation of a configuration -/

/-- The marked strings whose derived pair encoding is a reachable pair of configurations. -/
noncomputable def reachL (M : Pebble A B Q k) (ell : ℕ) (nid : Fin k) (q₁ q₂ : Q)
    (sp₁ sp₂ : Spot) : Language (MLetter A Q k) :=
  {u | (winMap u).map (pairMap nid q₁ q₂ sp₁ sp₂) ∈ PebEnc.reachLang M ell}

/-- The marked strings whose derived pair encoding is a pair joined by a single step. -/
noncomputable def stepL (M : Pebble A B Q k) (nid : Fin k) (q₁ q₂ : Q) (sp₁ sp₂ : Spot) :
    Language (MLetter A Q k) :=
  {u | (winMap u).map (pairMap nid (q₁, false) (q₂, true) sp₁ sp₂)
        ∈ PebEnc.reachLang (Pebble.stepMach M) 0}

/-! ## The simple atoms -/

/-- The stack contains a pebble with the index `i`. -/
def hgtL (i : Fin k) : Language (MLetter A Q k) := {u | ∃ c ∈ u, c.1.2.2 i = true}

/-- The state of the configuration is `q`. -/
def stateL (q : Q) : Language (MLetter A Q k) := {u | ∀ c ∈ u, c.1.1 = q}

/-- The input letter of the marked gap is `a`. -/
def lettL (a : Option A) : Language (MLetter A Q k) :=
  {u | ∃ c ∈ u, c.2.1 = true ∧ c.1.2.1 = a}

/-- The marked gap carries the pebble with the index `i`. -/
def pebL (i : Fin k) : Language (MLetter A Q k) := {u | ∃ c ∈ u, c.2.1 = true ∧ c.1.2.2 i = true}

/-- The marked gap is the first one. -/
def zeroL : Language (MLetter A Q k) :=
  {u | ∀ t ∈ winMap u, (t.1.isNone = true → t.2.1.2.1 = true)}

/-- The second mark does not sit in the position named by the spot. -/
def neqSpotL (sp : Spot) : Language (MLetter A Q k) :=
  {u | ∀ t ∈ winMap u, ¬ (t.2.1.2.2 = true ∧ spotBit sp t = true)}

/-- The empty language of marked string representations. -/
def emptyL : Language (MLetter A Q k) := {u | u ∉ (Set.univ : Language (MLetter A Q k))}

@[simp] lemma mem_emptyL (u : List (MLetter A Q k)) : u ∈ emptyL (A := A) (Q := Q) (k := k) ↔ False :=
  ⟨fun h => h (Set.mem_univ _), fun h => h.elim⟩

lemma emptyL_isRegular : (emptyL (A := A) (Q := Q) (k := k)).IsRegular :=
  isRegular_not isRegular_univ

lemma hgtL_isRegular (i : Fin k) : (hgtL (A := A) (Q := Q) i).IsRegular := by
  refine isRegular_of_eq (isRegular_not (isRegular_all
    (fun c : MLetter A Q k => !c.1.2.2 i))) (fun u => ?_)
  constructor
  · rintro ⟨c, hc, hb⟩ h
    have := h c hc
    simp [hb] at this
  · intro h
    by_contra hc
    exact h (fun c hcm => by
      by_cases hb : c.1.2.2 i = true
      · exact absurd ⟨c, hcm, hb⟩ hc
      · simp only [Bool.not_eq_true] at hb
        simp [hb])

lemma stateL_isRegular (q : Q) : (stateL (A := A) (k := k) q).IsRegular := by
  refine isRegular_of_eq (isRegular_all (fun c : MLetter A Q k => decide (c.1.1 = q)))
    (fun u => ?_)
  constructor
  · intro h c hc; exact decide_eq_true (h c hc)
  · intro h c hc; exact of_decide_eq_true (h c hc)

lemma lettL_isRegular (a : Option A) : (lettL (Q := Q) (k := k) a).IsRegular := by
  refine isRegular_of_eq (isRegular_not (isRegular_all
    (fun c : MLetter A Q k => !(c.2.1 && decide (c.1.2.1 = a))))) (fun u => ?_)
  constructor
  · rintro ⟨c, hc, h1, h2⟩ h
    have := h c hc
    simp [h1, h2] at this
  · intro h
    by_contra hc
    exact h (fun c hcm => by
      by_cases hb : c.2.1 = true ∧ c.1.2.1 = a
      · exact absurd ⟨c, hcm, hb.1, hb.2⟩ hc
      · rw [not_and_or] at hb
        rcases hb with hb | hb
        · simp only [Bool.not_eq_true] at hb
          simp [hb]
        · simp [decide_eq_false hb])

lemma pebL_isRegular (i : Fin k) : (pebL (A := A) (Q := Q) i).IsRegular := by
  refine isRegular_of_eq (isRegular_not (isRegular_all
    (fun c : MLetter A Q k => !(c.2.1 && c.1.2.2 i)))) (fun u => ?_)
  constructor
  · rintro ⟨c, hc, h1, h2⟩ h
    have := h c hc
    simp [h1, h2] at this
  · intro h
    by_contra hc
    exact h (fun c hcm => by
      by_cases hb : c.2.1 = true ∧ c.1.2.2 i = true
      · exact absurd ⟨c, hcm, hb.1, hb.2⟩ hc
      · rw [not_and_or] at hb
        rcases hb with hb | hb <;>
          (simp only [Bool.not_eq_true] at hb; simp [hb]))

variable [Finite A] [Finite Q]

lemma zeroL_isRegular : (zeroL (A := A) (Q := Q) (k := k)).IsRegular := by
  have key : ∀ t : Win (MLetter A Q k),
      ((!t.1.isNone || t.2.1.2.1) = true ↔ (t.1.isNone = true → t.2.1.2.1 = true)) := by
    intro t
    cases h : t.1.isNone <;> simp
  refine isRegular_of_eq (isRegular_all_win
    (fun t : Win (MLetter A Q k) => !t.1.isNone || t.2.1.2.1)) (fun u => ?_)
  exact ⟨fun h t ht => (key t).2 (h t ht), fun h t ht => (key t).1 (h t ht)⟩

lemma neqSpotL_isRegular (sp : Spot) : (neqSpotL (A := A) (Q := Q) (k := k) sp).IsRegular := by
  have key : ∀ t : Win (MLetter A Q k),
      ((!(t.2.1.2.2 && spotBit sp t)) = true ↔ ¬ (t.2.1.2.2 = true ∧ spotBit sp t = true)) := by
    intro t
    cases h1 : t.2.1.2.2 <;> cases h2 : spotBit sp t <;> simp
  refine isRegular_of_eq (isRegular_all_win
    (fun t : Win (MLetter A Q k) => !(t.2.1.2.2 && spotBit sp t))) (fun u => ?_)
  exact ⟨fun h t ht => (key t).2 (h t ht), fun h t ht => (key t).1 (h t ht)⟩

lemma reachL_isRegular (M : Pebble A B Q k) (ell : ℕ) (nid : Fin k) (q₁ q₂ : Q)
    (sp₁ sp₂ : Spot) : (reachL M ell nid q₁ q₂ sp₁ sp₂).IsRegular :=
  isRegular_comapWin _ (PebEnc.reachLang_isRegular M ell)

lemma stepL_isRegular (M : Pebble A B Q k) (nid : Fin k) (q₁ q₂ : Q) (sp₁ sp₂ : Spot) :
    (stepL M nid q₁ q₂ sp₁ sp₂).IsRegular :=
  isRegular_comapWin _ (PebEnc.reachLang_isRegular (Pebble.stepMach M) 0)

/-! ## The validity of a spot, and the direction of a column -/

/-- The spot of the column that a direction leads to from the marked column. -/
def spotOfDir : CG.Dir → Spot
  | none => Spot.mark
  | some true => Spot.markR
  | some false => Spot.markL

/-- The column that a direction leads to from the column `x`. -/
def colOf (x : ℕ) : CG.Dir → ℕ
  | none => x
  | some true => x + 1
  | some false => x - 1

@[simp] lemma spotPos_spotOfDir (d : CG.Dir) (x r : ℕ) :
    spotPos (spotOfDir d) x r = some (colOf x d) := by
  cases d with
  | none => rfl
  | some b => cases b <;> rfl

/-- The marked string representations in which the spot names a genuine gap. -/
def okL : Spot → Language (MLetter A Q k)
  | Spot.markL => {u | u ∉ zeroL}
  | Spot.markR => {u | u ∉ lettL none}
  | _ => Set.univ

lemma okL_isRegular (sp : Spot) : (okL (A := A) (Q := Q) (k := k) sp).IsRegular := by
  cases sp with
  | markL => exact isRegular_not zeroL_isRegular
  | markR => exact isRegular_not (lettL_isRegular none)
  | nop => exact isRegular_univ
  | zero => exact isRegular_univ
  | mark => exact isRegular_univ
  | extra => exact isRegular_univ

/-! ## Children, and the successor of a child -/

/-- A single step leads from the configuration to the vertex `(q', 0)`. -/
noncomputable def firstL (M : Pebble A B Q k) (nid : Fin k) (q₀ q' : Q) :
    Language (MLetter A Q k) :=
  stepL M nid q₀ q' Spot.nop Spot.zero

/-- The vertex in the column named by the spot, with the state `q`, is a child. -/
noncomputable def childL (M : Pebble A B Q k) (nid : Fin k) (q : Q) (sp : Spot) :
    Language (MLetter A Q k) :=
  {u | ∃ p : Q × Q, u ∈ stateL p.1 ∧ u ∈ firstL M nid p.1 p.2 ∧
    u ∈ reachL M ((nid : ℕ) + 1) nid p.2 q Spot.zero sp}

/-- A child lies strictly between the two given vertices, in the column of the second mark. -/
noncomputable def midL (M : Pebble A B Q k) (nid : Fin k) (qa : Q) (da : CG.Dir) (qb : Q)
    (db : CG.Dir) : Language (MLetter A Q k) :=
  {u | ∃ q₃ : Q, u ∈ reachL M ((nid : ℕ) + 1) nid qa q₃ (spotOfDir da) Spot.extra ∧
    u ∈ reachL M ((nid : ℕ) + 1) nid q₃ qb Spot.extra (spotOfDir db) ∧
    (q₃ = qa → u ∈ neqSpotL (spotOfDir da)) ∧
    (q₃ = qb → u ∈ neqSpotL (spotOfDir db))}

/-- The letter map that forgets the second mark. -/
def dropExtra (c : MLetter A Q k) : CG.ConfLetter A Q k × Bool := (c.1, c.2.1)

/-- **Quantifying the second mark away**: the marked strings that become a member of `L` for some
placement of the second mark. -/
def existsExtraL (L : Language (MLetter A Q k)) : Language (MLetter A Q k) :=
  {u | ∃ v : List (MLetter A Q k), v ∈ L ∧ MarksOnce (fun c => c.2.2) v ∧
        v.map dropExtra = u.map dropExtra}

omit [Finite A] [Finite Q] in
lemma existsExtraL_isRegular {L : Language (MLetter A Q k)} (hL : L.IsRegular) :
    (existsExtraL L).IsRegular := by
  have h1 : Language.IsRegular {v : List (MLetter A Q k) | v ∈ L ∧ MarksOnce (fun c => c.2.2) v} :=
    isRegular_and hL (isRegular_marksOnce _)
  have h2 := isRegular_image dropExtra h1
  refine isRegular_of_eq (isRegular_comap dropExtra h2) (fun u => ?_)
  constructor
  · rintro ⟨v, hv, hm, he⟩
    exact ⟨v, ⟨hv, hm⟩, he⟩
  · rintro ⟨v, ⟨hv, hm⟩, he⟩
    exact ⟨v, hv, hm, he⟩

/-- **The successor of a child**: the vertex in the marked column with the state `qa` is a child,
and its successor is the vertex with the state `qb` in the column that `db` leads to. -/
noncomputable def edgeL (M : Pebble A B Q k) (nid : Fin k) (qa : Q) (da : CG.Dir) (qb : Q)
    (db : CG.Dir) : Language (MLetter A Q k) :=
  if qa = qb ∧ da = db then emptyL else
    {u | u ∈ okL (spotOfDir da) ∧ u ∈ okL (spotOfDir db) ∧
      u ∈ childL M nid qa (spotOfDir da) ∧
      u ∈ reachL M ((nid : ℕ) + 1) nid qa qb (spotOfDir da) (spotOfDir db) ∧
      u ∉ existsExtraL (midL M nid qa da qb db)}

lemma firstL_isRegular (M : Pebble A B Q k) (nid : Fin k) (q₀ q' : Q) :
    (firstL M nid q₀ q').IsRegular := stepL_isRegular M nid q₀ q' Spot.nop Spot.zero

lemma childL_isRegular (M : Pebble A B Q k) (nid : Fin k) (q : Q) (sp : Spot) :
    (childL M nid q sp).IsRegular :=
  isRegular_exists_finite _ (fun p : Q × Q =>
    isRegular_and (stateL_isRegular p.1)
      (isRegular_and (firstL_isRegular M nid p.1 p.2)
        (reachL_isRegular M ((nid : ℕ) + 1) nid p.2 q Spot.zero sp)))

lemma midL_isRegular (M : Pebble A B Q k) (nid : Fin k) (qa : Q) (da : CG.Dir) (qb : Q)
    (db : CG.Dir) : (midL M nid qa da qb db).IsRegular := by
  refine isRegular_exists_finite (fun q₃ : Q =>
    {u : List (MLetter A Q k) |
      u ∈ reachL M ((nid : ℕ) + 1) nid qa q₃ (spotOfDir da) Spot.extra ∧
      u ∈ reachL M ((nid : ℕ) + 1) nid q₃ qb Spot.extra (spotOfDir db) ∧
      (q₃ = qa → u ∈ neqSpotL (spotOfDir da)) ∧
      (q₃ = qb → u ∈ neqSpotL (spotOfDir db))}) (fun q₃ => ?_)
  refine isRegular_and (reachL_isRegular _ _ _ _ _ _ _)
    (isRegular_and (reachL_isRegular _ _ _ _ _ _ _) (isRegular_and ?_ ?_))
  · by_cases h : q₃ = qa
    · refine isRegular_of_eq (neqSpotL_isRegular (spotOfDir da)) (fun u => ?_)
      exact ⟨fun hh => hh h, fun hh _ => hh⟩
    · refine isRegular_of_eq isRegular_univ (fun u => ?_)
      exact ⟨fun _ => Set.mem_univ _, fun _ hc => absurd hc h⟩
  · by_cases h : q₃ = qb
    · refine isRegular_of_eq (neqSpotL_isRegular (spotOfDir db)) (fun u => ?_)
      exact ⟨fun hh => hh h, fun hh _ => hh⟩
    · refine isRegular_of_eq isRegular_univ (fun u => ?_)
      exact ⟨fun _ => Set.mem_univ _, fun _ hc => absurd hc h⟩

lemma edgeL_isRegular (M : Pebble A B Q k) (nid : Fin k) (qa : Q) (da : CG.Dir) (qb : Q)
    (db : CG.Dir) : (edgeL M nid qa da qb db).IsRegular := by
  rw [edgeL]
  split
  · exact emptyL_isRegular
  · exact isRegular_and (okL_isRegular _)
      (isRegular_and (okL_isRegular _)
        (isRegular_and (childL_isRegular _ _ _ _)
          (isRegular_and (reachL_isRegular _ _ _ _ _ _ _)
            (isRegular_not (existsExtraL_isRegular (midL_isRegular _ _ _ _ _ _))))))

end CGL

end Lax194892Proofs.Transducers
